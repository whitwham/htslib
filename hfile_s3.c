/*  hfile_s3.c -- Amazon S3 backend for low-level file streams.

    Copyright (C) 2015-2017 Genome Research Ltd.

    Author: John Marshall <jm18@sanger.ac.uk>

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
DEALINGS IN THE SOFTWARE.  */

#include <config.h>

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include <curl/curl.h>
#include <errno.h>

#include "hfile_internal.h"
#ifdef ENABLE_PLUGINS
#include "version.h"
#endif
#include "htslib/hts.h"  // for hts_version() and hts_verbose
#include "htslib/kstring.h"

typedef struct {
    kstring_t id;
    kstring_t token;
    kstring_t secret;
    kstring_t region;
    char *bucket;
    char *canonical_uri;
    kstring_t auth_hdr;
    time_t auth_time;
    char date[40];
    char date_long[17];
    char date_short[9];
    kstring_t date_html;
    char mode;
    char *headers[3];
} s3_auth_data;

#define AUTH_LIFETIME 60

#if defined HAVE_COMMONCRYPTO

#include <CommonCrypto/CommonHMAC.h>

#define DIGEST_BUFSIZ CC_SHA1_DIGEST_LENGTH

static size_t
s3_sign(unsigned char *digest, kstring_t *key, kstring_t *message)
{
    CCHmac(kCCHmacAlgSHA1, key->s, key->l, message->s, message->l, digest);
    return CC_SHA1_DIGEST_LENGTH;
}

#elif defined HAVE_HMAC

#include <openssl/hmac.h>
#include <openssl/sha.h>

#define DIGEST_BUFSIZ EVP_MAX_MD_SIZE
#define SHA256_DIGEST_BUFSIZE SHA256_DIGEST_LENGTH
#define HASH_LENGTH_SHA256 (SHA256_DIGEST_BUFSIZE * 2) + 1

static size_t
s3_sign(unsigned char *digest, kstring_t *key, kstring_t *message)
{
    unsigned int len;
    HMAC(EVP_sha1(), key->s, key->l,
         (unsigned char *) message->s, message->l, digest, &len);
    return len;
}


static void s3_sha256(const unsigned char *in, size_t length, unsigned char *out) {
    SHA256(in, length, out);
}


unsigned char *s3_sign_sha256(const void *key, int key_len, const unsigned char *d, int n, unsigned char *md, unsigned int *md_len) {
    return HMAC(EVP_sha256(), key, key_len, d, n, md, md_len);
}

#else
#error No HMAC() routine found by configure
#endif

static void
urldecode_kput(const char *s, int len, kstring_t *str)
{
    char buf[3];
    int i = 0;

    while (i < len)
        if (s[i] == '%' && i+2 < len) {
            buf[0] = s[i+1], buf[1] = s[i+2], buf[2] = '\0';
            kputc(strtol(buf, NULL, 16), str);
            i += 3;
        }
        else kputc(s[i++], str);
}

static void base64_kput(const unsigned char *data, size_t len, kstring_t *str)
{
    static const char base64[] =
        "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

    size_t i = 0;
    unsigned x = 0;
    int bits = 0, pad = 0;

    while (bits || i < len) {
        if (bits < 6) {
            x <<= 8, bits += 8;
            if (i < len) x |= data[i++];
            else pad++;
        }

        bits -= 6;
        kputc(base64[(x >> bits) & 63], str);
    }

    str->l -= pad;
    kputsn("==", pad, str);
}

static int is_dns_compliant(const char *s0, const char *slim)
{
    int has_nondigit = 0, len = 0;
    const char *s;

    for (s = s0; s < slim; len++, s++)
        if (islower_c(*s))
            has_nondigit = 1;
        else if (*s == '-') {
            has_nondigit = 1;
            if (s == s0 || s+1 == slim) return 0;
        }
        else if (isdigit_c(*s))
            ;
        else if (*s == '.') {
            if (s == s0 || ! isalnum_c(s[-1])) return 0;
            if (s+1 == slim || ! isalnum_c(s[1])) return 0;
        }
        else return 0;

    return has_nondigit && len >= 3 && len <= 63;
}

static FILE *expand_tilde_open(const char *fname, const char *mode)
{
    FILE *fp;

    if (strncmp(fname, "~/", 2) == 0) {
        kstring_t full_fname = { 0, 0, NULL };
        const char *home = getenv("HOME");
        if (! home) return NULL;

        kputs(home, &full_fname);
        kputs(&fname[1], &full_fname);

        fp = fopen(full_fname.s, mode);
        free(full_fname.s);
    }
    else
        fp = fopen(fname, mode);

    return fp;
}

static void parse_ini(const char *fname, const char *section, ...)
{
    kstring_t line = { 0, 0, NULL };
    int active = 1;  // Start active, so global properties are accepted
    char *s;

    FILE *fp = expand_tilde_open(fname, "r");
    if (fp == NULL) return;

    while (line.l = 0, kgetline(&line, (kgets_func *) fgets, fp) >= 0)
        if (line.s[0] == '[' && (s = strchr(line.s, ']')) != NULL) {
            *s = '\0';
            active = (strcmp(&line.s[1], section) == 0);
        }
        else if (active && (s = strpbrk(line.s, ":=")) != NULL) {
            const char *key = line.s, *value = &s[1], *akey;
            va_list args;

            while (isspace_c(*key)) key++;
            while (s > key && isspace_c(s[-1])) s--;
            *s = '\0';

            while (isspace_c(*value)) value++;
            while (line.l > 0 && isspace_c(line.s[line.l-1]))
                line.s[--line.l] = '\0';

            va_start(args, section);
            while ((akey = va_arg(args, const char *)) != NULL) {
                kstring_t *avar = va_arg(args, kstring_t *);
                if (strcmp(key, akey) == 0) { kputs(value, avar); break; }
            }
            va_end(args);
        }

    fclose(fp);
    free(line.s);
}

static void parse_simple(const char *fname, kstring_t *id, kstring_t *secret)
{
    kstring_t text = { 0, 0, NULL };
    char *s;
    size_t len;

    FILE *fp = expand_tilde_open(fname, "r");
    if (fp == NULL) return;

    while (kgetline(&text, (kgets_func *) fgets, fp) >= 0)
        kputc(' ', &text);
    fclose(fp);

    s = text.s;
    while (isspace_c(*s)) s++;
    kputsn(s, len = strcspn(s, " \t"), id);

    s += len;
    while (isspace_c(*s)) s++;
    kputsn(s, strcspn(s, " \t"), secret);

    free(text.s);
}

static int copy_auth_headers(s3_auth_data *ad, char ***hdrs) {
    char **hdr = &ad->headers[0];
    *hdrs = hdr;
    *hdr = strdup(ad->date);
    if (!*hdr) return -1;
    hdr++;
    if (ad->auth_hdr.l) {
        *hdr = strdup(ad->auth_hdr.s);
        if (!*hdr) { free(ad->headers[0]); return -1; }
        hdr++;
    }
    *hdr = NULL;
    return 0;
}

static void free_auth_data(s3_auth_data *ad) {
    free(ad->id.s);
    free(ad->token.s);
    free(ad->secret.s);
    free(ad->bucket);
    free(ad->auth_hdr.s);
    free(ad);
}

static int auth_header_callback(void *ctx, char ***hdrs) {
    s3_auth_data *ad = (s3_auth_data *) ctx;

    time_t now = time(NULL);
#ifdef HAVE_GMTIME_R
    struct tm tm_buffer;
    struct tm *tm = gmtime_r(&now, &tm_buffer);
#else
    struct tm *tm = gmtime(&now);
#endif
    kstring_t message = { 0, 0, NULL };
    unsigned char digest[DIGEST_BUFSIZ];
    size_t digest_len;

    if (!hdrs) { // Closing connection
        free_auth_data(ad);
        return 0;
    }

    if (now - ad->auth_time < AUTH_LIFETIME) {
        // Last auth string should still be valid
        *hdrs = NULL;
        return 0;
    }

    strftime(ad->date, sizeof(ad->date), "Date: %a, %d %b %Y %H:%M:%S GMT", tm);
    if (!ad->id.l || !ad->secret.l) {
        ad->auth_time = now;
        return copy_auth_headers(ad, hdrs);
    }

    if (ksprintf(&message, "%s\n\n\n%s\n%s%s%s/%s",
                 ad->mode == 'r' ? "GET" : "PUT", ad->date + 6,
                 ad->token.l ? "x-amz-security-token:" : "",
                 ad->token.l ? ad->token.s : "",
                 ad->token.l ? "\n" : "",
                 ad->bucket) < 0) {
        return -1;
    }

    digest_len = s3_sign(digest, &ad->secret, &message);
    ad->auth_hdr.l = 0;
    if (ksprintf(&ad->auth_hdr, "Authorization: AWS %s:", ad->id.s) < 0)
        goto fail;
    base64_kput(digest, digest_len, &ad->auth_hdr);

    free(message.s);
    ad->auth_time = now;
    return copy_auth_headers(ad, hdrs);

 fail:
    free(message.s);
    return -1;
}

static hFILE * s3_rewrite(const char *s3url, const char *mode, va_list *argsp)
{
    const char *bucket, *path;
    char *header_list[4], **header = header_list;

    kstring_t url = { 0, 0, NULL };
    kstring_t profile = { 0, 0, NULL };
    kstring_t host_base = { 0, 0, NULL };
    kstring_t token_hdr = { 0, 0, NULL };

    s3_auth_data *ad = calloc(1, sizeof(*ad));

    if (!ad)
        return NULL;
    ad->mode = strchr(mode, 'r') ? 'r' : 'w';

    // Our S3 URL format is s3[+SCHEME]://[ID[:SECRET[:TOKEN]]@]BUCKET/PATH

    if (s3url[2] == '+') {
        bucket = strchr(s3url, ':') + 1;
        kputsn(&s3url[3], bucket - &s3url[3], &url);
    }
    else {
        kputs("https:", &url);
        bucket = &s3url[3];
    }
    while (*bucket == '/') kputc(*bucket++, &url);

    path = bucket + strcspn(bucket, "/?#@");
    if (*path == '@') {
        const char *colon = strpbrk(bucket, ":@");
        if (*colon != ':') {
            urldecode_kput(bucket, colon - bucket, &profile);
        }
        else {
            const char *colon2 = strpbrk(&colon[1], ":@");
            urldecode_kput(bucket, colon - bucket, &ad->id);
            urldecode_kput(&colon[1], colon2 - &colon[1], &ad->secret);
            if (*colon2 == ':')
                urldecode_kput(&colon2[1], path - &colon2[1], &ad->token);
        }

        bucket = &path[1];
        path = bucket + strcspn(bucket, "/?#");
    }
    else {
        // If the URL has no ID[:SECRET]@, consider environment variables.
        const char *v;
        if ((v = getenv("AWS_ACCESS_KEY_ID")) != NULL) kputs(v, &ad->id);
        if ((v = getenv("AWS_SECRET_ACCESS_KEY")) != NULL) kputs(v, &ad->secret);
        if ((v = getenv("AWS_SESSION_TOKEN")) != NULL) kputs(v, &ad->token);

        if ((v = getenv("AWS_DEFAULT_PROFILE")) != NULL) kputs(v, &profile);
        else if ((v = getenv("AWS_PROFILE")) != NULL) kputs(v, &profile);
        else kputs("default", &profile);
    }

    if (ad->id.l == 0) {
        const char *v = getenv("AWS_SHARED_CREDENTIALS_FILE");
        parse_ini(v? v : "~/.aws/credentials", profile.s,
                  "aws_access_key_id", &ad->id,
                  "aws_secret_access_key", &ad->secret,
                  "aws_session_token", &ad->token, NULL);
    }
    if (ad->id.l == 0)
        parse_ini("~/.s3cfg", profile.s, "access_key", &ad->id,
                  "secret_key", &ad->secret, "access_token", &ad->token,
                  "host_base", &host_base, NULL);
    if (ad->id.l == 0)
        parse_simple("~/.awssecret", &ad->id, &ad->secret);

    if (host_base.l == 0)
        kputs("s3.amazonaws.com", &host_base);
    // Use virtual hosted-style access if possible, otherwise path-style.
    if (is_dns_compliant(bucket, path)) {
        kputsn(bucket, path - bucket, &url);
        kputc('.', &url);
        kputs(host_base.s, &url);
    }
    else {
        kputs(host_base.s, &url);
        kputc('/', &url);
        kputsn(bucket, path - bucket, &url);
    }
    kputs(path, &url);

    if (ad->token.l > 0) {
        kputs("X-Amz-Security-Token: ", &token_hdr);
        kputs(ad->token.s, &token_hdr);
        *header++ = token_hdr.s;
    }

    ad->bucket = strdup(bucket);
    if (!ad->bucket)
        goto fail;

    *header = NULL;
    hFILE *fp = hopen(url.s, mode, "va_list", argsp, "httphdr:v", header_list,
                      "httphdr_callback", auth_header_callback,
                      "httphdr_callback_data", ad, NULL);
    if (!fp) goto fail;

    free(url.s);
    free(profile.s);
    free(host_base.s);
    free(token_hdr.s);
    return fp;

 fail:
    free(url.s);
    free(profile.s);
    free(host_base.s);
    free(token_hdr.s);
    free_auth_data(ad);
    return NULL;
}

/***************************************************************

AWS S3 sig version 4 writing code

****************************************************************/

#define MINIMUM_S3_WRITE_SIZE 5242880
#define HASH_LENGTH (SHA256_DIGEST_LENGTH * 2) + 1
#define S3_MOVED_PERMANENTLY 301

typedef struct {
    hFILE base;
    CURL *curl;
    CURLcode ret;
    s3_auth_data *ad;
    kstring_t buffer;
    kstring_t url;
    kstring_t host_base;
    kstring_t token_hdr;
    char *http_request;
    kstring_t canonical_query_string;
    kstring_t upload_id;
    kstring_t completion_message;
    int part_no;
    size_t index;
} hFILE_s3_write;


static void hash_string(char *in, size_t length, char *out) {
    unsigned char hashed[SHA256_DIGEST_BUFSIZE];
    int i, j;

    s3_sha256((const unsigned char *)in, length, hashed);
    
    for (i = 0, j = 0; i < SHA256_DIGEST_BUFSIZE; i++, j+= 2) {
        sprintf(out + j, "%02x", hashed[i]);
    }
}

static void kinit(kstring_t *s) {
    s->l = 0;
    s->m = 0;
    s->s = NULL;
}


static void kfree(kstring_t *s) {
    free(s->s);
    kinit(s);
}


static int make_signature(hFILE_s3_write *fp, kstring_t *string_to_sign, char *signature_string) {
    unsigned char date_key[SHA256_DIGEST_LENGTH];
    unsigned char date_region_key[SHA256_DIGEST_LENGTH];
    unsigned char date_region_service_key[SHA256_DIGEST_LENGTH];
    unsigned char signing_key[SHA256_DIGEST_LENGTH];
    unsigned char signature[SHA256_DIGEST_LENGTH];
    
    const unsigned char service[] = "s3";
    const unsigned char request[] = "aws4_request";
    
    kstring_t secret_access_key = {0, 0, NULL};
    unsigned int len;
    unsigned int i, j;
    
    ksprintf(&secret_access_key, "AWS4%s", fp->ad->secret.s);
    
    if (secret_access_key.l == 0) {
        return -1;
    }

    s3_sign_sha256(secret_access_key.s, secret_access_key.l, (const unsigned char *)fp->ad->date_short, strlen(fp->ad->date_short), date_key, &len);
    s3_sign_sha256(date_key, len, (const unsigned char *)fp->ad->region.s, fp->ad->region.l, date_region_key, &len); 
    s3_sign_sha256(date_region_key, len, service, 2, date_region_service_key, &len); 
    s3_sign_sha256(date_region_service_key, len, request, 12, signing_key, &len); 
    s3_sign_sha256(signing_key, len, (const unsigned char *)string_to_sign->s, string_to_sign->l, signature, &len);
    
    for (i = 0, j = 0; i < len; i++, j+= 2) {
        sprintf(signature_string + j, "%02x", signature[i]);
    }
    
    kfree(&secret_access_key);
    
    return 0;
}


static int make_authorisation(hFILE_s3_write *fp, char *content, kstring_t *auth) {
    kstring_t signed_headers = {0, 0, NULL};
    kstring_t canonical_headers = {0, 0, NULL};
    kstring_t canonical_request = {0, 0, NULL};
    kstring_t scope = {0, 0, NULL};
    kstring_t string_to_sign = {0, 0, NULL};
    char cr_hash[HASH_LENGTH_SHA256];
    char signature_string[HASH_LENGTH_SHA256];
    
    kputs("host;x-amz-content-sha256;x-amz-date", &signed_headers);
    
    if (signed_headers.l == 0) {
        return -1;
    }
    
    ksprintf(&canonical_headers, "host:%s\nx-amz-content-sha256:%s\nx-amz-date:%s\n",
        fp->host_base.s, content, fp->ad->date_long);
        
    if (canonical_headers.l == 0) {
        return -1;
    }
    
    ksprintf(&canonical_request, "%s\n/%s\n%s\n%s\n%s\n%s",
        fp->http_request, fp->ad->canonical_uri, fp->canonical_query_string.s,
        canonical_headers.s, signed_headers.s, content);
        
    if (canonical_request.l == 0) {
        return -1;
    }

    hash_string(canonical_request.s, canonical_request.l, cr_hash);
    
    ksprintf(&scope, "%s/%s/s3/aws4_request", fp->ad->date_short, fp->ad->region.s);
    
    if (scope.l == 0) {
        return -1;
    }
    
    ksprintf(&string_to_sign, "AWS4-HMAC-SHA256\n%s\n%s\n%s", fp->ad->date_long, scope.s, cr_hash);
    
    if (string_to_sign.l == 0) {
        return -1;
    }
    
    if (make_signature(fp, &string_to_sign, signature_string)) {
        return -1;
    }
    
    ksprintf(auth, "Authorization: AWS4-HMAC-SHA256 Credential=%s/%s/%s/s3/aws4_request,SignedHeaders=%s,Signature=%s",
                fp->ad->id.s, fp->ad->date_short, fp->ad->region.s, signed_headers.s, signature_string);
                
    if (auth->l == 0) {
        return -1;
    }
    
    kfree(&signed_headers);
    kfree(&canonical_headers);
    kfree(&canonical_request);
    kfree(&scope);
    kfree(&string_to_sign);
    
    return 0;
}


struct curl_slist *set_html_headers(hFILE_s3_write *fp, kstring_t *auth, kstring_t *date, kstring_t *content) {
    struct curl_slist *headers = NULL;

    headers = curl_slist_append(headers, "Content-Type:"); // get rid of this
    headers = curl_slist_append(headers, "Expect:");       // and this
    headers = curl_slist_append(headers, auth->s);
    headers = curl_slist_append(headers, date->s);
    headers = curl_slist_append(headers, content->s);

    curl_easy_setopt(fp->curl, CURLOPT_HTTPHEADER, headers);
    
    return headers;
}


size_t response_callback(void *contents, size_t size, size_t nmemb, void *userp) {
    size_t realsize = size * nmemb;
    kstring_t *resp = (kstring_t *)userp;

    if (kputsn((const char *)contents, realsize, resp) == EOF) {
        return 0;
    }    
    
    return realsize;
}


/*
    The partially uploaded file will hang around unless the delete command is sent.
*/
static int abort_upload(hFILE_s3_write *fp) {
    char content_hash[HASH_LENGTH_SHA256];
    kstring_t authorisation = {0, 0, NULL};
    kstring_t url = {0, 0, NULL};
    kstring_t content = {0, 0, NULL};
    int ret = 0;
    struct curl_slist *headers;

    fp->http_request = "DELETE";

    if (ksprintf(&fp->canonical_query_string, "uploadId=%s", fp->upload_id.s) < 0) {
        return -1;
    }    

    hash_string("", 0, content_hash); // empty hash
    
    if (make_authorisation(fp, content_hash, &authorisation)) {
        return -1;
    }
    
    if (ksprintf(&url, "%s?%s", fp->url.s, fp->canonical_query_string.s) < 0) {
        return -1;
    }
    
    ksprintf(&content, "x-amz-content-sha256: %s", content_hash);

    curl_easy_reset(fp->curl);
    curl_easy_setopt(fp->curl, CURLOPT_CUSTOMREQUEST, fp->http_request);
    curl_easy_setopt(fp->curl, CURLOPT_USERAGENT, "andy_write_test");
    curl_easy_setopt(fp->curl, CURLOPT_URL, url.s);
    
    curl_easy_setopt(fp->curl, CURLOPT_VERBOSE, 1L);

    headers = set_html_headers(fp, &authorisation, &fp->ad->date_html, &content);
    fp->ret = curl_easy_perform(fp->curl);
    
    if (fp->ret != CURLE_OK) {
        ret = -1;
    }
       
    kfree(&authorisation);
    kfree(&content);
    kfree(&fp->canonical_query_string);    
    curl_slist_free_all(headers);
    
    return ret;
}
    

static int initialise_upload(hFILE_s3_write *fp, kstring_t *head, kstring_t *resp) {
    char content_hash[HASH_LENGTH_SHA256];
    kstring_t authorisation = {0, 0, NULL};
    kstring_t url = {0, 0, NULL};
    kstring_t content = {0, 0, NULL};
    int ret = 0;
    struct curl_slist *headers;
    
    fp->http_request = "POST";
    kputs("uploads=", &fp->canonical_query_string);
    
    if (fp->canonical_query_string.l == 0) {
        return -1;
    }
    
    hash_string("", 0, content_hash); // empty hash
    
    if (make_authorisation(fp, content_hash, &authorisation)) {
        return -1;
    }
    
    ksprintf(&url, "%s?uploads", fp->url.s);
    
    if (url.l == 0) {
        return -1;
    }
    
    ksprintf(&content, "x-amz-content-sha256: %s", content_hash);
    
    if (content.l == 0) {
        return -1;
    }
    
    curl_easy_setopt(fp->curl, CURLOPT_URL, url.s);
    curl_easy_setopt(fp->curl, CURLOPT_POST, 1L);
    curl_easy_setopt(fp->curl, CURLOPT_POSTFIELDS, "");  // send no data
    curl_easy_setopt(fp->curl, CURLOPT_WRITEFUNCTION, response_callback);
    curl_easy_setopt(fp->curl, CURLOPT_WRITEDATA, (void *)resp);
    curl_easy_setopt(fp->curl, CURLOPT_HEADERFUNCTION, response_callback);
    curl_easy_setopt(fp->curl, CURLOPT_HEADERDATA, (void *)head);
    curl_easy_setopt(fp->curl, CURLOPT_USERAGENT, "andy_write_test");
    
    curl_easy_setopt(fp->curl, CURLOPT_VERBOSE, 1L);
    
    headers = set_html_headers(fp, &authorisation, &fp->ad->date_html, &content);
    fp->ret = curl_easy_perform(fp->curl);
    
    if (fp->ret != CURLE_OK) {
        ret = -1;
    }
       
    kfree(&authorisation);
    kfree(&content);
    kfree(&fp->canonical_query_string);    
    curl_slist_free_all(headers);
    
    return ret;    
}


static int redirect_endpoint(hFILE_s3_write *fp, kstring_t *head, char *bucket) {
    int ret = 0;
    
    if (strstr(fp->host_base.s, "amazonaws.com")) {
        char *new_region;
        char *end;
        
        if ((new_region = strstr(head->s, "x-amz-bucket-region: ")) == NULL) {
            return -1;
        }

        new_region += strlen("x-amz-bucket-region: ");
        end = new_region;

        while (isalnum(*end) || ispunct(*end)) end++;

        *end = 0;

        fp->ad->region.l = 0;
        kputs(new_region, &fp->ad->region);
        
        fp->host_base.l = 0;
        ksprintf(&fp->host_base, "s3.%s.amazonaws.com", new_region);
        
        if (fp->ad->region.l == 0) {
            ret = -1;
        }
        
        fp->url.l = 0;
        kputs(fp->host_base.s, &fp->url);
        kputc('/', &fp->url);
        kputsn(bucket, strlen(bucket), &fp->url);
        
    } else {
        ret = -1;
    }
    
    return ret;
}


static int get_entry(char *in, char *start_tag, char *end_tag, kstring_t *out) {
    char *start;
    char *end;
    
    start = strstr(in, start_tag);
    
    if (start) {
        start += strlen(start_tag);
        end = strstr(start, end_tag);
    }
    
    if (!start || !end) return EOF;
    
    return kputsn(start, end - start, out);
}


static int get_upload_id(hFILE_s3_write *fp, kstring_t *resp) {
    int ret = 0;

    kinit(&fp->upload_id);

    if (get_entry(resp->s, "<UploadId>", "</UploadId>", &fp->upload_id) == EOF) {
        ret = -1;
    }
    
    return ret;
}


static size_t upload_callback(void *ptr, size_t size, size_t nmemb, void *stream) {
    size_t realsize = size * nmemb;
    hFILE_s3_write *fp = (hFILE_s3_write *)stream;
    size_t read_length;
    
    if (realsize > (fp->buffer.l - fp->index)) {
        read_length = fp->buffer.l - fp->index;
    } else {
        read_length = realsize;
    }
    
    memcpy(ptr, fp->buffer.s + fp->index, read_length);
    fp->index += read_length;
    
    return read_length;
}


static int upload_part(hFILE_s3_write *fp, kstring_t *resp) {
    char content_hash[HASH_LENGTH_SHA256];
    kstring_t authorisation = {0, 0, NULL};
    kstring_t url = {0, 0, NULL};
    kstring_t content = {0, 0, NULL};
    int ret = 0;
    struct curl_slist *headers;
    
    fp->http_request = "PUT";
    
    if (ksprintf(&fp->canonical_query_string, "partNumber=%d&uploadId=%s", fp->part_no, fp->upload_id.s) < 0) {
        return -1;
    }
    
    hash_string(fp->buffer.s, fp->buffer.l, content_hash);
    
    if (make_authorisation(fp, content_hash, &authorisation)) {
        return -1;
    }
    
    if (ksprintf(&url, "%s?%s", fp->url.s, fp->canonical_query_string.s) < 0) {
        return -1;
    }
    
    fp->index = 0;
    ksprintf(&content, "x-amz-content-sha256: %s", content_hash);
    
    curl_easy_reset(fp->curl);

    curl_easy_setopt(fp->curl, CURLOPT_UPLOAD, 1L);
    curl_easy_setopt(fp->curl, CURLOPT_READFUNCTION, upload_callback);
    curl_easy_setopt(fp->curl, CURLOPT_READDATA, fp);
    curl_easy_setopt(fp->curl, CURLOPT_INFILESIZE_LARGE, (curl_off_t)fp->buffer.l);       
    curl_easy_setopt(fp->curl, CURLOPT_HEADERFUNCTION, response_callback);
    curl_easy_setopt(fp->curl, CURLOPT_HEADERDATA, (void *)resp);
    curl_easy_setopt(fp->curl, CURLOPT_URL, url.s);
    curl_easy_setopt(fp->curl, CURLOPT_USERAGENT, "andy_write_test");
    
    curl_easy_setopt(fp->curl, CURLOPT_VERBOSE, 1L);    
    
    headers = set_html_headers(fp, &authorisation, &fp->ad->date_html, &content);
    fp->ret = curl_easy_perform(fp->curl);
    
    if (fp->ret != CURLE_OK) {
        ret = -1;
    }
       
    kfree(&authorisation);
    kfree(&content);
    kfree(&fp->canonical_query_string);    
    curl_slist_free_all(headers);
    
    return ret;    
}
    

static ssize_t s3_write(hFILE *fpv, const void *bufferv, size_t nbytes) {
    hFILE_s3_write *fp = (hFILE_s3_write *)fpv;
    const char *buffer  = (const char *)bufferv;
    
    if (kputsn(buffer, nbytes, &fp->buffer) == EOF) {
        return -1;
    }
    
    if (fp->buffer.l > MINIMUM_S3_WRITE_SIZE) {
        // time to write out our data
        kstring_t response = {0, 0, NULL};
        int ret;
        
        ret = upload_part(fp, &response);
        
        if (!ret) {
            long response_code;
            kstring_t etag = {0, 0, NULL};
            
            curl_easy_getinfo(fp->curl, CURLINFO_RESPONSE_CODE, &response_code);

            if (response_code > 200) {
                ret = -1;
            } else {
                if (get_entry(response.s, "ETag: \"", "\"", &etag) == EOF) {
                    ret = -1;
                } else {
                    ksprintf(&fp->completion_message, "\t<Part>\n\t\t<PartNumber>%d</PartNumber>\n\t\t<ETag>%s</ETag>\n\t</Part>\n",
                        fp->part_no, etag.s);
                        
                    kfree(&etag);
                }
            }
        }
        
        kfree(&response);
        
        if (ret) {
            abort_upload(fp);
            return -1;
        }
        
        fp->part_no++;
        fp->buffer.l = 0;
    }

    return nbytes;
}


static int complete_upload(hFILE_s3_write *fp, kstring_t *resp) {
    char content_hash[HASH_LENGTH_SHA256];
    kstring_t authorisation = {0, 0, NULL};
    kstring_t url = {0, 0, NULL};
    kstring_t content = {0, 0, NULL};
    int ret = 0;
    struct curl_slist *headers;

    fp->http_request = "POST";
    
    if (ksprintf(&fp->canonical_query_string, "uploadId=%s", fp->upload_id.s) < 0) {
        return -1;
    }
    
    // finish off the completion reply
    kputs("</CompleteMultipartUpload>\n", &fp->completion_message);
    
    hash_string(fp->completion_message.s, fp->completion_message.l, content_hash);
    
    if (make_authorisation(fp, content_hash, &authorisation)) {
        return -1;
    }
    
    if (ksprintf(&url, "%s?%s", fp->url.s, fp->canonical_query_string.s) < 0) {
        return -1;
    }
    
    ksprintf(&content, "x-amz-content-sha256: %s", content_hash);
    
    curl_easy_reset(fp->curl);
    curl_easy_setopt(fp->curl, CURLOPT_POST, 1L);
    curl_easy_setopt(fp->curl, CURLOPT_POSTFIELDS, fp->completion_message.s);
    curl_easy_setopt(fp->curl, CURLOPT_POSTFIELDSIZE, fp->completion_message.l);
    curl_easy_setopt(fp->curl, CURLOPT_WRITEFUNCTION, response_callback);
    curl_easy_setopt(fp->curl, CURLOPT_WRITEDATA, (void *)resp);
    curl_easy_setopt(fp->curl, CURLOPT_URL, url.s);
    curl_easy_setopt(fp->curl, CURLOPT_USERAGENT, "andy_write_test");
    
    curl_easy_setopt(fp->curl, CURLOPT_VERBOSE, 1L);    
    
    headers = set_html_headers(fp, &authorisation, &fp->ad->date_html, &content);
    fp->ret = curl_easy_perform(fp->curl);
    
    if (fp->ret != CURLE_OK) {
        ret = -1;
    }
       
    kfree(&authorisation);
    kfree(&content);
    kfree(&fp->canonical_query_string);    
    curl_slist_free_all(headers);
    
    return ret;
}


static int s3_close(hFILE *fpv) {
    hFILE_s3_write *fp = (hFILE_s3_write *)fpv;
    kstring_t response = {0, 0, NULL};
    int ret = 0;
    
    if (fp->buffer.l) {
        // write the last part
        
        ret = upload_part(fp, &response);
        
        if (!ret) {
            long response_code;
            kstring_t etag = {0, 0, NULL};
            
            curl_easy_getinfo(fp->curl, CURLINFO_RESPONSE_CODE, &response_code);

            if (response_code > 200) {
                ret = -1;
            } else {
                if (get_entry(response.s, "ETag: \"", "\"", &etag) == EOF) {
                    ret = -1;
                } else {
                    ksprintf(&fp->completion_message, "\t<Part>\n\t\t<PartNumber>%d</PartNumber>\n\t\t<ETag>%s</ETag>\n\t</Part>\n",
                        fp->part_no, etag.s);
                        
                    kfree(&etag);
                }
            }
        }
        
        kfree(&response);
        
        if (ret) {
            abort_upload(fp);
            return -1;
        }
        
        fp->part_no++;
    }
    
    if (fp->part_no > 1) {
        ret = complete_upload(fp, &response);
        
        if (!ret) {
            if (strstr(response.s, "CompleteMultipartUploadResult") == NULL) {
                ret = -1;
            }
        }
    } else {
        ret = -1;
    }
    
    if (ret) {
        abort_upload(fp);
    }

    curl_easy_cleanup(fp->curl);

    return ret;
}


static const struct hFILE_backend s3_write_backend = {
    NULL, s3_write, NULL, NULL, s3_close
};
 

static hFILE *s3_open_for_writing(char *s3url, va_list *argsp) {
    hFILE_s3_write *fp;
    CURLcode err;
    kstring_t profile  = {0, 0, NULL};
    kstring_t response = {0, 0, NULL};
    kstring_t header   = {0, 0, NULL};
    char *bucket, *path;
    struct tm *base_time;
    int ret;

    fp = (hFILE_s3_write *)hfile_init(sizeof(hFILE_s3_write), "w", 0);
    
    if (fp == NULL) goto error; // FIXME need to sort out error handling properly
    
    kinit(&fp->buffer);
    kinit(&fp->url);
    kinit(&fp->host_base);
    kinit(&fp->token_hdr);
    kinit(&fp->canonical_query_string);
    
    err = curl_global_init(CURL_GLOBAL_ALL);  // FIXME possibly called twice (with hfile_libcurl)
    
    if (err != CURLE_OK) {
        goto error; // FIXME error handling
    }
    
    if ((fp->curl = curl_easy_init()) == NULL) {
        errno = ENOMEM;
        goto error;
    }
    
    if ((fp->ad = calloc(1, sizeof(s3_auth_data))) == NULL) {
        goto error;
    }
    
    fp->ad->mode = 'w';
    
    if (s3url[2] == '+') {
        bucket = strchr(s3url, ':') + 1;
        kputsn(&s3url[3], bucket - &s3url[3], &fp->url);
    }
    else {
        kputs("https:", &fp->url);
        bucket = &s3url[3];
    }    
    
    while (*bucket == '/') kputc(*bucket++, &fp->url);

    path = bucket + strcspn(bucket, "/?#@");
    
    if (*path == '@') {
        const char *colon = strpbrk(bucket, ":@");
        if (*colon != ':') {
            urldecode_kput(bucket, colon - bucket, &profile);
        }
        else {
            const char *colon2 = strpbrk(&colon[1], ":@");
            urldecode_kput(bucket, colon - bucket, &fp->ad->id);
            urldecode_kput(&colon[1], colon2 - &colon[1], &fp->ad->secret);
            if (*colon2 == ':')
                urldecode_kput(&colon2[1], path - &colon2[1], &fp->ad->token);
        }

        bucket = &path[1];
        path = bucket + strcspn(bucket, "/?#");
    }
    else {
        // If the URL has no ID[:SECRET]@, consider environment variables.
        const char *v;
        if ((v = getenv("AWS_ACCESS_KEY_ID")) != NULL) kputs(v, &fp->ad->id);
        if ((v = getenv("AWS_SECRET_ACCESS_KEY")) != NULL) kputs(v, &fp->ad->secret);
        if ((v = getenv("AWS_SESSION_TOKEN")) != NULL) kputs(v, &fp->ad->token);
        if ((v = getenv("AWS_DEFAULT_REGION")) != NULL) kputs(v, &fp->ad->region);

        if ((v = getenv("AWS_DEFAULT_PROFILE")) != NULL) kputs(v, &profile);
        else if ((v = getenv("AWS_PROFILE")) != NULL) kputs(v, &profile);
        else kputs("default", &profile);
    }
    
    if (fp->ad->id.l == 0) {
        const char *v = getenv("AWS_SHARED_CREDENTIALS_FILE");
        parse_ini(v? v : "~/.aws/credentials", profile.s,
                  "aws_access_key_id", &fp->ad->id,
                  "aws_secret_access_key", &fp->ad->secret,
                  "aws_session_token", &fp->ad->token,
                  "region", &fp->ad->region, NULL);
    }
    
    if (fp->ad->id.l == 0)
        parse_ini("~/.s3cfg", profile.s, "access_key", &fp->ad->id,
                  "secret_key", &fp->ad->secret, "access_token", &fp->ad->token,
                  "host_base", &fp->host_base,
                  "bucket_location", &fp->ad->region, NULL);
    if (fp->ad->id.l == 0)
        parse_simple("~/.awssecret", &fp->ad->id, &fp->ad->secret);

    if (fp->host_base.l == 0)
        kputs("s3.amazonaws.com", &fp->host_base);
        
    if (fp->ad->region.l == 0)
        kputs("us-east-1", &fp->ad->region);
    
    
    /* use path-style url as virtual hosted-style has the possibility
       of breaking ssl certificates if there is a dot in the bucket name */
       
    kputs(fp->host_base.s, &fp->url);
    kputc('/', &fp->url);
    kputsn(bucket, strlen(bucket), &fp->url);

    
    fp->ad->canonical_uri = bucket;
    
    if ((fp->ad->bucket = strdup(bucket)) == NULL) {
        goto error;
    }
    
    // FIXME look at doing something with a token
    
    // set up the time, look at keeping this updated
    fp->ad->auth_time = time(NULL);
    base_time = gmtime(&fp->ad->auth_time);
    
    if (strftime(fp->ad->date_long, 17, "%Y%m%dT%H%M%SZ", base_time) != 16) {
        goto error;
    }
    
    if (strftime(fp->ad->date_short, 9, "%Y%m%d", base_time) != 8) {
        goto error;
    }
    
    ksprintf(&fp->ad->date_html, "x-amz-date: %s", fp->ad->date_long);
    
    ret = initialise_upload(fp, &header, &response);
    
    if (ret == 0) {
        long response_code;
        
        curl_easy_getinfo(fp->curl, CURLINFO_RESPONSE_CODE, &response_code);
    
        if (response_code == S3_MOVED_PERMANENTLY) {
            if (redirect_endpoint(fp, &header, bucket) == 0) {
                kfree(&response);
                kfree(&header);

                ret = initialise_upload(fp, &header, &response);
            }
        }

        kfree(&header); // no longer needed
    }
    
    if (ret) goto error;

    if (get_upload_id(fp, &response)) goto error;
    
    // start the completion message (a formatted list of parts)
    kinit(&fp->completion_message);

    if (kputs("<CompleteMultipartUpload>\n", &fp->completion_message) == EOF) {
        goto error;
    }
    
    fp->part_no = 1;

    fp->base.backend = &s3_write_backend;
    
    return &fp->base;
    
error:
    curl_easy_cleanup(fp->curl);
    curl_global_cleanup();
    
    // do some cleaning up here
    return NULL;
}


static hFILE *s3_open(const char *url, const char *mode)
{
    hFILE *fp;

    kstring_t mode_colon = { 0, 0, NULL };
    
    if (strchr(mode, 'w')) {
        fp = s3_open_for_writing(url, NULL);
    } else {
       kstring_t mode_colon = { 0, 0, NULL };
       kputs(mode, &mode_colon);
       kputc(':', &mode_colon);
       fp = s3_rewrite(url, mode_colon.s, NULL);
       free(mode_colon.s);
    }
    
    return fp;
}

static hFILE *s3_vopen(const char *url, const char *mode_colon, va_list args0)
{
    // Need to use va_copy() as we can only take the address of an actual
    // va_list object, not that of a parameter whose type may have decayed.
    va_list args;
    va_copy(args, args0);
    hFILE *fp = s3_rewrite(url, mode_colon, &args);
    va_end(args);
    return fp;
}

int PLUGIN_GLOBAL(hfile_plugin_init,_s3)(struct hFILE_plugin *self)
{
    static const struct hFILE_scheme_handler handler =
        { s3_open, hfile_always_remote, "Amazon S3", 2000 + 50, s3_vopen
        };

#ifdef ENABLE_PLUGINS
    // Embed version string for examination via strings(1) or what(1)
    static const char id[] = "@(#)hfile_s3 plugin (htslib)\t" HTS_VERSION;
    if (hts_verbose >= 9)
        fprintf(stderr, "[M::hfile_s3.init] version %s\n", strchr(id, '\t')+1);
#endif

    self->name = "Amazon S3";
    hfile_add_scheme_handler("s3", &handler);
    hfile_add_scheme_handler("s3+http", &handler);
    hfile_add_scheme_handler("s3+https", &handler);
    return 0;
}
