/*
    hfile_s3_write.c
    
    Code to handle mulitpart uploading to S3.
    
    Andrew Whitwham, January 2019
*/

#include <config.h>

#include <stdarg.h>
#include <stdlib.h>
#include <string.h>
#ifdef __MSYS__
#include <strings.h>
#endif
#include <errno.h>
#include <pthread.h>

#include "hfile_internal.h"
#ifdef ENABLE_PLUGINS
#include "version.h"
#endif
#include "htslib/hts.h"  // for hts_version() and hts_verbose
#include "htslib/kstring.h"
#include "htslib/khash.h"

#include <curl/curl.h>

#define MINIMUM_S3_WRITE_SIZE 5242880
#define S3_MOVED_PERMANENTLY 301

typedef int (*s3_auth_callback) (void *auth_data, char *, kstring_t*, char*, kstring_t*, kstring_t*, kstring_t*);
typedef int (*redirect_callback) (void *auth_data, kstring_t*, kstring_t*);

typedef struct {
    s3_auth_callback callback;
    redirect_callback redirect_callback;
    void *callback_data;
} s3_authorisation;

typedef struct { // FIXME DON@T KNOW IF NEEDED
    char *path;
    char *token;
    time_t expiry;
    int failed;
    pthread_mutex_t lock;
} auth_token;

// For the authorization header cache (DON'T KNOW IF I NEED IT YET FIXME)
KHASH_MAP_INIT_STR(auth_map, auth_token *)

static struct {
    kstring_t useragent;
    CURLSH *share;
    char *auth_path;
    khash_t(auth_map) *auth_map;
    pthread_mutex_t auth_lock;
    pthread_mutex_t share_lock;
} curl = { { 0, 0, NULL }, NULL, NULL, NULL, PTHREAD_MUTEX_INITIALIZER,
           PTHREAD_MUTEX_INITIALIZER };

static void share_lock(CURL *handle, curl_lock_data data,
                       curl_lock_access access, void *userptr) {
    pthread_mutex_lock(&curl.share_lock);
}

static void share_unlock(CURL *handle, curl_lock_data data, void *userptr) {
    pthread_mutex_unlock(&curl.share_lock);
}


static void free_auth(auth_token *tok) {
    if (!tok) return;
    if (pthread_mutex_destroy(&tok->lock)) abort();
    free(tok->path);
    free(tok->token);
    free(tok);
}


typedef struct {
    hFILE base;
    CURL *curl;
    CURLcode ret;
    s3_authorisation *au;
    kstring_t buffer;
    kstring_t url;
    kstring_t token_hdr;
    kstring_t upload_id;
    kstring_t completion_message;
    int part_no;
    int aborted;
    size_t index;
    long verbose;
} hFILE_s3_write;


static void kinit(kstring_t *s) {
    s->l = 0;
    s->m = 0;
    s->s = NULL;
}

static void ksfree(kstring_t *s) {
    free(s->s);
    kinit(s);
}


size_t response_callback(void *contents, size_t size, size_t nmemb, void *userp) {
    size_t realsize = size * nmemb;
    kstring_t *resp = (kstring_t *)userp;

    if (kputsn((const char *)contents, realsize, resp) == EOF) {
        return 0;
    }    
    
    return realsize;
}


static int get_entry(char *in, char *start_tag, char *end_tag, kstring_t *out) {
    char *start;
    char *end;
    
    if (!in) {
        return EOF;
    }
    
    start = strstr(in, start_tag);
    
    if (start) {
        start += strlen(start_tag);
        end = strstr(start, end_tag);
    }
    
    if (!start || !end) return EOF;
    
    return kputsn(start, end - start, out);
}


static void cleanup(hFILE_s3_write *fp) {
    ksfree(&fp->buffer);
    ksfree(&fp->url);
    ksfree(&fp->token_hdr);
    ksfree(&fp->upload_id);
    ksfree(&fp->completion_message);
    
    // free up authorisation data
    fp->au->callback(fp->au->callback_data,  NULL, NULL, NULL, NULL, NULL, NULL);
    free(fp->au);
    
    curl_easy_cleanup(fp->curl);
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


/*
    The partially uploaded file will hang around unless the delete command is sent.
*/
static int abort_upload(hFILE_s3_write *fp) {
    kstring_t content_hash = {0, 0, NULL};
    kstring_t authorisation = {0, 0, NULL};
    kstring_t url = {0, 0, NULL};
    kstring_t content = {0, 0, NULL};
    kstring_t canonical_query_string = {0, 0, NULL};
    kstring_t date = {0, 0, NULL};
    int ret = 0;
    struct curl_slist *headers;
    char http_request[] = "DELETE";
    
    if (ksprintf(&canonical_query_string, "uploadId=%s", fp->upload_id.s) < 0) {
        return -1;
    }    

    ret = fp->au->callback(fp->au->callback_data,  http_request, NULL,
             canonical_query_string.s, &content_hash, &authorisation, &date);
             
    if (ret) {
        return -1;
    }

    if (ksprintf(&url, "%s?%s", fp->url.s, canonical_query_string.s) < 0) {
        return -1;
    }
    
    ksprintf(&content, "x-amz-content-sha256: %s", content_hash.s);

    curl_easy_reset(fp->curl);
    curl_easy_setopt(fp->curl, CURLOPT_CUSTOMREQUEST, http_request);
    curl_easy_setopt(fp->curl, CURLOPT_USERAGENT, curl.useragent.s);
    curl_easy_setopt(fp->curl, CURLOPT_URL, url.s);
    
    curl_easy_setopt(fp->curl, CURLOPT_VERBOSE, fp->verbose);

    headers = set_html_headers(fp, &authorisation, &date, &content);
    fp->ret = curl_easy_perform(fp->curl);
    
    if (fp->ret != CURLE_OK) {
        ret = -1;
    }
       
    ksfree(&authorisation);
    ksfree(&content);
    ksfree(&content_hash);
    ksfree(&url);
    ksfree(&date);    
    ksfree(&canonical_query_string);    
    curl_slist_free_all(headers);
    
    fp->aborted = 1;
    cleanup(fp);
    
    return ret;
}


static int complete_upload(hFILE_s3_write *fp, kstring_t *resp) {
    kstring_t content_hash = {0, 0, NULL};
    kstring_t authorisation = {0, 0, NULL};
    kstring_t url = {0, 0, NULL};
    kstring_t content = {0, 0, NULL};
    kstring_t canonical_query_string = {0, 0, NULL};
    kstring_t date = {0, 0, NULL};
    int ret = 0;
    struct curl_slist *headers;
    char http_request[] = "POST";
    
    if (ksprintf(&canonical_query_string, "uploadId=%s", fp->upload_id.s) < 0) {
        return -1;
    }
    
    // finish off the completion reply
    kputs("</CompleteMultipartUpload>\n", &fp->completion_message);
    
    ret = fp->au->callback(fp->au->callback_data,  http_request, &fp->completion_message,
             canonical_query_string.s, &content_hash, &authorisation, &date);

    if (ret) {
        return -1;
    }
    
    if (ksprintf(&url, "%s?%s", fp->url.s, canonical_query_string.s) < 0) {
        return -1;
    }
    
    ksprintf(&content, "x-amz-content-sha256: %s", content_hash.s);
    
    curl_easy_reset(fp->curl);
    curl_easy_setopt(fp->curl, CURLOPT_POST, 1L);
    curl_easy_setopt(fp->curl, CURLOPT_POSTFIELDS, fp->completion_message.s);
    curl_easy_setopt(fp->curl, CURLOPT_POSTFIELDSIZE, fp->completion_message.l);
    curl_easy_setopt(fp->curl, CURLOPT_WRITEFUNCTION, response_callback);
    curl_easy_setopt(fp->curl, CURLOPT_WRITEDATA, (void *)resp);
    curl_easy_setopt(fp->curl, CURLOPT_URL, url.s);
    curl_easy_setopt(fp->curl, CURLOPT_USERAGENT, curl.useragent.s);
    
    curl_easy_setopt(fp->curl, CURLOPT_VERBOSE, fp->verbose);
    
    headers = set_html_headers(fp, &authorisation, &date, &content);
    fp->ret = curl_easy_perform(fp->curl);
    
    if (fp->ret != CURLE_OK) {
        ret = -1;
    }
       
    ksfree(&authorisation);
    ksfree(&content);
    ksfree(&content_hash);
    ksfree(&url);
    ksfree(&date);    
    ksfree(&canonical_query_string);    
    curl_slist_free_all(headers);
    
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
    kstring_t content_hash = {0, 0, NULL};
    kstring_t authorisation = {0, 0, NULL};
    kstring_t url = {0, 0, NULL};
    kstring_t content = {0, 0, NULL};
    kstring_t canonical_query_string = {0, 0, NULL};
    kstring_t date = {0, 0, NULL};
    int ret = 0;
    struct curl_slist *headers;
    char http_request[] = "PUT";
    
    if (ksprintf(&canonical_query_string, "partNumber=%d&uploadId=%s", fp->part_no, fp->upload_id.s) < 0) {
        return -1;
    }

    ret = fp->au->callback(
            fp->au->callback_data, http_request, &fp->buffer, canonical_query_string.s,
            &content_hash, &authorisation, &date);

    if (ret) {
        return -1;
    }
    
    if (ksprintf(&url, "%s?%s", fp->url.s, canonical_query_string.s) < 0) {
        return -1;
    }
    
    fp->index = 0;
    ksprintf(&content, "x-amz-content-sha256: %s", content_hash.s);
    
    curl_easy_reset(fp->curl);

    curl_easy_setopt(fp->curl, CURLOPT_UPLOAD, 1L);
    curl_easy_setopt(fp->curl, CURLOPT_READFUNCTION, upload_callback);
    curl_easy_setopt(fp->curl, CURLOPT_READDATA, fp);
    curl_easy_setopt(fp->curl, CURLOPT_INFILESIZE_LARGE, (curl_off_t)fp->buffer.l);       
    curl_easy_setopt(fp->curl, CURLOPT_HEADERFUNCTION, response_callback);
    curl_easy_setopt(fp->curl, CURLOPT_HEADERDATA, (void *)resp);
    curl_easy_setopt(fp->curl, CURLOPT_URL, url.s);
    curl_easy_setopt(fp->curl, CURLOPT_USERAGENT, curl.useragent.s);
    
    curl_easy_setopt(fp->curl, CURLOPT_VERBOSE, fp->verbose);    
    
    headers = set_html_headers(fp, &authorisation, &date, &content);
    fp->ret = curl_easy_perform(fp->curl);
    
    if (fp->ret != CURLE_OK) {
        ret = -1;
    }
       
    ksfree(&authorisation);
    ksfree(&content);
    ksfree(&content_hash);
    ksfree(&url);
    ksfree(&date);    
    ksfree(&canonical_query_string);    
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
                        
                    ksfree(&etag);
                }
            }
        }
        
        ksfree(&response);
        
        if (ret) {
            abort_upload(fp);
            return -1;
        }
        
        fp->part_no++;
        fp->buffer.l = 0;
    }

    return nbytes;
}


static int s3_close(hFILE *fpv) {
    hFILE_s3_write *fp = (hFILE_s3_write *)fpv;
    kstring_t response = {0, 0, NULL};
    int ret = 0;
    
    if (!fp->aborted) {

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

                        ksfree(&etag);
                    }
                }
            }

            ksfree(&response);

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
        } else {
            cleanup(fp);
        }
    }
    
    ksfree(&response);

    return ret;
}


static int redirect_endpoint(hFILE_s3_write *fp, kstring_t *head) {
    int ret = -1;

    if (fp->au->redirect_callback) {
        ret = fp->au->redirect_callback(fp->au->callback_data, head, &fp->url);
    }
    
    return ret;
}


static int initialise_upload(hFILE_s3_write *fp, kstring_t *head, kstring_t *resp) {
    kstring_t content_hash = {0, 0, NULL};
    kstring_t authorisation = {0, 0, NULL};
    kstring_t url = {0, 0, NULL};
    kstring_t content = {0, 0, NULL};
    kstring_t date = {0, 0, NULL};
    int ret = 0;
    struct curl_slist *headers;
    char http_request[] = "POST";
    
    ret = fp->au->callback(fp->au->callback_data,  http_request, NULL,
             "uploads=", &content_hash, &authorisation, &date);
             
    if (ret) {
        return -1;
    }
    
    ksprintf(&url, "%s?uploads", fp->url.s);
    
    if (url.l == 0) {
        return -1;
    }
    
    ksprintf(&content, "x-amz-content-sha256: %s", content_hash.s);

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
    curl_easy_setopt(fp->curl, CURLOPT_USERAGENT, curl.useragent.s);
    
    curl_easy_setopt(fp->curl, CURLOPT_VERBOSE, fp->verbose);
    
    headers = set_html_headers(fp, &authorisation, &date, &content);
    fp->ret = curl_easy_perform(fp->curl);
    
    if (fp->ret != CURLE_OK) {
        ret = -1;
    }
       
    ksfree(&authorisation);
    ksfree(&content);
    ksfree(&content_hash);
    ksfree(&url);
    ksfree(&date);    
    curl_slist_free_all(headers);
    
    return ret;    
}


static int get_upload_id(hFILE_s3_write *fp, kstring_t *resp) {
    int ret = 0;

    kinit(&fp->upload_id);

    if (get_entry(resp->s, "<UploadId>", "</UploadId>", &fp->upload_id) == EOF) {
        ret = -1;
    }
    
    return ret;
}


static const struct hFILE_backend s3_write_backend = {
    NULL, s3_write, NULL, NULL, s3_close
};


static hFILE *s3_write_open(const char *url, s3_authorisation *auth) {
    hFILE_s3_write *fp;
    kstring_t response = {0, 0, NULL};
    kstring_t header   = {0, 0, NULL};
    int ret;
    
    if (!auth || !auth->callback || !auth->callback_data) {
        // FIXME ERROR STUFF
        return NULL;
    }
    
    fp = (hFILE_s3_write *)hfile_init(sizeof(hFILE_s3_write), "w", 0);
    
    if (fp == NULL) {
        // FIXME ERROR STUFF HERE
        return NULL;
    }
    
    if ((fp->curl = curl_easy_init()) == NULL) {
        errno = ENOMEM;
        goto error;
    }
    
    if ((fp->au = calloc(1, sizeof(s3_authorisation))) == NULL) {
        goto error;
    }
    
    memcpy(fp->au, auth, sizeof(s3_authorisation));
    
    kinit(&fp->buffer);
    kinit(&fp->url);
    kinit(&fp->token_hdr);
    fp->aborted = 0;
    
    if (hts_verbose >= 8) {
        fp->verbose = 1L;
    } else {
        fp->verbose = 0L;
    }
    
    kputs(url + 4, &fp->url);

    ret = initialise_upload(fp, &header, &response);
    
    if (ret == 0) {
        long response_code;
        
        curl_easy_getinfo(fp->curl, CURLINFO_RESPONSE_CODE, &response_code);
    
        if (response_code == S3_MOVED_PERMANENTLY) {
            if (redirect_endpoint(fp, &header) == 0) {
                ksfree(&response);
                ksfree(&header);

                ret = initialise_upload(fp, &header, &response);
            }
        }

        ksfree(&header); // no longer needed
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
    ksfree(&response);

    return &fp->base;
    
error:
    // do some cleaning up here FIXME
    return NULL;
}
    

static hFILE *hopen_s3_write(const char *url, const char *mode) {
    
    return s3_write_open(url, NULL);
}


static int parse_va_list(s3_authorisation *auth, va_list args) {
    const char *argtype;
    
    while  ((argtype = va_arg(args, const char *)) != NULL) {
        if (strcmp(argtype, "s3_auth_callback") == 0) {
            auth->callback = va_arg(args, s3_auth_callback);
        } else if (strcmp(argtype, "s3_auth_callback_data") == 0) {
            auth->callback_data = va_arg(args, void *);
        } else if (strcmp(argtype, "redirect_callback") == 0) {
            auth->redirect_callback = va_arg(args, redirect_callback);
        } else if (strcmp(argtype, "va_list") == 0) {
            va_list *args2 = va_arg(args, va_list *);
            
            if (args2) {
                if (parse_va_list(auth, *args2) < 0) return -1;
            }
        } else {
            errno = EINVAL;
            return -1;
        }
    }
    
    return 0;
}


static hFILE *vhopen_s3_write(const char *url, const char *mode, va_list args) {
    hFILE *fp = NULL;
    s3_authorisation auth = {NULL, NULL, NULL};
    
    if (parse_va_list(&auth, args) == 0) {
        fp =  s3_write_open(url, &auth);
    }
    
    return fp;
}    


static void s3_write_exit() {
    if (curl_share_cleanup(curl.share) == CURLSHE_OK)
        curl.share = NULL;

    free(curl.useragent.s);
    curl.useragent.l = curl.useragent.m = 0; curl.useragent.s = NULL;

    free(curl.auth_path);
    curl.auth_path = NULL;

    if (curl.auth_map) {
        khiter_t i;
        for (i = kh_begin(curl.auth_map); i != kh_end(curl.auth_map); ++i) {
            if (kh_exist(curl.auth_map, i)) {
                free_auth(kh_value(curl.auth_map, i));
                kh_key(curl.auth_map, i) = NULL;
                kh_value(curl.auth_map, i) = NULL;
            }
        }
        kh_destroy(auth_map, curl.auth_map);
        curl.auth_map = NULL;
    }

    curl_global_cleanup();
}


int PLUGIN_GLOBAL(hfile_plugin_init,_s3_write)(struct hFILE_plugin *self) {

    static const struct hFILE_scheme_handler handler =
        { hopen_s3_write, hfile_always_remote, "S3 Multipart Upload",
          2000 + 50, vhopen_s3_write
        };
        
#ifdef ENABLE_PLUGINS
    // Embed version string for examination via strings(1) or what(1)
    static const char id[] = "@(#)hfile_s3_write plugin (htslib)\t" HTS_VERSION;
    const char *version = strchr(id, '\t') + 1;
    
    if (hts_verbose >= 9)
        fprintf(stderr, "[M::hfile_s3_write.init] version %s\n",
                version);
#else
    const char *version = hts_version();
#endif

    const curl_version_info_data *info;
    CURLcode err;
    CURLSHcode errsh;
    
    err = curl_global_init(CURL_GLOBAL_ALL);
    
    if (err != CURLE_OK) {
        // look at putting in an errno here
        return -1;
    }
    
    curl.share = curl_share_init();
    
    if (curl.share == NULL) {
        curl_global_cleanup();
        errno = EIO;
        return -1;
    }
    
    errsh  = curl_share_setopt(curl.share, CURLSHOPT_LOCKFUNC, share_lock);
    errsh |= curl_share_setopt(curl.share, CURLSHOPT_UNLOCKFUNC, share_unlock);
    errsh |= curl_share_setopt(curl.share, CURLSHOPT_SHARE, CURL_LOCK_DATA_DNS);

    if (errsh != 0) {
        curl_share_cleanup(curl.share);
        curl_global_cleanup();
        errno = EIO;
        return -1;
    }
    
    info = curl_version_info(CURLVERSION_NOW);
    ksprintf(&curl.useragent, "htslib/%s libcurl/%s", version, info->version);
    
    self->name = "S3 Multipart Upload";
    self->destroy = s3_write_exit;

    hfile_add_scheme_handler("s3w",       &handler);
    hfile_add_scheme_handler("s3w+http",  &handler);
    hfile_add_scheme_handler("s3w+https", &handler);
    
    return 0;
}
