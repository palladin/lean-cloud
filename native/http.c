/* Synchronous libcurl transport. Lean owns endpoint routing and exclusive
 * handle access. No retries: a failed response may follow a committed send. */
#include <lean/lean.h>
#include <curl/curl.h>
#include <pthread.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdio.h>

#include <dlfcn.h>
static CURL * (*p_curl_easy_init)(void);
static void (*p_curl_easy_cleanup)(CURL *);
static void (*p_curl_easy_reset)(CURL *);
static CURLcode (*p_curl_easy_setopt)(CURL *, CURLoption, ...);
static CURLcode (*p_curl_easy_getinfo)(CURL *, CURLINFO, ...);
static CURLcode (*p_curl_easy_perform)(CURL *);
static const char * (*p_curl_easy_strerror)(CURLcode);
static CURLcode (*p_curl_global_init)(long);
static struct curl_slist * (*p_curl_slist_append)(struct curl_slist *, const char *);
static void (*p_curl_slist_free_all)(struct curl_slist *);
static int curl_ready;
static lean_external_class *client_class;
static pthread_once_t once = PTHREAD_ONCE_INIT;
static void finalize(void *p) { p_curl_easy_cleanup(p); }
static void visit(void *p, b_lean_obj_arg f) { (void)p; (void)f; }
static void initialize(void) {
#ifdef __APPLE__
    void *library = dlopen("/usr/lib/libcurl.4.dylib", RTLD_NOW | RTLD_LOCAL);
#else
    void *library = dlopen("libcurl.so.4", RTLD_NOW | RTLD_LOCAL);
#endif
    if (!library) return;
    p_curl_easy_init = (CURL * (*)(void))dlsym(library, "curl_easy_init");
    if (!p_curl_easy_init) return;
    p_curl_easy_cleanup = (void (*)(CURL *))dlsym(library, "curl_easy_cleanup");
    if (!p_curl_easy_cleanup) return;
    p_curl_easy_reset = (void (*)(CURL *))dlsym(library, "curl_easy_reset");
    if (!p_curl_easy_reset) return;
    p_curl_easy_setopt = (CURLcode (*)(CURL *, CURLoption, ...))dlsym(library, "curl_easy_setopt");
    if (!p_curl_easy_setopt) return;
    p_curl_easy_getinfo = (CURLcode (*)(CURL *, CURLINFO, ...))dlsym(library, "curl_easy_getinfo");
    if (!p_curl_easy_getinfo) return;
    p_curl_easy_perform = (CURLcode (*)(CURL *))dlsym(library, "curl_easy_perform");
    if (!p_curl_easy_perform) return;
    p_curl_easy_strerror = (const char * (*)(CURLcode))dlsym(library, "curl_easy_strerror");
    if (!p_curl_easy_strerror) return;
    p_curl_global_init = (CURLcode (*)(long))dlsym(library, "curl_global_init");
    if (!p_curl_global_init) return;
    p_curl_slist_append = (struct curl_slist * (*)(struct curl_slist *, const char *))dlsym(library, "curl_slist_append");
    if (!p_curl_slist_append) return;
    p_curl_slist_free_all = (void (*)(struct curl_slist *))dlsym(library, "curl_slist_free_all");
    if (!p_curl_slist_free_all) return;
    if (p_curl_global_init(CURL_GLOBAL_DEFAULT) != CURLE_OK) return;
    curl_ready = 1;
    client_class = lean_register_external_class(finalize, visit);
}
static lean_obj_res fail(const char *message) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(message)));
}
LEAN_EXPORT lean_obj_res lc_http_client(lean_obj_arg world) {
    (void)world;
    pthread_once(&once, initialize);
    if (!curl_ready) return fail("Cannot load the system libcurl runtime");
    CURL *client = p_curl_easy_init();
    if (!client) return fail("Cannot allocate HTTP client");
    return lean_io_result_mk_ok(lean_alloc_external(client_class, client));
}
struct buffer { char *data; size_t size; };
static size_t receive(char *data, size_t size, size_t count, void *context) {
    struct buffer *b = context;
    if (count && size > SIZE_MAX / count) return 0;
    size_t n = size * count;
    if (n > 16 * 1024 * 1024 - b->size) return 0;
    char *next = realloc(b->data, b->size + n + 1);
    if (!next) return 0;
    b->data = next;
    memcpy(b->data + b->size, data, n);
    b->size += n; b->data[b->size] = 0;
    return n;
}
LEAN_EXPORT lean_obj_res lc_http_post(b_lean_obj_arg handle, b_lean_obj_arg url,
    b_lean_obj_arg token, b_lean_obj_arg body, uint32_t timeout, lean_obj_arg world) {
    (void)world;
    CURL *c = lean_get_external_data(handle);
    const char *secret = lean_string_cstr(token);
    if (strchr(secret, '\r') || strchr(secret, '\n')) return fail("Invalid HTTP token");
    size_t auth_len = strlen(secret) + 23;
    char *auth = malloc(auth_len);
    if (!auth) return fail("HTTP allocation failed");
    snprintf(auth, auth_len, "Authorization: Bearer %s", secret);
    struct curl_slist *headers = NULL;
    headers = p_curl_slist_append(headers, "Content-Type: application/json");
    headers = p_curl_slist_append(headers, "Expect:");
    headers = p_curl_slist_append(headers, auth);
    free(auth);
    struct buffer b = {0};
    char error[CURL_ERROR_SIZE] = {0};
    p_curl_easy_reset(c);
    p_curl_easy_setopt(c, CURLOPT_URL, lean_string_cstr(url));
#if LIBCURL_VERSION_NUM >= 0x075500
    p_curl_easy_setopt(c, CURLOPT_PROTOCOLS_STR, "http,https");
#else
    p_curl_easy_setopt(c, CURLOPT_PROTOCOLS, CURLPROTO_HTTP | CURLPROTO_HTTPS);
#endif
    p_curl_easy_setopt(c, CURLOPT_HTTPHEADER, headers);
    p_curl_easy_setopt(c, CURLOPT_POSTFIELDS, lean_string_cstr(body));
    p_curl_easy_setopt(c, CURLOPT_POSTFIELDSIZE_LARGE, (curl_off_t)(lean_string_size(body) - 1));
    p_curl_easy_setopt(c, CURLOPT_WRITEFUNCTION, receive);
    p_curl_easy_setopt(c, CURLOPT_WRITEDATA, &b);
    p_curl_easy_setopt(c, CURLOPT_ERRORBUFFER, error);
    p_curl_easy_setopt(c, CURLOPT_NOSIGNAL, 1L);
    p_curl_easy_setopt(c, CURLOPT_CONNECTTIMEOUT_MS, 2000L);
    p_curl_easy_setopt(c, CURLOPT_TIMEOUT_MS, (long)timeout);
    p_curl_easy_setopt(c, CURLOPT_NOPROXY, "*");
    CURLcode code = p_curl_easy_perform(c);
    long status = 0;
    p_curl_easy_getinfo(c, CURLINFO_RESPONSE_CODE, &status);
    p_curl_slist_free_all(headers);
    if (code != CURLE_OK) {
        free(b.data);
        return fail(error[0] ? error : p_curl_easy_strerror(code));
    }
    lean_object *result = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(result, 0, lean_box_uint32((uint32_t)status));
    lean_ctor_set(result, 1, lean_mk_string_from_bytes(b.data ? b.data : "", b.size));
    free(b.data);
    return lean_io_result_mk_ok(result);
}
