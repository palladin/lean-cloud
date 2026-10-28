/* Synchronous libcurl transport. Lean owns endpoint routing and exclusive
 * handle access. Typed transport failures are retried by Lean's shared policy. */
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
static lean_obj_res transfer_result(CURLcode code, lean_object *value) {
    lean_object *result = lean_alloc_ctor(code == CURLE_OK ? 1 : 0, 1, 0);
    lean_ctor_set(result, 0, code == CURLE_OK ? value : lean_box_uint32((uint32_t)code));
    return lean_io_result_mk_ok(result);
}
LEAN_EXPORT lean_obj_res lc_http_client(lean_obj_arg world) {
    (void)world;
    pthread_once(&once, initialize);
    if (!curl_ready) return fail("Cannot load the system libcurl runtime");
    CURL *client = p_curl_easy_init();
    if (!client) return fail("Cannot allocate HTTP client");
    return lean_io_result_mk_ok(lean_alloc_external(client_class, client));
}
struct buffer { char *data; size_t size, limit; };
static int progress(void *context, curl_off_t total, curl_off_t now,
    curl_off_t upload_total, curl_off_t upload_now) {
    (void)context; (void)total; (void)now; (void)upload_total; (void)upload_now;
    return lean_io_check_canceled_core() ? 1 : 0;
}
static size_t receive(char *data, size_t size, size_t count, void *context) {
    struct buffer *b = context;
    if (count && size > SIZE_MAX / count) return 0;
    size_t n = size * count;
    if (n > b->limit - b->size) return 0;
    char *next = realloc(b->data, b->size + n + 1);
    if (!next) return 0;
    b->data = next;
    memcpy(b->data + b->size, data, n);
    b->size += n; b->data[b->size] = 0;
    return n;
}
static lean_obj_res request_http(b_lean_obj_arg handle, b_lean_obj_arg url,
    const char *secret, b_lean_obj_arg body, uint32_t timeout) {
    CURL *c = lean_get_external_data(handle);
    struct curl_slist *headers = NULL;
    if (secret) {
        if (strchr(secret, '\r') || strchr(secret, '\n')) return fail("Invalid HTTP token");
        size_t auth_len = strlen(secret) + 23;
        char *auth = malloc(auth_len);
        if (!auth) return fail("HTTP allocation failed");
        snprintf(auth, auth_len, "Authorization: Bearer %s", secret);
        headers = p_curl_slist_append(headers, "Content-Type: application/json");
        headers = p_curl_slist_append(headers, "Expect:");
        headers = p_curl_slist_append(headers, auth);
        free(auth);
    }
    struct buffer b = { .limit = 16 * 1024 * 1024 };
    p_curl_easy_reset(c);
    p_curl_easy_setopt(c, CURLOPT_URL, lean_string_cstr(url));
#if LIBCURL_VERSION_NUM >= 0x075500
    p_curl_easy_setopt(c, CURLOPT_PROTOCOLS_STR, "http,https");
#else
    p_curl_easy_setopt(c, CURLOPT_PROTOCOLS, CURLPROTO_HTTP | CURLPROTO_HTTPS);
#endif
    p_curl_easy_setopt(c, CURLOPT_HTTPHEADER, headers);
    if (body) {
        p_curl_easy_setopt(c, CURLOPT_POSTFIELDS, lean_string_cstr(body));
        p_curl_easy_setopt(c, CURLOPT_POSTFIELDSIZE_LARGE, (curl_off_t)(lean_string_size(body) - 1));
    }
    p_curl_easy_setopt(c, CURLOPT_WRITEFUNCTION, receive);
    p_curl_easy_setopt(c, CURLOPT_WRITEDATA, &b);
    p_curl_easy_setopt(c, CURLOPT_NOSIGNAL, 1L);
    p_curl_easy_setopt(c, CURLOPT_NOPROGRESS, 0L);
    p_curl_easy_setopt(c, CURLOPT_XFERINFOFUNCTION, progress);
    p_curl_easy_setopt(c, CURLOPT_CONNECTTIMEOUT_MS, 10000L);
    p_curl_easy_setopt(c, CURLOPT_TIMEOUT_MS, (long)timeout);
    /* A restarted/reconnected node may have a different IP. easy_reset keeps
     * libcurl's DNS cache, whose default 60s lifetime outlasts our work leases.
     * Resolve each new connection instead of sending mail to an old address. */
    p_curl_easy_setopt(c, CURLOPT_DNS_CACHE_TIMEOUT, 0L);
    p_curl_easy_setopt(c, CURLOPT_NOPROXY, "*");
    CURLcode code = p_curl_easy_perform(c);
    long status = 0;
    p_curl_easy_getinfo(c, CURLINFO_RESPONSE_CODE, &status);
    p_curl_slist_free_all(headers);
    /* Clear borrowed pointers/credentials while retaining connection reuse. */
    p_curl_easy_reset(c);
    if (code != CURLE_OK) {
        free(b.data);
        return transfer_result(code, NULL);
    }
    lean_object *result = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(result, 0, lean_box_uint32((uint32_t)status));
    lean_ctor_set(result, 1, lean_mk_string_from_bytes(b.data ? b.data : "", b.size));
    free(b.data);
    return transfer_result(CURLE_OK, result);
}

LEAN_EXPORT lean_obj_res lc_http_post(b_lean_obj_arg handle, b_lean_obj_arg url,
    b_lean_obj_arg token, b_lean_obj_arg body, uint32_t timeout, lean_obj_arg world) {
    (void)world;
    return request_http(handle, url, lean_string_cstr(token), body, timeout);
}

/* Storage uses borrowed request bytes and grows the Lean response buffer
 * geometrically. No subprocesses, temporary files, or final response copy. */
struct binary_buffer { lean_object *bytes; size_t capacity; };
static size_t receive_binary(char *data, size_t size, size_t count, void *context) {
    struct binary_buffer *b = context;
    if (count && size > SIZE_MAX / count) return 0;
    size_t n = size * count, previous = lean_sarray_size(b->bytes);
    if (n > SIZE_MAX - previous - 1) return 0;
    size_t needed = previous + n;
    if (needed > b->capacity) {
        size_t capacity = b->capacity > SIZE_MAX / 2 ? needed : b->capacity * 2;
        if (capacity < 16384) capacity = 16384;
        if (capacity < needed) capacity = needed;
        lean_object *amount = lean_usize_to_nat(capacity);
        lean_object *next = lean_mk_empty_byte_array(amount);
        lean_dec(amount);
        memcpy(lean_sarray_cptr(next), lean_sarray_cptr(b->bytes), previous);
        lean_dec(b->bytes);
        b->bytes = next; b->capacity = capacity;
    }
    memcpy(lean_sarray_cptr(b->bytes) + previous, data, n);
    lean_sarray_set_size(b->bytes, needed);
    return n;
}

LEAN_EXPORT lean_obj_res lc_http_storage(b_lean_obj_arg handle, b_lean_obj_arg url,
        b_lean_obj_arg method, b_lean_obj_arg fields, b_lean_obj_arg body,
        b_lean_obj_arg signing, uint8_t no_proxy, lean_obj_arg world) {
    (void)world;
    CURL *c = lean_get_external_data(handle);
    struct curl_slist *headers = NULL;
    struct binary_buffer b = { .bytes = lean_mk_empty_byte_array(lean_box(0)), .capacity = 0 };
    CURLcode code = CURLE_OK;
    long status = 0;
    curl_off_t length = -1;
    const char *verb = lean_string_cstr(method);
    p_curl_easy_reset(c);
#define STORAGE_OPT(option, value) do { code = p_curl_easy_setopt(c, option, value); if (code != CURLE_OK) goto done; } while (0)
    for (size_t i = 0; i < lean_array_size(fields); ++i) {
        struct curl_slist *next = p_curl_slist_append(headers, lean_string_cstr(lean_array_get_core(fields, i)));
        if (!next) { code = CURLE_OUT_OF_MEMORY; goto done; }
        headers = next;
    }
    STORAGE_OPT(CURLOPT_URL, lean_string_cstr(url));
#if LIBCURL_VERSION_NUM >= 0x075500
    STORAGE_OPT(CURLOPT_PROTOCOLS_STR, "http,https");
#else
    STORAGE_OPT(CURLOPT_PROTOCOLS, CURLPROTO_HTTP | CURLPROTO_HTTPS);
#endif
    STORAGE_OPT(CURLOPT_HTTPHEADER, headers);
    STORAGE_OPT(CURLOPT_FOLLOWLOCATION, 0L);
    STORAGE_OPT(CURLOPT_NOSIGNAL, 1L);
    STORAGE_OPT(CURLOPT_CONNECTTIMEOUT_MS, 10000L);
    STORAGE_OPT(CURLOPT_TIMEOUT_MS, 60000L);
    STORAGE_OPT(CURLOPT_MAXCONNECTS, 4L);
    STORAGE_OPT(CURLOPT_NOPROGRESS, 0L);
    STORAGE_OPT(CURLOPT_XFERINFOFUNCTION, progress);
    STORAGE_OPT(CURLOPT_WRITEFUNCTION, receive_binary);
    STORAGE_OPT(CURLOPT_WRITEDATA, &b);
    if (no_proxy) STORAGE_OPT(CURLOPT_NOPROXY, "*");
    if (lean_array_size(signing) == 3) {
        STORAGE_OPT(CURLOPT_AWS_SIGV4, lean_string_cstr(lean_array_get_core(signing, 0)));
        STORAGE_OPT(CURLOPT_USERNAME, lean_string_cstr(lean_array_get_core(signing, 1)));
        STORAGE_OPT(CURLOPT_PASSWORD, lean_string_cstr(lean_array_get_core(signing, 2)));
    }
    if (!strcmp(verb, "PUT") || !strcmp(verb, "POST")) {
        STORAGE_OPT(CURLOPT_POSTFIELDS, lean_sarray_cptr(body));
        STORAGE_OPT(CURLOPT_POSTFIELDSIZE_LARGE, (curl_off_t)lean_sarray_size(body));
    }
    if (!strcmp(verb, "HEAD")) STORAGE_OPT(CURLOPT_NOBODY, 1L);
    STORAGE_OPT(CURLOPT_CUSTOMREQUEST, verb);
    code = p_curl_easy_perform(c);
    if (code == CURLE_OK) code = p_curl_easy_getinfo(c, CURLINFO_RESPONSE_CODE, &status);
    if (code == CURLE_OK) code = p_curl_easy_getinfo(c, CURLINFO_CONTENT_LENGTH_DOWNLOAD_T, &length);
done:
    /* Clear credentials and borrowed pointers; reset preserves connections. */
    p_curl_easy_reset(c);
    p_curl_slist_free_all(headers);
    if (code != CURLE_OK) {
        lean_dec(b.bytes);
        return transfer_result(code, NULL);
    }
    lean_object *known = lean_box(0);
    if (length >= 0) {
        known = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(known, 0, lean_uint64_to_nat((uint64_t)length));
    }
    lean_object *payload = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(payload, 0, b.bytes);
    lean_ctor_set(payload, 1, known);
    lean_object *result = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(result, 0, lean_box_uint32((uint32_t)status));
    lean_ctor_set(result, 1, payload);
    return transfer_result(CURLE_OK, result);
#undef STORAGE_OPT
}
