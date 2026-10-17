#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <limits.h>
#include <sys/stat.h>

#ifdef __APPLE__
#include <CommonCrypto/CommonDigest.h>
typedef CC_SHA256_CTX digest_ctx;
static int digest_init(digest_ctx *ctx) { return CC_SHA256_Init(ctx); }
static int digest_update(digest_ctx *ctx, const void *data, size_t size) {
    return CC_SHA256_Update(ctx, data, (CC_LONG)size);
}
static int digest_final(digest_ctx *ctx, unsigned char *hash) { return CC_SHA256_Final(hash, ctx); }
static void digest_free(digest_ctx *ctx) { (void)ctx; }
#else
#include <dlfcn.h>
#include <pthread.h>
typedef void *digest_ctx;
static void *crypto;
static void *(*ctx_new)(void);
static void (*ctx_free)(void *);
static const void *(*sha256)(void);
static int (*init_ex)(void *, const void *, void *);
static int (*update)(void *, const void *, size_t);
static int (*final_ex)(void *, unsigned char *, unsigned int *);
static pthread_once_t once = PTHREAD_ONCE_INIT;
static void load_crypto(void) {
    crypto = dlopen("libcrypto.so.3", RTLD_NOW | RTLD_LOCAL);
    if (!crypto) return;
    ctx_new = dlsym(crypto, "EVP_MD_CTX_new");
    ctx_free = dlsym(crypto, "EVP_MD_CTX_free");
    sha256 = dlsym(crypto, "EVP_sha256");
    init_ex = dlsym(crypto, "EVP_DigestInit_ex");
    update = dlsym(crypto, "EVP_DigestUpdate");
    final_ex = dlsym(crypto, "EVP_DigestFinal_ex");
}
static int digest_init(digest_ctx *ctx) {
    pthread_once(&once, load_crypto);
    *ctx = NULL;
    if (!ctx_new || !ctx_free || !sha256 || !init_ex || !update || !final_ex) return 0;
    *ctx = ctx_new();
    return *ctx && init_ex(*ctx, sha256(), NULL);
}
static int digest_update(digest_ctx *ctx, const void *data, size_t size) { return update(*ctx, data, size); }
static int digest_final(digest_ctx *ctx, unsigned char *hash) {
    unsigned int size = 0;
    return final_ex(*ctx, hash, &size) && size == 32;
}
static void digest_free(digest_ctx *ctx) { if (*ctx) ctx_free(*ctx); }
#endif

static lean_obj_res failure(void) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("File hashing or range copy failed")));
}
static lean_obj_res finish(digest_ctx *ctx, int ok) {
    unsigned char hash[32];
    char hex[65];
    ok = ok && digest_final(ctx, hash);
    digest_free(ctx);
    if (!ok) return failure();
    for (size_t i = 0; i < 32; ++i) snprintf(hex + 2*i, 3, "%02x", hash[i]);
    return lean_io_result_mk_ok(lean_mk_string(hex));
}

LEAN_EXPORT lean_obj_res lean_cloud_sha256_bytes(b_lean_obj_arg bytes, lean_obj_arg world) {
    (void)world;
    digest_ctx ctx;
    int ok = digest_init(&ctx);
    size_t size = lean_sarray_size(bytes), offset = 0;
    const unsigned char *data = lean_sarray_cptr(bytes);
    while (ok && offset < size) {
        size_t count = size - offset < 65536 ? size - offset : 65536;
        ok = digest_update(&ctx, data + offset, count);
        offset += count;
    }
    return finish(&ctx, ok);
}

LEAN_EXPORT lean_obj_res lean_cloud_sha256_file(b_lean_obj_arg path, lean_obj_arg world) {
    (void)world;
    FILE *input = fopen(lean_string_cstr(path), "rb");
    if (!input) return failure();
    digest_ctx ctx;
    int ok = digest_init(&ctx);
    unsigned char buffer[65536];
    size_t count;
    while (ok && (count = fread(buffer, 1, sizeof(buffer), input)) > 0)
        ok = digest_update(&ctx, buffer, count);
    ok = ok && !ferror(input);
    if (fclose(input)) ok = 0;
    return finish(&ctx, ok);
}

/* The caller owns a private output path. A range never reads beyond its pack. */
LEAN_EXPORT lean_obj_res lean_cloud_copy_range(b_lean_obj_arg source, b_lean_obj_arg destination,
        uint64_t offset, uint64_t length, uint8_t executable, lean_obj_arg world) {
    (void)world;
    if (offset > INT64_MAX || length > INT64_MAX - offset) return failure();
    FILE *input = fopen(lean_string_cstr(source), "rb");
    if (!input) return failure();
    struct stat source_stat;
    if (fstat(fileno(input), &source_stat) || source_stat.st_size < 0 ||
        offset + length > (uint64_t)source_stat.st_size) { fclose(input); return failure(); }
    if (fseeko(input, (off_t)offset, SEEK_SET)) { fclose(input); return failure(); }
    FILE *output = fopen(lean_string_cstr(destination), "wb");
    if (!output) { fclose(input); return failure(); }
    digest_ctx ctx;
    int ok = digest_init(&ctx);
    unsigned char buffer[65536];
    while (ok && length) {
        size_t count = length < sizeof(buffer) ? (size_t)length : sizeof(buffer);
        ok = fread(buffer, 1, count, input) == count &&
            fwrite(buffer, 1, count, output) == count && digest_update(&ctx, buffer, count);
        length -= count;
    }
    struct stat permissions;
    if (fstat(fileno(output), &permissions) ||
        fchmod(fileno(output), (permissions.st_mode & 0777 & ~0111) | (executable ? 0100 : 0))) ok = 0;
    if (fclose(input)) ok = 0;
    if (fclose(output)) ok = 0;
    return finish(&ctx, ok);
}
