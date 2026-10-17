#define _POSIX_C_SOURCE 200809L
#include <lean/lean.h>
#include <expat.h>
#include <bzlib.h>
#include <regex.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <inttypes.h>
#include <time.h>
#include <errno.h>
#include <locale.h>

/* Only compression/XML/regex machinery lives in C. Workflows, blob transfers,
   vocabulary analysis, request validation and result aggregation live in Lean. */
#define PAGE_LIMIT (8u * 1024u * 1024u)
#define ARTICLE_LIMIT (64u * 1024u * 1024u)
#define EXPANDED_LIMIT (1024ull * 1024ull * 1024ull)
#define MAX_SHARDS 2048
static lean_obj_res failure(const char *s) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(s)));
}
static double now(void) {
    struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t);
    return (double)t.tv_sec + (double)t.tv_nsec / 1e9;
}
typedef struct { char *data; size_t len, cap; } Buffer;
static int append(Buffer *b, const char *s, size_t n) {
    if (n > PAGE_LIMIT || b->len > PAGE_LIMIT - n) return 0;
    if (b->len + n + 1 > b->cap) {
        size_t cap = (b->len + n + 1) * 2;
        char *p = realloc(b->data, cap);
        if (!p) return 0;
        b->data = p; b->cap = cap;
    }
    memcpy(b->data + b->len, s, n); b->len += n; b->data[b->len] = 0;
    return 1;
}
static void clear(Buffer *b) { b->len = 0; if (b->data) b->data[0] = 0; }
static const char *value(Buffer *b) { return b->data ? b->data : ""; }
static const char *local(const char *name) {
    const char *p = strrchr(name, '|'); return p ? p + 1 : name;
}
/* JSON quoting preserves UTF-8, which Expat validates. */
static size_t quoted_size(Buffer *b) {
    size_t n = 2;
    for (size_t i = 0; i < b->len; i++) {
        unsigned char c = (unsigned char)b->data[i];
        n += c < 32 ? 6 : (c == '"' || c == '\\' ? 2 : 1);
    }
    return n;
}
static void quote(FILE *f, Buffer *b) {
    fputc('"', f);
    for (size_t i = 0; i < b->len; i++) {
        unsigned char c = (unsigned char)b->data[i];
        if (c < 32) fprintf(f, "\\u%04x", c);
        else { if (c == '"' || c == '\\') fputc('\\', f); fputc(c, f); }
    }
    fputc('"', f);
}
typedef struct {
    XML_Parser xml;
    const char *directory;
    uint64_t target, expanded, written, total_output;
    uint32_t namespace;
    int redirects, depth, page, revision, revisions, field, field_depth, redirect;
    int seen[6];
    Buffer fields[6]; /* title, namespace, page ID, revision ID, text, model */
    char error[256];
    FILE *out;
    unsigned files;
    uint64_t pages, counts[MAX_SHARDS];
    double deadline;
} Parser;
static void stop(Parser *p, const char *message) {
    if (!p->error[0]) snprintf(p->error, sizeof(p->error), "%s", message);
    XML_StopParser(p->xml, XML_FALSE);
}
static int number(Buffer *b, uint64_t *out) {
    if (!b->len) return 0;
    uint64_t v = 0;
    for (size_t i = 0; i < b->len; i++) {
        unsigned char c = (unsigned char)b->data[i];
        if (c < '0' || c > '9' || v > (UINT64_MAX - (c - '0')) / 10) return 0;
        v = v * 10 + (c - '0');
    }
    *out = v; return 1;
}
static void finish_page(Parser *p) {
    uint64_t id, revision, ns;
    if (!number(&p->fields[1], &ns)) { stop(p, "Missing or invalid page namespace"); return; }
    if (ns != p->namespace) return;
    if (!p->redirects && p->redirect) return;
    if (!p->seen[0] || !p->seen[4] || p->revisions != 1 ||
        !number(&p->fields[2], &id) || !number(&p->fields[3], &revision)) {
        stop(p, "Expected a current-page dump with title, IDs and one visible text revision"); return;
    }
    if (p->seen[5] && strcmp(value(&p->fields[5]), "wikitext")) {
        stop(p, "Selected page has a non-wikitext content model"); return;
    }
    /* Includes enough room for every numeric field and JSON key. */
    size_t bytes = quoted_size(&p->fields[0]) + quoted_size(&p->fields[4]) + 160;
    /* The NDJSON reader applies the same limit, after JSON escaping. */
    if (bytes > ARTICLE_LIMIT) { stop(p, "Encoded article exceeds 64 MiB"); return; }
    p->total_output += bytes;
    if (p->total_output > EXPANDED_LIMIT) { stop(p, "Article output exceeds 1 GiB per part"); return; }
    if (p->out && p->written + bytes > p->target) {
        if (fclose(p->out)) { p->out = NULL; stop(p, "Cannot flush article shard"); return; }
        p->out = NULL;
    }
    if (!p->out) {
        if (p->files == MAX_SHARDS) { stop(p, "Too many output shards"); return; }
        char path[4096];
        if (snprintf(path, sizeof(path), "%s/%u.jsonl", p->directory, p->files) >= (int)sizeof(path)) {
            stop(p, "Output path too long"); return;
        }
        p->out = fopen(path, "wx");
        if (!p->out) { stop(p, "Cannot create article shard"); return; }
        p->files++; p->written = 0;
    }
    fprintf(p->out, "{\"id\":%" PRIu64 ",\"revision\":%" PRIu64 ",\"ns\":%" PRIu64 ",\"title\":", id, revision, ns);
    quote(p->out, &p->fields[0]); fputs(",\"text\":", p->out);
    quote(p->out, &p->fields[4]); fputs("}\n", p->out);
    if (ferror(p->out)) { stop(p, "Cannot write article shard"); return; }
    p->written += bytes; p->counts[p->files-1]++; p->pages++;
}
static void XMLCALL start(void *data, const char *tag, const char **attrs) {
    Parser *p = data; const char *name = local(tag); p->depth++;
    if (p->depth > 64) { stop(p, "XML nesting limit exceeded"); return; }
    if (p->depth == 1 && strcmp(name, "mediawiki")) { stop(p, "Expected mediawiki XML root"); return; }
    if (p->depth == 2 && !strcmp(name, "page")) {
        p->page = 1; p->revision = 0; p->revisions = 0; p->redirect = 0;
        for (unsigned i = 0; i < 6; i++) { clear(&p->fields[i]); p->seen[i] = 0; }
    }
    if (!p->page) return;
    if (p->field >= 0) { stop(p, "Unexpected nested XML in a page field"); return; }
    if (p->depth == 3 && !strcmp(name, "redirect")) p->redirect = 1;
    if (p->depth == 3 && !strcmp(name, "revision")) { p->revision = 1; p->revisions++; }
    int field = -1;
    if (p->depth == 3) {
        if (!strcmp(name, "title")) field = 0;
        if (!strcmp(name, "ns")) field = 1;
        if (!strcmp(name, "id")) field = 2;
    }
    if (p->depth == 4 && p->revision) {
        if (!strcmp(name, "id")) field = 3;
        if (!strcmp(name, "text")) field = 4;
        if (!strcmp(name, "model")) field = 5;
    }
    if (field >= 0) {
        if (p->seen[field]) { stop(p, "Duplicate page field or history dump"); return; }
        for (const char **a = attrs; *a; a += 2)
            if (field == 4 && !strcmp(local(a[0]), "deleted")) {
                stop(p, "Suppressed text cannot be analyzed"); return;
            }
        p->seen[field] = 1; p->field = field; p->field_depth = p->depth;
    }
}
static void XMLCALL end(void *data, const char *tag) {
    Parser *p = data; const char *name = local(tag);
    if (p->field >= 0 && p->depth == p->field_depth) p->field = -1;
    if (p->page && p->depth == 3 && !strcmp(name, "revision")) p->revision = 0;
    if (p->depth == 2 && !strcmp(name, "page")) { finish_page(p); p->page = 0; }
    p->depth--;
}
static void XMLCALL characters(void *data, const char *text, int length) {
    Parser *p = data;
    if (p->field >= 0 && !append(&p->fields[p->field], text, (size_t)length))
        stop(p, "Page field exceeds 8 MiB or allocation failed");
}
static void XMLCALL doctype(void *data, const char *name, const char *sysid, const char *pubid, int internal) {
    (void)name; (void)sysid; (void)pubid; (void)internal;
    stop(data, "DTD/entity declarations are unsupported");
}
static int feed(Parser *p, const char *data, size_t size, int final) {
    p->expanded += size;
    if (p->expanded > EXPANDED_LIMIT || now() > p->deadline) {
        snprintf(p->error, sizeof(p->error), "Dump part exceeded 1 GiB expanded data or 5 minute limit"); return 0;
    }
    if (XML_Parse(p->xml, data, (int)size, final) == XML_STATUS_ERROR) {
        if (!p->error[0]) snprintf(p->error, sizeof(p->error), "Invalid XML at line %lu: %s",
            XML_GetCurrentLineNumber(p->xml), XML_ErrorString(XML_GetErrorCode(p->xml)));
        return 0;
    }
    return 1;
}
/* Streaming bzip2 decoder accepts concatenated streams and rejects truncation,
   trailing garbage and CRC failures. Reuses fixed buffers between streams. */
static int decompress(FILE *in, Parser *p, FILE *out) {
    char input[65536], output[65536]; bz_stream bz = {0};
    int rc = BZ2_bzDecompressInit(&bz, 0, 0), ok = 0;
    if (rc != BZ_OK) return 0;
    uint64_t total = 0; double deadline = now() + 300;
    for (;;) {
        if (!bz.avail_in) {
            bz.avail_in = (unsigned)fread(input, 1, sizeof(input), in); bz.next_in = input;
            if (!bz.avail_in) break; /* EOF before stream end is truncation. */
        }
        bz.next_out = output; bz.avail_out = sizeof(output);
        rc = BZ2_bzDecompress(&bz);
        size_t n = sizeof(output) - bz.avail_out; total += n;
        if (total > EXPANDED_LIMIT || now() > deadline) break;
        if (p && !feed(p, output, n, 0)) break;
        if (out && fwrite(output, 1, n, out) != n) break;
        if (rc == BZ_STREAM_END) {
            if (!bz.avail_in) {
                bz.avail_in = (unsigned)fread(input, 1, sizeof(input), in); bz.next_in = input;
                if (!bz.avail_in) { ok = !ferror(in); break; }
            }
            char *next = bz.next_in; unsigned available = bz.avail_in;
            BZ2_bzDecompressEnd(&bz); memset(&bz, 0, sizeof(bz));
            if (BZ2_bzDecompressInit(&bz, 0, 0) != BZ_OK) return 0;
            bz.next_in = next; bz.avail_in = available;
        } else if (rc != BZ_OK) break;
    }
    BZ2_bzDecompressEnd(&bz); return ok;
}
LEAN_EXPORT lean_obj_res wiki_normalize(b_lean_obj_arg input, b_lean_obj_arg directory,
    uint8_t compressed, uint8_t first, uint8_t last, uint32_t ns, uint8_t redirects,
    uint64_t shard_bytes, lean_obj_arg world) {
    (void)world;
    Parser p = {0}; p.directory = lean_string_cstr(directory); p.target = shard_bytes;
    p.namespace = ns; p.redirects = redirects; p.field = -1; p.deadline = now() + 300;
    p.xml = XML_ParserCreateNS(NULL, '|');
    if (!p.xml) return failure("Cannot allocate XML parser");
    XML_SetUserData(p.xml, &p); XML_SetElementHandler(p.xml, start, end);
    XML_SetCharacterDataHandler(p.xml, characters); XML_SetStartDoctypeDeclHandler(p.xml, doctype);
    FILE *in = fopen(lean_string_cstr(input), "rb"); int ok = in != NULL;
    if (ok && !first) ok = feed(&p, "<mediawiki>", 11, 0);
    if (ok && compressed) ok = decompress(in, &p, NULL);
    else if (ok) {
        char buffer[65536]; size_t n;
        while (ok && (n = fread(buffer, 1, sizeof(buffer), in))) ok = feed(&p, buffer, n, 0);
        if (ferror(in)) ok = 0;
    }
    if (ok && !last) ok = feed(&p, "</mediawiki>", 12, 0);
    if (ok) ok = feed(&p, "", 0, 1);
    if (in) fclose(in);
    if (p.out && fclose(p.out)) ok = 0;
    XML_ParserFree(p.xml);
    for (unsigned i = 0; i < 6; i++) free(p.fields[i].data);
    if (!ok) return failure(p.error[0] ? p.error : "Cannot read dump: corrupt/truncated bzip2, IO error or decompression limit");
    lean_object *counts = lean_mk_empty_array();
    for (unsigned i = 0; i < p.files; i++) counts = lean_array_push(counts, lean_uint64_to_nat(p.counts[i]));
    return lean_io_result_mk_ok(counts);
}
LEAN_EXPORT lean_obj_res wiki_decompress(b_lean_obj_arg input, b_lean_obj_arg output, lean_obj_arg world) {
    (void)world; FILE *in = fopen(lean_string_cstr(input), "rb");
    FILE *out = fopen(lean_string_cstr(output), "wb");
    int ok = in && out && decompress(in, NULL, out);
    if (in) fclose(in);
    if (out && fclose(out)) ok = 0;
    return ok ? lean_io_result_mk_ok(lean_box(0)) : failure("Cannot decompress index (corruption, IO or 1 GiB/5 minute limit)");
}

typedef struct { regex_t regex; locale_t locale; int compiled, ignore_case; char *literal; size_t length, *prefix; } Matcher;
static void release(void *data) {
    Matcher *m = data; if (m->compiled) regfree(&m->regex);
    if (m->locale) freelocale(m->locale);
    free(m->literal); free(m->prefix); free(m);
}
static void visit(void *data, b_lean_obj_arg f) { (void)data; (void)f; }
static lean_external_class *matcher_class;
static pthread_once_t once = PTHREAD_ONCE_INIT;
static void register_matcher(void) { matcher_class = lean_register_external_class(release, visit); }
static unsigned char lower(unsigned char c) { return c >= 'A' && c <= 'Z' ? (unsigned char)(c + 32) : c; }
LEAN_EXPORT lean_obj_res wiki_matcher(b_lean_obj_arg pattern, uint8_t regex, uint8_t ignore_case, lean_obj_arg world) {
    (void)world; pthread_once(&once, register_matcher);
    Matcher *m = calloc(1, sizeof(*m)); if (!m) return failure("Cannot allocate matcher");
    m->ignore_case = ignore_case;
    if (regex) {
        /* Thread-local locale: independent of the host environment and other
           cloud programs; never change the process-wide locale. */
        m->locale = newlocale(LC_ALL_MASK, "C", (locale_t)0);
        if (!m->locale) { free(m); return failure("Cannot create regex locale"); }
        locale_t previous = uselocale(m->locale);
        int rc = regcomp(&m->regex, lean_string_cstr(pattern), REG_EXTENDED | (ignore_case ? REG_ICASE : 0));
        if (rc) {
            char message[256]; regerror(rc, &m->regex, message, sizeof(message));
            uselocale(previous); release(m); return failure(message);
        }
        uselocale(previous);
        m->compiled = 1;
    } else {
        m->literal = strdup(lean_string_cstr(pattern)); m->length = strlen(lean_string_cstr(pattern));
        if (!m->literal) { free(m); return failure("Cannot allocate pattern"); }
        m->prefix = calloc(m->length + 1, sizeof(size_t));
        if (!m->prefix) { release(m); return failure("Cannot allocate matcher"); }
        if (ignore_case) for (size_t i = 0; i < m->length; i++) m->literal[i] = (char)lower((unsigned char)m->literal[i]);
        for (size_t i = 1, j = 0; i < m->length; i++) {
            while (j && m->literal[i] != m->literal[j]) j = m->prefix[j-1];
            if (m->literal[i] == m->literal[j]) j++;
            m->prefix[i] = j;
        }
    }
    return lean_io_result_mk_ok(lean_alloc_external(matcher_class, m));
}
LEAN_EXPORT lean_obj_res wiki_find(b_lean_obj_arg matcher, b_lean_obj_arg text, lean_obj_arg world) {
    (void)world; Matcher *m = lean_get_external_data(matcher);
    const char *s = lean_string_cstr(text); size_t length = lean_string_size(text) - 1;
    size_t offset = 0, size = 0; int found = 0;
    if (m->compiled) {
        regmatch_t match;
        locale_t previous = uselocale(m->locale);
        int rc = regexec(&m->regex, s, 1, &match, 0);
        uselocale(previous);
        if (rc != 0 && rc != REG_NOMATCH) return failure("Regex execution failed");
        if (!rc) { found = 1; offset = (size_t)match.rm_so; size = (size_t)(match.rm_eo - match.rm_so); }
    } else if (!m->length) { found = 1;
    } else if (m->length <= length) {
        /* KMP: linear in article length, including repetitive adversarial text. */
        for (size_t i = 0, j = 0; i < length; i++) {
            unsigned char c = m->ignore_case ? lower((unsigned char)s[i]) : (unsigned char)s[i];
            while (j && c != (unsigned char)m->literal[j]) j = m->prefix[j-1];
            if (c == (unsigned char)m->literal[j]) j++;
            if (j == m->length) { found = 1; offset = i + 1 - j; size = j; break; }
        }
    }
    if (!found) return lean_io_result_mk_ok(lean_box(0));
    lean_object *pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, lean_usize_to_nat(offset)); lean_ctor_set(pair, 1, lean_usize_to_nat(size));
    lean_object *some = lean_alloc_ctor(1, 1, 0); lean_ctor_set(some, 0, pair);
    return lean_io_result_mk_ok(some);
}
