/* Best-effort diagnostics use a separate nonblocking file description.
   A full log pipe drops an observation; it cannot stall a workflow. */
#include <lean/lean.h>
#include <fcntl.h>
#include <unistd.h>
#include <pthread.h>
#include <signal.h>
#include <errno.h>
#include <time.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <inttypes.h>
#ifdef __linux__
#include <sys/statvfs.h>

/* cgroup v2 counters for the current container; no Docker socket or privileges.
   The kernel defines cpu.stat in microseconds and io.stat in bytes:
   https://docs.kernel.org/admin-guide/cgroup-v2.html */
static FILE *counter_file(const char *group, const char *name) {
    char path[2048];
    int size = snprintf(path, sizeof(path), "/sys/fs/cgroup%s/%s", !strcmp(group, "/") ? "" : group, name);
    return size > 0 && (size_t)size < sizeof(path) ? fopen(path, "r") : NULL;
}
static int parent_group(char *group) {
    char *slash = strrchr(group, '/');
    if (!slash || !slash[1]) return 0;
    *slash = 0;
    return 1;
}
static int read_counter(const char *group, const char *name, uint64_t *value) {
    FILE *file = counter_file(group, name);
    if (!file) return 0;
    int ok = fscanf(file, "%" SCNu64, value) == 1;
    fclose(file);
    return ok;
}
static int memory_limit(const char *group, uint64_t *limit) {
    /* Parent limits can constrain the container even when its own limit is max. */
    char parent[1024]; snprintf(parent, sizeof(parent), "%s", group);
    int found = 0;
    do {
        uint64_t current;
        if (read_counter(parent, "memory.max", &current)) {
            if (!found || current < *limit) *limit = current;
            found = 1;
        }
    } while (parent_group(parent));
    return found;
}
static int keyed_counter(FILE *file, const char *key, uint64_t *value) {
    if (!file) return 0;
    char line[1024], name[128]; uint64_t number;
    int found = 0;
    while (fgets(line, sizeof(line), file)) {
        if (sscanf(line, "%127s %" SCNu64, name, &number) == 2 && !strcmp(name, key)) {
            *value = number; found = 1; break;
        }
    }
    fclose(file);
    return found;
}
static void json_counter(char *json, size_t capacity, const char *name, int ok, uint64_t value) {
    size_t used = strlen(json);
    if (ok) snprintf(json + used, capacity - used, ",\"%s\":%" PRIu64, name, value);
    else snprintf(json + used, capacity - used, ",\"%s\":null", name);
}
static void json_name(char *json, size_t capacity, const char *name, const char *value) {
    /* Names come from the deployment/OS, not trusted JSON. Bound their size and
       escape control characters so they cannot corrupt the whole sample. */
    if (!value || !*value || strlen(value) > 255) return;
    char escaped[6 * 255 + 1]; size_t used = 0;
    for (const unsigned char *p = (const unsigned char *)value; *p; p++) {
        if (*p < 32) used += (size_t)snprintf(escaped + used, sizeof(escaped) - used, "\\u%04x", *p);
        else {
            if (*p == '"' || *p == '\\') escaped[used++] = '\\';
            escaped[used++] = (char)*p;
        }
    }
    escaped[used] = 0;
    used = strlen(json);
    snprintf(json + used, capacity - used, ",\"%s\":\"%s\"", name, escaped);
}
static int cpu_capacity(const char *group, uint64_t *millis) {
    /* The kernel's affinity bitmap includes cpuset restrictions. Count its set
       bits without assuming that allowed CPU IDs form a contiguous range. */
    FILE *status = fopen("/proc/self/status", "r");
    char line[4096]; int found = 0;
    if (status) {
        while (fgets(line, sizeof(line), status)) {
            if (strncmp(line, "Cpus_allowed:", 13) || !strchr(line, '\n')) continue;
            uint64_t cores = 0;
            for (char *p = line + 13; *p; p++) {
                unsigned bits = (*p >= '0' && *p <= '9') ? (unsigned)(*p - '0') :
                    (*p >= 'a' && *p <= 'f') ? (unsigned)(*p - 'a' + 10) :
                    (*p >= 'A' && *p <= 'F') ? (unsigned)(*p - 'A' + 10) : 0;
                for (; bits; bits >>= 1) cores += bits & 1;
            }
            if (cores) { *millis = cores * 1000; found = 1; }
            break;
        }
        fclose(status);
    }
    /* A tighter parent quota also applies. Only ancestors visible in this
       cgroup namespace can be inspected; CPU shares/requests are not limits. */
    char parent[1024]; snprintf(parent, sizeof(parent), "%s", group);
    do {
        FILE *file = counter_file(parent, "cpu.max");
        if (file) {
            uint64_t quota, period;
            if (fscanf(file, "%" SCNu64 " %" SCNu64, &quota, &period) == 2 && period && quota <= UINT64_MAX / 1000) {
                uint64_t limit = quota * 1000 / period;
                if (!found || limit < *millis) *millis = limit;
                found = 1;
            }
            fclose(file);
        }
    } while (parent_group(parent));
    return found;
}
#endif

/* Unsupported/missing counters produce no sample or JSON null, never a false 0.
   Invoked at trace boundaries, independently of whether a console is connected. */
LEAN_EXPORT lean_obj_res lc_trace_resources(lean_obj_arg world) {
    (void)world;
    char json[4096] = "";
#ifdef __linux__
    char group[1024] = "", line[2048]; int found = 0;
    FILE *file = fopen("/proc/self/cgroup", "r");
    if (file) {
        while (fgets(line, sizeof(line), file)) {
            if (!strncmp(line, "0::", 3)) {
                size_t size = strcspn(line + 3, "\r\n");
                if (size < sizeof(group)) { memcpy(group, line + 3, size); group[size] = 0; found = 1; }
                break;
            }
        }
        fclose(file);
    }
    struct timespec now;
    if (found && !strstr(group, "..") && !clock_gettime(CLOCK_MONOTONIC, &now)) {
        snprintf(json, sizeof(json), "{\"timeNs\":%" PRIu64,
            (uint64_t)now.tv_sec * 1000000000 + (uint64_t)now.tv_nsec);
        json_name(json, sizeof(json), "nodeName", getenv("CLOUD_NODE_NAME"));
        char hostname[256] = {0};
        if (gethostname(hostname, sizeof(hostname) - 1) == 0)
            json_name(json, sizeof(json), "hostname", hostname);
        long cores = sysconf(_SC_NPROCESSORS_ONLN);
        json_counter(json, sizeof(json), "cpuCores", cores > 0, cores > 0 ? (uint64_t)cores : 0);
        uint64_t value = 0;
        int capacity_ok = cpu_capacity(group, &value);
        json_counter(json, sizeof(json), "cpuCapacityMillis", capacity_ok, value);
        int ok = keyed_counter(counter_file(group, "cpu.stat"), "usage_usec", &value);
        json_counter(json, sizeof(json), "cpuNs", ok, value * 1000);
        ok = read_counter(group, "memory.current", &value);
        json_counter(json, sizeof(json), "memory", ok, value);
        uint64_t limit = 0, physical = 0;
        int limited = memory_limit(group, &limit);
        int have_physical = keyed_counter(fopen("/proc/meminfo", "r"), "MemTotal:", &physical);
        physical *= 1024;
        json_counter(json, sizeof(json), "memoryCapacity", have_physical, physical);
        if (have_physical && (!limited || limit > physical)) { limit = physical; limited = 1; }
        json_counter(json, sizeof(json), "memoryLimit", limited, limit);

        uint64_t rx = 0, tx = 0;
        file = fopen("/proc/net/dev", "r"); ok = file != NULL;
        if (file) {
            while (fgets(line, sizeof(line), file)) {
                char *colon = strchr(line, ':');
                if (!colon) continue;
                *colon = 0;
                char *name = line; while (*name == ' ' || *name == '\t') name++;
                if (!strcmp(name, "lo")) continue;
                char *cursor = colon + 1, *end; uint64_t fields[16]; int count = 0;
                for (; count < 16; count++) {
                    fields[count] = strtoull(cursor, &end, 10);
                    if (cursor == end) break;
                    cursor = end;
                }
                if (count == 16) { rx += fields[0]; tx += fields[8]; }
                else ok = 0;
            }
            fclose(file);
        }
        json_counter(json, sizeof(json), "rx", ok, rx);
        json_counter(json, sizeof(json), "tx", ok, tx);

        uint64_t read_bytes = 0, write_bytes = 0;
        file = counter_file(group, "io.stat"); ok = file != NULL;
        if (file) {
            while (fgets(line, sizeof(line), file)) {
                char *r = strstr(line, "rbytes="), *w = strstr(line, "wbytes=");
                if (r && w) { read_bytes += strtoull(r + 7, NULL, 10); write_bytes += strtoull(w + 7, NULL, 10); }
                else ok = 0;
            }
            fclose(file);
        }
        json_counter(json, sizeof(json), "readBytes", ok, read_bytes);
        json_counter(json, sizeof(json), "writeBytes", ok, write_bytes);
        struct statvfs disk;
        ok = statvfs("/", &disk) == 0;
        json_counter(json, sizeof(json), "diskUsed", ok, ok ? (uint64_t)(disk.f_blocks - disk.f_bfree) * disk.f_frsize : 0);
        json_counter(json, sizeof(json), "diskCapacity", ok, ok ? (uint64_t)disk.f_blocks * disk.f_frsize : 0);
        size_t used = strlen(json); snprintf(json + used, sizeof(json) - used, "}");
    }
#endif
    return lean_io_result_mk_ok(lean_mk_string(json));
}

static int output = -1;
static pthread_once_t once = PTHREAD_ONCE_INIT;
static void open_output(void) {
    /* Combined nodes open this description before dropping privileges. Unlike
       dup(stdout), it does not set ordinary Lean logging nonblocking. */
    const char *inherited = getenv("LEAN_CLOUD_TRACE_FD");
    if (inherited && *inherited) {
        char *end;
        long fd = strtol(inherited, &end, 10);
        if (!*end && fd >= 3 && fd <= 65535) {
            int flags = fcntl((int)fd, F_GETFL);
            if (flags >= 0 && (flags & O_NONBLOCK) && (flags & O_ACCMODE) == O_WRONLY) {
                output = fcntl((int)fd, F_DUPFD_CLOEXEC, 3);
                if (output >= 0) { close((int)fd); unsetenv("LEAN_CLOUD_TRACE_FD"); return; }
            }
        }
    }
#ifdef __linux__
    output = open("/proc/self/fd/1", O_WRONLY | O_NONBLOCK | O_CLOEXEC);
#else
    output = open("/dev/fd/1", O_WRONLY | O_NONBLOCK | O_CLOEXEC);
#endif
}
LEAN_EXPORT lean_obj_res lc_trace_emit(b_lean_obj_arg text, lean_obj_arg world) {
    (void)world;
    pthread_once(&once, open_output);
    size_t size = lean_string_size(text) - 1;
    /* Fits PIPE_BUF, so a pipe write is atomic or dropped, never interleaved. */
    if (output >= 0 && size <= 2048) {
        sigset_t block, old, pending;
        sigemptyset(&block); sigaddset(&block, SIGPIPE);
        pthread_sigmask(SIG_BLOCK, &block, &old);
        sigpending(&pending);
        int already_pending = sigismember(&pending, SIGPIPE);
        ssize_t result = write(output, lean_string_cstr(text), size);
        if (result < 0 && errno == EPIPE && !already_pending) {
            struct timespec zero = {0};
#ifdef __linux__
            sigtimedwait(&block, NULL, &zero);
#else
            (void)zero;
            sigpending(&pending);
            if (sigismember(&pending, SIGPIPE)) {
                int signal_number;
                sigwait(&block, &signal_number);
            }
#endif
        }
        pthread_sigmask(SIG_SETMASK, &old, NULL);
    }
    return lean_io_result_mk_ok(lean_box(0));
}
