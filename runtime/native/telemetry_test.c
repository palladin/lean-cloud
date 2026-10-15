/* Test the production readers against kernel-format files without privileges,
   cgroup mutations, or a dependency on the test machine's resource limits. */
#include <assert.h>
#include <stdio.h>
#include <string.h>

static struct { const char *path, *contents; } files[16];
static size_t file_count;

static size_t add_file(const char *path, const char *contents) {
    assert(file_count < sizeof(files) / sizeof(files[0]));
    files[file_count].path = path;
    files[file_count].contents = contents;
    return file_count++;
}

static FILE *fixture_fopen(const char *path, const char *mode) {
    assert(!strcmp(mode, "r"));
    for (size_t i = 0; i < file_count; i++) {
        if (strcmp(files[i].path, path)) continue;
        FILE *file = tmpfile();
        assert(file);
        assert(fputs(files[i].contents, file) >= 0);
        rewind(file);
        return file;
    }
    return NULL;
}

#define fopen fixture_fopen
#include "telemetry.c"
#undef fopen

int main(void) {
    uint64_t value = 999;
    assert(!cpu_capacity("/pod/worker", &value));
    assert(!memory_limit("/pod/worker", &value));

    /* Noncontiguous affinity across multiple bitmap words; unlimited quota. */
    size_t affinity = add_file("/proc/self/status", "Name:\tcloud-app\nCpus_allowed:\t00000001,00000005\n");
    size_t quota = add_file("/sys/fs/cgroup/pod/worker/cpu.max", "max 100000\n");
    assert(cpu_capacity("/pod/worker", &value) && value == 3000);
    size_t parent_quota = add_file("/sys/fs/cgroup/pod/cpu.max", "150000 100000\n");
    assert(cpu_capacity("/pod/worker", &value) && value == 1500);
    files[quota].contents = "50000 100000\n";
    assert(cpu_capacity("/pod/worker", &value) && value == 500);
    files[quota].contents = "50000 0\n";
    assert(cpu_capacity("/pod/worker", &value) && value == 1500);
    files[quota].contents = "18446744073709551615 100000\n";
    assert(cpu_capacity("/pod/worker", &value) && value == 1500);

    /* A wider quota never overrides affinity. A missing affinity file is not zero. */
    files[quota].contents = "400000 100000\n";
    files[parent_quota].contents = "max 100000\n";
    assert(cpu_capacity("/pod/worker", &value) && value == 3000);
    files[affinity].path = "/missing-status";
    assert(cpu_capacity("/pod/worker", &value) && value == 4000);

    /* Effective memory is the tightest visible ancestor, including zero. */
    size_t memory = add_file("/sys/fs/cgroup/pod/worker/memory.max", "max\n");
    assert(!memory_limit("/pod/worker", &value));
    add_file("/sys/fs/cgroup/pod/memory.max", "268435456\n");
    assert(memory_limit("/pod/worker", &value) && value == 268435456);
    files[memory].contents = "134217728\n";
    assert(memory_limit("/pod/worker", &value) && value == 134217728);
    files[memory].contents = "536870912\n";
    assert(memory_limit("/pod/worker", &value) && value == 268435456);
    add_file("/sys/fs/cgroup/memory.max", "0\n");
    assert(memory_limit("/pod/worker", &value) && value == 0);
    assert(memory_limit("/", &value) && value == 0);
    assert(memory_limit("", &value) && value == 0);

    /* Deployment names are JSON data, including quotes and control characters. */
    char json[4096] = "{";
    json_name(json, sizeof(json), "nodeName", "node\"\\\n\t");
    assert(!strcmp(json, "{,\"nodeName\":\"node\\\"\\\\\\u000a\\u0009\""));
    char name[257]; memset(name, 1, sizeof(name)); name[255] = 0;
    json[0] = '{'; json[1] = 0;
    json_name(json, sizeof(json), "nodeName", name);
    assert(strlen(json) == 1 + strlen(",\"nodeName\":\"\"") + 255 * 6);
    name[255] = 1; name[256] = 0;
    json[0] = '{'; json[1] = 0;
    json_name(json, sizeof(json), "nodeName", name);
    assert(!strcmp(json, "{"));

    puts("Native telemetry: affinity, inherited CPU/memory limits, missing counters and JSON names passed.");
    return 0;
}
