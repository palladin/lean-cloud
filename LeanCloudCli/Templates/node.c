/* Container entry point: one durable RabbitMQ mailbox and one Lean actor.
 * Only serve-* commands start the node; registry/submission tools run directly.
 * PID 1 reaps descendants, restarts Lean without interrupting the broker, and
 * stops Lean before RabbitMQ. A broker failure exits for Docker to restart.
 */
#define _POSIX_C_SOURCE 200809L
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

static volatile sig_atomic_t stopping;
static void stop(int sig) { stopping = sig; }
static long seconds(void) {
    struct timespec t;
    if (clock_gettime(CLOCK_MONOTONIC, &t) != 0) { perror("clock_gettime"); exit(1); }
    return t.tv_sec;
}
static void tick(void) {
    struct timespec t = {0, 100000000};
    nanosleep(&t, NULL);
}
static void group_signal(pid_t pid, int sig) { if (pid > 0) kill(-pid, sig); }
static pid_t spawn(char *const argv[], int quiet, int actor) {
    pid_t pid = fork();
    if (pid == 0) {
        if (setsid() < 0) _exit(127);
        signal(SIGTERM, SIG_DFL); signal(SIGINT, SIG_DFL);
        if (quiet) {
            int fd = open("/dev/null", O_RDWR);
            if (fd < 0) _exit(127);
            dup2(fd, STDOUT_FILENO); dup2(fd, STDERR_FILENO); close(fd);
        }
        if (actor) {
            /* Docker's stdout pipe belongs to root. Give the unprivileged
             * actor a separate, already-open nonblocking description for its
             * best-effort trace writer, without changing ordinary stdout. */
            int fd = open("/proc/self/fd/1", O_WRONLY | O_NONBLOCK);
            if (fd >= 0) {
                char value[32]; snprintf(value, sizeof(value), "%d", fd);
                if (setenv("LEAN_CLOUD_TRACE_FD", value, 1) < 0) { close(fd); _exit(127); }
            }
        }
        execvp(argv[0], argv);
        perror(argv[0]); _exit(127);
    }
    if (pid < 0) perror("fork");
    return pid;
}
static int save_pid(const char *name, pid_t pid) {
    FILE *f = fopen(name, "w");
    if (!f) return -1;
    int ok = fprintf(f, "%ld\n", (long)pid) > 0;
    return fclose(f) == 0 && ok ? 0 : -1;
}
static int alive(const char *name) {
    FILE *f = fopen(name, "r");
    if (!f) return 0;
    long pid = 0;
    int ok = fscanf(f, "%ld", &pid) == 1 && pid > 1;
    fclose(f);
    return ok && kill((pid_t)pid, 0) == 0;
}
static void terminate(pid_t pid) {
    if (pid <= 0) return;
    group_signal(pid, SIGTERM);
    long deadline = seconds() + 8;
    while (waitpid(pid, NULL, WNOHANG) == 0 && seconds() < deadline) tick();
    /* Also stop descendants that outlived the group leader. */
    group_signal(pid, SIGKILL);
    while (waitpid(pid, NULL, 0) < 0 && errno == EINTR) {}
}

int main(int argc, char **argv) {
    if (argc == 2 && strcmp(argv[1], "health") == 0) {
        if (!alive("/run/cloud-node/app.pid") || !alive("/run/cloud-node/broker.pid")) return 1;
        execlp("gosu", "gosu", "rabbitmq", "rabbitmq-diagnostics", "-q", "check_running", (char *)NULL);
        return 1;
    }
    if (argc < 2) { fputs("cloud-node: expected an application command\n", stderr); return 2; }
    char **app = calloc((size_t)argc + 3, sizeof(char *));
    if (!app) return 1;
    app[0] = "gosu"; app[1] = "worker"; app[2] = "cloud-app";
    for (int i = 1; i < argc; ++i) app[i + 2] = argv[i];
    if (strcmp(argv[1], "serve-worker") && strcmp(argv[1], "serve-scheduler")) {
        execvp(app[0], app); perror("cloud-app"); return 127;
    }
    struct sigaction action = {0};
    action.sa_handler = stop; sigemptyset(&action.sa_mask);
    sigaction(SIGTERM, &action, NULL); sigaction(SIGINT, &action, NULL);
    if (mkdir("/run/cloud-node", 0755) < 0 && errno != EEXIST) { perror("mkdir"); return 1; }
    unlink("/run/cloud-node/app.pid"); unlink("/run/cloud-node/broker.pid");
    char *broker_args[] = {"docker-entrypoint.sh", "rabbitmq-server", NULL};
    char *probe_args[] = {"gosu", "rabbitmq", "rabbitmq-diagnostics", "-q", "check_port_connectivity", NULL};
    pid_t broker = spawn(broker_args, 0, 0), actor = -1, probe = -1;
    if (broker < 0) return 1;
    int ready = 0, failed = 0;
    long startup_deadline = seconds() + 120, next_probe = 0, probe_deadline = 0, next_actor = 0;
    while (!stopping && !failed) {
        int status;
        pid_t ended;
        while ((ended = waitpid(-1, &status, WNOHANG)) > 0) {
            if (ended == broker) {
                fputs("cloud-node: mailbox exited; restarting the node\n", stderr);
                group_signal(broker, SIGKILL); broker = -1; failed = 1;
            } else if (ended == actor) {
                group_signal(actor, SIGKILL); actor = -1;
                unlink("/run/cloud-node/app.pid");
                fprintf(stderr, "cloud-node: Lean actor exited (%d); restarting in 1s\n",
                    WIFEXITED(status) ? WEXITSTATUS(status) : 128 + WTERMSIG(status));
                next_actor = seconds() + 1;
            } else if (ended == probe) {
                group_signal(probe, SIGKILL); probe = -1;
                ready = WIFEXITED(status) && WEXITSTATUS(status) == 0;
                next_probe = seconds() + 2;
            }
        }
        if (stopping || failed) break;
        if (!ready) {
            if (seconds() >= startup_deadline) {
                fputs("cloud-node: mailbox startup timed out\n", stderr); failed = 1; break;
            }
            if (probe > 0 && seconds() >= probe_deadline) group_signal(probe, SIGKILL);
            if (probe < 0 && seconds() >= next_probe) {
                probe = spawn(probe_args, 1, 0); probe_deadline = seconds() + 5;
                if (probe < 0) failed = 1;
            }
        } else if (actor < 0 && seconds() >= next_actor) {
            actor = spawn(app, 0, 1);
            if (actor < 0 || save_pid("/run/cloud-node/broker.pid", broker) ||
                save_pid("/run/cloud-node/app.pid", actor)) failed = 1;
        }
        tick();
    }
    unlink("/run/cloud-node/app.pid"); unlink("/run/cloud-node/broker.pid");
    group_signal(probe, SIGKILL);
    terminate(probe); terminate(actor); terminate(broker);
    while (waitpid(-1, NULL, WNOHANG) > 0) {}
    free(app);
    return failed ? 1 : 0;
}
