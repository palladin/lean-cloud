# Terminal console

Start the console from the lean-cloud checkout (Docker must be running):

```sh
lake exe lean_cloud
```

Create and select your application:

```text
cloud> init my-app
```

Edit `my-app/Main.lean` with your workflow, then return to the same console:

```text
cloud> deploy
cloud> run my-app --id first
cloud> watch first
cloud> result first
```

`init` generates a complete Lean application and selects it in the console.
The included parallel example returns `55`. `deploy` builds the executable in
Docker and by default starts five containers: the scheduler, three workers, and global blobs. Each node runs its HTTP API, embedded SQLite inbox, and actor in one Lean process.
The CLI generates Docker and service configuration under `.lean-cloud/`; users
only maintain their Lean code and package metadata.

Use `deployments` to list known applications, including deployments taken down,
and `use my-app` to select one. The selection is remembered across console sessions.
Use `open DIRECTORY` to select another application directory.
Paths such as `--input numbers.json` are relative to the selected application's
directory. You can also run the built `lean_cloud` executable from that directory.
For an existing Lean package that already uses the application runtime, use
`deploy EXECUTABLE` once to select its Lake executable; later deployments use
plain `deploy`.

Creating an app from this SDK checkout automatically uses the local SDK source,
including uncommitted changes. Elsewhere, `init` uses the published Git dependency.
`init my-app --sdk /path/to/lean-cloud` explicitly selects a local checkout;
the local override file is excluded from Git. Deployment resolves that SDK inside
Docker without modifying the local Lake dependency manifest.

On an interactive terminal, the prompt stays at the bottom with completion
suggestions directly beneath it. Command output appears in the area above.

Type `help` to list commands. Use `help COMMAND`, `COMMAND --help`, or
`COMMAND -h` for usage, options, and examples:

```text
cloud> help deploy
cloud> run --help
cloud> top -h
```

Tab completes command names after `help` and help flags after commands. Help
stays in the prompt's output area and does not execute the command. One-shot
help, such as `lake exe lean_cloud deploy --help`, works without Docker or a
configured application.

The console uses a shared htop-style theme: cyan table headers, blue selections,
green running/completed states, yellow pending/paused states, and red failures or
cancellations. The prompt, completion suggestions, deployment diagnostics, process
tables, and live monitor use the same renderer. Styles survive wrapping and
scrolling; text from programs and external services cannot supply terminal escapes.
Set `NO_COLOR=1` to disable colors. Piped output and `--once` views remain plain text.

- **Tab / Shift-Tab:** complete and cycle through suggestions for commands,
  deployed programs, run IDs, flags, actor names and `--input` file paths.
- **↑ / ↓:** recall command history and return to the draft you were editing.
- **← / →, Home / End, Backspace / Delete:** edit the command.
- **PgUp / PgDn:** scroll the output. The session retains the latest 2,000 lines.
- **Ctrl-U:** clear input; **Ctrl-K:** delete to the end.
- **Ctrl-C:** clear input, or exit when empty. **Ctrl-D:** exit when empty.

The layout follows terminal resizing. Bracketed multiline paste inserts a single
command for review; it does not submit on pasted newlines. `watch RUN` and `top` temporarily
take over the screen, then return to the anchored prompt when you press `q`.
Piped input and one-shot commands keep plain text output.

`deploy` and `up` show short, colored stage messages by default. Add `-v` or
`--verbose` to stream the full Docker build/startup output:

```text
cloud> deploy --verbose
cloud> deploy my_app -v
cloud> up -v
```

Both modes save the complete decoded plain-text output under
`.lean-cloud/PROJECT/logs/`, with a separate file for each build or service-start
attempt. Previous logs are kept. A failed command in quiet mode shows the last
20 output lines (long lines are clipped on screen), and errors include the log
path. Interrupted commands keep whatever output has already been captured.

While a command runs, the prompt shows `running>`; you can scroll with PgUp/PgDn, resize the terminal, and edit a
draft command with completion. Press Enter after the current command finishes
to submit that draft. Enter during execution does not queue or launch a command.

Ctrl-C interrupts the local build/startup command and releases its process and
deployment lock. Services already started remain running; use `status` to inspect
them. Docker may retain build cache and other partial work. This is not a workflow
cancellation command. One-shot commands use the same quiet/verbose behavior
and handle SIGINT/SIGTERM with process cleanup.

To try the bundled examples instead, open the lean-cloud repository. The shell and one-shot commands use the same implementation:

```text
cloud> deploy
cloud> programs
cloud> run sum-squares --id squares-1
cloud> run log-summary --id logs-1
cloud> ps
cloud> inspect logs-1
cloud> watch logs-1
cloud> result squares-1
cloud> result logs-1
cloud> top --once
cloud> quit
```

The example results are `55` and `files=16, errors=24`. By default, `deploy` starts one
scheduler, three persistent workers, and global blob storage: five long-lived
containers. Each scheduler/worker container includes its own in-process HTTP server and SQLite inbox. Every compute node contains the same
application executable and complete registered-program registry.

`run PROGRAM` submits a logical cloud process to this existing pool. It does
not create containers. The scheduler assigns work from different runs to free
workers, rotating between runnable runs. A worker loads the run's immutable
entry point and input, selects the registered program, and executes an assignment
with the existing replay interpreter. Results remain isolated by run ID.
After completing an assignment, the worker asks for more work; nodes remain
running even when every workflow has finished. Closing the console leaves the
pool running. `ps` lists workflows; `top` shows the deployed compute nodes,
including idle nodes. `status` includes blob storage health.

Use `down` to stop and remove the deployment's containers while preserving blobs,
mailboxes, scheduler state, images, and the local catalog. `up` starts the saved
image without rebuilding and automatically recovers active runs. Paused runs
remain paused. It checks that durable volumes still exist before starting.
Use `deploy` when application code changes. Changing the image requires completing
or killing unfinished runs first: replay must use the same application code.
Redeploying after `down` starts the retained services before checking saved
results. Missing durable volumes are reported instead of silently recreated.

To remove a deployment completely, select it and run `clean`:

```text
cloud> use my-app
cloud> clean
```

`clean` permanently deletes that deployment's containers, networks, storage volumes
(including retired workers), application image tags, local history, generated files,
and catalog entry. This includes workflows, results, replay records, and locally
hosted blobs. Your Lean project, shared Docker images/build cache, and external
storage services remain. It also works after `down` or an incomplete deployment.
If cleanup fails, run `clean` again to finish; then `deploy` creates a fresh deployment.
Saved RabbitMQ deployments require this reset before deploying the HTTP/SQLite
runtime. `deploy` reports the required commands and preserves the old data until
you explicitly run `clean`.

Use `remove RUN` to delete one finished, failed, or killed workflow while the
deployment keeps running:

```text
cloud> remove example-1
```

The scheduler retires the run ID, then a worker deletes its replay records and
result. The CLI removes the local run entry only after that succeeds. The ID
stays reserved, so delayed submissions cannot recreate the run. Active or paused
runs must finish or be killed first; all old attempts must have stopped.
Cleanup needs an available worker. If interrupted, repeat `remove RUN`.
If a timed-out blob request commits late, repeating removal reclaims its remaining
records; the retired ID cannot become a runnable workflow again.
Named blobs and user blob objects are preserved because other runs may share them.

## Backup and restore

Back up a stopped deployment to a new directory outside its `.lean-cloud/PROJECT`
directory. The parent directory must already exist:

```text
cloud> down
cloud> backup /backups/my-app-01
cloud> up
```

The backup includes exact application and blob-service images, scheduler and
inbox volumes (including retired workers), the bundled blob volume, configuration,
run inputs, and final watch snapshots. It includes credentials; keep it private.
It does not back up your Lean source checkout or an external blob service.
`down` must have removed the containers before backup, including stopped ones
that could otherwise restart. The blob image ID is saved at service startup.
For an older deployment without that ID, run `up`, then `down` once before backup.

To recover into fresh storage, select the destination project directory and run:

```text
cloud> restore /backups/my-app-01
cloud> up
```

Restore selects the deployment name saved in the backup, verifies archive
checksums, imports the images and volumes, and leaves everything stopped.
The destination must have no deployment files, containers, or volumes under that
name, including retired-worker volumes. The saved images need a compatible Docker platform. Application source is
not needed for `up`; keep it separately for future development and `deploy`.
Active workflows recover from their records, paused workflows stay paused, and
completed results remain available. Removed run IDs stay reserved.

An interrupted backup has no completion manifest and cannot be restored. An
interrupted restore cannot start; use `clean` on that incomplete destination,
then repeat `restore`. A backup is a point-in-time copy of durable workflow data;
restoring it does not roll back external actions previously performed by user IO.

## Elastic worker capacity

```text
cloud> deploy --workers 2
cloud> run log-summary --id logs-1
cloud> scale 6
cloud> scale 2
cloud> scale 0
```

`deploy --workers N` chooses the initial count (default three). `scale N` changes
capacity on the running deployment, using the same image and scheduler. Each added
worker starts with its own SQLite inbox. Scaling does not rebuild the image or
restart retained nodes. A pool of N workers uses N + 2 containers, including the
scheduler and blob storage.

On scale-down, the scheduler stops giving retiring workers new assignments. They
finish their current assignments and confirm drainage before their containers stop.
An unresponsive live worker is never forcibly removed by scaling. After one minute,
the command reports any workers still draining; retry `scale N` to finish removal.
A crashed, stopped worker's outstanding attempt is fenced and becomes pending.

`scale 0` drains all workers while preserving the scheduler, blobs, and pending
workflows. Scale above zero to resume processing. This controls capacity explicitly;
there is no CPU- or backlog-driven autoscaler yet.

The count is saved in the deployment and, for generated applications, in
`lean-cloud.json` as `"workers": N`. `up` and subsequent deployments reuse it.
Mailbox volumes and replay traces are retained after scale-down; growing the pool
reuses stable worker names and their volumes. Repeating a scale command is safe,
including after an interrupted command. Use `status` or `top` to inspect
the resulting pool.

## Pause and kill a run

```text
cloud> pause logs-1
cloud> ps
cloud> resume logs-1
cloud> kill logs-1
cloud> result logs-1
```

`pause RUN` tells the scheduler to stop assigning work for that run and revoke
its current attempts. Workers check assignment validity at replay-record
boundaries. An IO action already executing can finish before the worker notices
revocation. The shared containers and other runs keep running. `resume RUN`
reactivates the run with fresh attempts and reconstructs execution from its
immutable records; it does not restore an in-memory continuation.

`kill RUN` durably revokes the run. A worker then publishes its terminal
cancellation record; with zero workers, publication waits for a worker to become
available. A normal result that won the atomic creation race is preserved.
A killed run cannot resume or reuse its ID. Killing does not undo external
actions or delete records. `Cloud.exec` can execute again if interruption occurs
before its result is recorded, so external actions must tolerate retries.

The scheduler alone writes its SQLite state through lean-linq. It saves control
changes before confirming replies. The console also saves pending control intent:
if `ps` shows `pausing` or `killing`, retry that command. A pending kill blocks
resume. Process controls need the deployment scheduler; use `up` if it is down.
The console sends validation, submission, control, and result requests to the
scheduler's HTTP API. Docker is used for deployment, container metrics and logs.

Use a JSON file for other input:

```sh
lake exe lean_cloud run sum-squares --input numbers.json --id squares-2
lake exe lean_cloud inspect squares-2
lake exe lean_cloud watch squares-2 --once
```

`numbers.json` contains an array, for example `[2, 3, 4]`. The application validates
input with its registered codec before the console creates a launch manifest.
Omitting `--input` uses the program's registered sample input, if available.
Shell arguments support single/double quotes and escapes; they are never evaluated
as shell code. `logs RUN [worker1|worker2|worker3|scheduler]` prints recent structured events for that run from the selected shared node.

## Deployment commands

| Command | Purpose |
| --- | --- |
| `deployments` | List registered deployments, their directories, and observed service state. |
| `use NAME` | Select a registered deployment and remember it for later sessions. |
| `status` | Show its image, program/run counts, service health, and actor counts. |
| `top [--once]` | Live worker and scheduler resource graphs across the selected deployment. |
| `up` | Restart services and the node pool without rebuilding the application. |
| `doctor` | Check configuration, Docker/Compose, retained images, volumes, and container health. |
| `remove RUN` | Delete a terminal run's records and local entry; preserve shared user blobs. |
| `backup DIRECTORY` | Snapshot a stopped deployment, including its images and retained volumes. |
| `restore DIRECTORY` | Import a backup into fresh storage; start it separately with `up`. |

`status` counts locally recorded runs; use `ps` for workflow completion status.
`ps` distinguishes active execution, pending assignment, zero worker capacity,
stop acknowledgements, and terminal-result publication when the runtime provides
these diagnostics. `inspect RUN` includes pending/running/replied assignment
counts and the workers whose stop acknowledgement is still needed. It also shows
the last observed local retry for a current attempt, if available; missing or
dropped telemetry is not evidence that storage is healthy or that a worker stopped.
An unavailable Docker daemon is reported as unavailable, not as a stopped deployment.
`doctor` is read-only and returns a nonzero exit code if required checks fail,
including stopped services. It does not test runtime credentials or execute a workflow.

The deployment index lives at `$XDG_STATE_HOME/lean-cloud/deployments.json`, or
`$HOME/.local/state/lean-cloud/deployments.json` by default. `LEAN_CLOUD_HOME`
overrides the directory and must be an absolute path. Registration and selection
use a file lock and atomic replacement. Application directories retain their own
`.lean-cloud/PROJECT/` run catalogs. `init`, `open`, and `deploy` register and select
an application; an application with no completed deployment is shown as `not deployed`.
A Docker project name cannot belong to two different directories in the index.

`deployments` also imports older deployments found under the selected application's
`.lean-cloud/` directory. For older deployments elsewhere, first `open DIRECTORY`.
The CLI does not scan your entire filesystem. The remembered selection overrides
the shell's current directory; `open` selects a different directory explicitly,
and `LEAN_CLOUD_PROJECT` overrides the remembered selection at startup.

Isolated test deployments keep a `catalog-owner.json` marker with their catalog
directory. Discovery and listing respect that ownership, so retained test artifacts
do not appear in the ordinary deployment list.

This index targets the current Docker context. It does not configure Docker contexts
or manage remote deployments. Keep the same Docker context when stopping or resuming
an existing deployment.

## Effects and handlers

The entire console is a `lean-eff` program:

```lean
abbrev Cli := ExceptT String (Eff [Host])

def application (args : List String) : Cli UInt32
def dispatch (ctx : Context) (args : List String) : Cli (Context × Bool)
```

[Effects.lean](../LeanCloudCli/Effects.lean) defines typed requests for processes,
files, terminal input/output, time, environment and locks. Deployment, launch,
inspection, the REPL and the live-view loop compose those requests. JSON decoding,
Docker arguments, command decisions and rendering stay in the CLI logic.

Streaming uses typed `startProcess`, `pollProcess`, and `closeProcess` requests.
The IO handler owns the native process handles; C performs POSIX spawning,
bounded pipe reads, polling and process-group cleanup. Lean handles incremental
UTF-8 decoding, output sanitization, terminal input and command finalizers.
Machine-readable commands such as registry discovery keep their captured output.

`Cli.runWith` takes a handler for these requests. The
[IO handler](../LeanCloudCli/IO.lean) executes them on the host;
[the test handler](../LeanCloudTests/ConsoleModel.lean) uses pure state with
scripted process responses, files, keys and time. Requests cannot embed arbitrary
IO actions. The executable's `main` only runs `application` with the IO handler.

Host errors are returned to the effect program, so `catch` and `finally` have the
same behavior in both handlers. Lock release and terminal restoration are CLI
effects too. The IO handler also releases any remaining owned resources when it
exits. As with IO, failure of a finalizer takes precedence over an earlier error.

## Registering programs

`CloudProgram Input Output` packages a name, version, typed entry point, codecs,
and optional example input/source metadata. See
[Programs.lean](../runtime/LeanCloudRuntime/Programs.lean) for both examples.

```lean
def myProgram : CloudProgram (Array Nat) Nat := {
  name := "sum-squares"
  version := "v1"
  run := workflow
  sampleInput := some #[1, 2, 3, 4, 5]
}

def main (args : List String) : IO UInt32 :=
  Application.main ⟨#[myProgram.register]⟩ args
```

`Application.main` supplies worker and scheduler startup and the CLI protocol.
It uses typed Eff requests with an IO handler. Your application only supplies the
registry; it does not implement command dispatch or connection setup.

The runtime application exposes `programs`, `validate`, `submit-entry`, `serve-worker`,
`serve-scheduler`, `pause`, `resume`, `status`, `outcome`, `result`, and `cancel`; the console discovers that
registry from the built image. Register additional programs in the application and redeploy. There
is no closure serialization or runtime compilation of submitted source.

A typed client can also call `program.submit config id input`, receiving a
`CloudProcess Output` with `poll` and `await`. This API persists the definition and publishes a confirmed registration to the
deployment scheduler. Existing workers execute it; no containers are created.

Every run records its image ID, and deployment retains a versioned image tag.
Complete or kill unfinished runs before deploying a changed image. Changing
program semantics or codecs also requires a new registered version.

## Run catalog and recovery

The selected Docker project defaults to the application name in `lean-cloud.json`,
or `lean-cloud-console` for the SDK examples. To use an isolated
local environment, set `LEAN_CLOUD_PROJECT` before starting the console:

```sh
LEAN_CLOUD_PROJECT=my-experiment lake exe lean_cloud
```

The console retains launch manifests, inputs, bundled source, and configuration in
`.lean-cloud/PROJECT/`, which is ignored by Git and Docker builds. This is a local
launch catalog for this checkout. Scheduler state and immutable blob results are
the authority for progress and completion; the catalog is not a shared execution
database. `ps` queries those services and reports unavailable state explicitly.

`resume RUN` repairs an interrupted launch. Submission is idempotent, existing
the deployment image must match the saved run image, and completed runs are not
re-executed. A per-run launch lock prevents two consoles from changing the same
run concurrently. Preserve the local catalog, inbox volumes, scheduler volume,
blob volume, and application images for recovery.

The console currently targets local Docker deployments with a configurable, elastic worker pool. It does not provision remote hosts or cloud accounts.

## Live view

Use `top` for worker and scheduler graphs across all runs in the selected
deployment. No run ID is needed:

```text
cloud> top
```

Each node gets a panel with CPU, memory, filesystem usage, network RX/TX, and
disk read/write rates. Panels resize with the terminal. Use PgUp/PgDn or the
left/right arrows to change pages, and `q` to return to the console. Running
actors appear first; stopped actors remain visible with their status.
Each node includes its mailbox service. `status` also lists blob storage health.

`top --once` (or piped `top`) prints a plain-text snapshot of every page. Rates
need two samples, so that first snapshot shows `—` for network and I/O rates.

`watch RUN` shows a live branch tree, source code, and worker graphs.
When the run completes, it freezes the last view. Completed, paused, failed, and
killed runs can be opened again; there is no event list or execution timeline.

`ps` shows start and finish timestamps in UTC and elapsed wall time. The tree's
**ELAPSED** column shows the span of each branch and parallel group. Timing starts
when the scheduler registers the run, branch, or group; it includes waiting,
pauses, and retries. A parallel group's clock stops when all children complete;
the parent branch continues through its remaining code. Completion, failure, or
kill freezes unfinished clocks. These summaries are saved with scheduler state
and survive restarts. Older runs without timings show `—`. An unavailable
scheduler leaves the last saved observation fixed.

Select a **parallel group** to see all workers together, each with its current
branch, code position, and resource graphs. Idle workers are labeled explicitly.
Select an **individual branch** to see only the worker currently assigned to it;
an old or revoked attempt is never shown as executing. A completed run shows the
last observed worker and frozen statistics instead of current container activity.

- **↑ / ↓:** select a branch or parallel group.
- **← / →:** collapse or expand groups; move to the parent or first child.
- **PgUp / PgDn:** page through worker cards when the terminal cannot fit them all.
- **j / k:** scroll source; **a:** follow the selected branch's source line.
- **q:** return to the prompt.

The branch tree sits beside the code; narrow terminals stack them. `>` marks the
latest observed source line. Pending branches may show the parent parallel call.
A noninteractive terminal or `--once` prints one frame without control sequences.
Watching never submits, resumes, or re-executes a workflow.

The console reduces runtime observations to one latest snapshot in `watch.json`:
branch states, source positions, and a bounded window for worker meters. It does
not accumulate execution history. Old `trace.json` caches are compacted and removed
on first use. `down` and image replacement save the last view before removing
containers. If the deployment is unavailable, watch labels the saved view.
Missing source or resource observations remain unavailable; Docker log rotation or
dropped diagnostics can leave gaps. Ordinary pure code and lines inside an IO body
are not individually instrumented.

`cloud { ... }` captures source spans automatically. `program.register` bundles
the exact source files and site map from the build, including imported workflow
modules. Workers report the site on each replay node; repeated operation labels
and calls from different files remain distinct. Helper effects inherit the call
site unless an inner cloud block supplies its own annotation. No manual labels
or source-marker tables are required.

Source sites identify code, while replay locations identify dynamic occurrences
(such as different loop iterations or parallel branches). Source metadata never
changes replay keys, requests, fuel, or scheduling. Unknown sites and legacy events
still show their location/activity without a guessed source line. No input values,
blob contents, or local variables are logged.

Workers emit events through a best-effort nonblocking log channel. A full channel
may drop events, and Docker rotates the logs. These observations never determine
assignments, commit results, or acknowledge workflow messages. The event format
includes a run ID, worker incarnation, sequence number, attempt, location, and activity;
sequence numbers are local to each incarnation, not a global execution order.

While following an active run, resource graphs use live Docker container statistics.
For the last view of a completed, paused, or killed run, they use
resource counters attached to the worker's trace events. Collection happens in the
runtime even when no console is connected. Rebuild with `deploy` once to enable it
for future runs; already missing samples cannot be recovered.

The Linux container runtime samples cgroup v2 CPU, memory, and I/O counters,
network-interface counters, and root-filesystem usage at trace boundaries.
CPU and transfer rates use adjacent samples from the same process incarnation;
they are unavailable until two usable samples exist. Sampling is event-based,
so a long computation need not produce intermediate samples. These are container-wide measurements, including
the HTTP service, SQLite, and other workflows sharing that worker. Unsupported
counters remain missing.
The [kernel's cgroup documentation](https://docs.kernel.org/admin-guide/cgroup-v2.html)
defines the CPU, memory, and I/O counters.

Worker panels display:

- CPU utilization and memory usage/limit;
- network receive/send rates;
- block-device read/write rates;
- filesystem used/capacity where the container provides `df`.

CPU, memory, and filesystem usage have text meters. Their fill is green below
70%, yellow from 70%, and red from 90%. A CPU meter represents one core; usage
above 100% keeps its full numeric value and adds `+` to the meter. Memory and
filesystem meters use their reported capacity. Use `top --once` for a text
snapshot and `status` for the health of all deployment services.

Network receive/send and disk read/write rates have distinct colored histories.
Graphs use `_` for measured zero and `·` for an unavailable rate; the first counter
sample has no rate yet. CPU and memory histories appear when the panel is wide
enough, scaled to one core and the reported memory limit respectively.

Node statistics cover the Lean process, including HTTP and SQLite. CPU can exceed 100% on
multiple cores. Filesystem capacity can be shared between containers; it is not
space attributed exclusively to the selected container. Missing samples are not
zero utilization. Rate series restart when a container restarts or counters reset.
Graphs display up to 30 recent samples from one incarnation. The final meter
window survives console restart and deployment shutdown; it has no history cursor.
Rate graphs scale independently.

## Validation

`lake test` includes shell parsing, input identifiers, source-map ambiguity,
terminal escape sanitization, metric units, counter resets, bounded meter windows,
latest source markers, snapshot compaction, stable branch selection during refresh,
and navigation at several terminal widths. Docker integration tests
validate the typed registry and compare an instrumented workflow against direct
evaluation, including durable typed results and conflicting submissions.
Theme tests check styled wrapping/clipping, missing samples, meter saturation,
multicore CPU values, shared shell/table styling, and color opt-out.
Dashboard tests cover all-run paging, resizing, unavailable statistics, stopped
nodes, terminal cleanup, and returning from `top` to the anchored prompt.

Pure effect tests execute complete deployment, launch/resume, pause/kill,
inspection and REPL commands, plus keyboard navigation and timed live-view refresh.
They inject host failures throughout deployment, launch, pause, kill and watch
to check lock and terminal cleanup, and separately check finalizer error propagation.
Shell tests cover prompt placement, resizing, completion, file paths with spaces,
history, UTF-8 input, bracketed paste and handing terminal ownership to `watch`.
Deployment-command tests cover persistent selection, conflicting names, corrupt
catalog recovery, offline Docker, missing volumes, and read-only diagnostics.
Cleanup tests cover resource ownership, retired workers, incomplete deployments,
retries after Docker or filesystem failures, and preservation of other deployments.
Streaming tests cover split UTF-8/CRLF, partial lines, bounded output, editing and
scrolling during execution, resize, interruption, and finalizer failures.

`lake exe cloud_process_tests` exercises the native handler with Lean subprocesses:
incremental output, both pipes beyond pipe capacity, exit codes, invalid arguments,
SIGINT recovery, and cleanup of descendants, including when their parent exits first.
It also checks recursive deployment-file removal without following symlinks.

Run `lake exe cloud_console_tests` for the console's Docker smoke test. It checks
input rejection before launch, concurrent runs, retained images after replacing
the build tag, source events, and recovery after killing a worker and scheduler.
It checks stable node identities across submissions, pause/resume, terminal cancellation,
preserved completed results, and cancellation after deployment restart.
It cleans up its own containers, volumes, and image tags and retains its local
catalog for diagnosis.

CI also runs a focused test through the compiled CLI executable:

```sh
lake build lean_cloud
lake exe cloud_console_tests --lifecycle-only
```

It starts with saved RabbitMQ configuration and a retired worker volume, verifies
that `deploy` rejects them with reset instructions, then runs `clean`, `deploy`,
`programs`, `status`, `run`, `result`, `ps`, `inspect`, `watch --once`, `down`, `up`,
and `clean` against real Docker, HTTP, SQLite, and blob storage. It verifies the
workflow result, persistence across restart, complete removal, and source
preservation. The test uses a separate deployment and catalog; command logs are
retained under `.lean-cloud/cli-command-logs-PID/` and uploaded by CI on failure.

`lake exe cloud_console_tests --maintenance-only` drives the real CLI through
scaling from zero workers, per-run removal, backup, complete cleanup, restore,
and resumed execution. It checks that shared nodes and neighboring runs survive
removal, removed IDs stay reserved, paused runs remain paused, and incomplete
restores cannot start. CI runs this alongside the existing runtime suites.

The console smoke test also creates a separate user application, builds a custom
Lake executable with generated deployment files, and verifies results for sample
and supplied input. It checks deployment selection, status and diagnostics, then
takes the app down and verifies its results after `up` without rebuilding.
Tests use an isolated deployment index. Run only the generated-app check with
`lake exe cloud_console_tests --app-only`, or the shared-pool check with
`lake exe cloud_console_tests --pool-only`.
