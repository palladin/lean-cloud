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
Docker and by default starts five containers: the scheduler, three workers, and global blobs. Each node includes its own RabbitMQ mailbox.
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
cloud> nodes
cloud> quit
```

The example results are `55` and `files=16, errors=24`. By default, `deploy` starts one
scheduler, three persistent workers, and global blob storage: five long-lived
containers. Each scheduler/worker container includes its own RabbitMQ broker. Every compute node contains the same
application executable and complete registered-program registry.

`run PROGRAM` submits a logical cloud process to this existing pool. It does
not create containers. The scheduler assigns work from different runs to free
workers, rotating between runnable runs. A worker loads the run's immutable
entry point and input, selects the registered program, and executes an assignment
with the existing replay interpreter. Results remain isolated by run ID.
After completing an assignment, the worker asks for more work; nodes remain
running even when every workflow has finished. Closing the console leaves the
pool running. `ps` lists workflows; `top` shows the deployed compute nodes,
including idle nodes; `nodes` also includes blob storage.

Use `down` to stop and remove the deployment's containers while preserving blobs,
mailboxes, scheduler state, images, and the local catalog. `up` starts the saved
image without rebuilding and automatically recovers active runs. Paused runs
remain paused. It checks that durable volumes still exist before starting.
Use `deploy` when application code changes. Changing the image requires completing
or killing unfinished runs first: replay must use the same application code.
Redeploying after `down` starts the retained services before checking saved
results. Missing durable volumes are reported instead of silently recreated.

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
worker starts with its own RabbitMQ mailbox. Scaling does not rebuild the image or
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
including after an interrupted command. Use `status`, `nodes`, or `top` to inspect
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

`kill RUN` durably revokes the run and creates a terminal cancellation in its
root record. A normal result that won the atomic creation race is preserved.
A killed run cannot resume or reuse its ID. Killing does not undo external
actions or delete records. `Cloud.exec` can execute again if interruption occurs
before its result is recorded, so external actions must tolerate retries.

The scheduler alone writes its SQLite state through lean-linq. It saves control
changes before confirming replies. The console also saves pending control intent:
if `ps` shows `pausing` or `killing`, retry that command. A pending kill blocks
resume. Process controls need the deployment scheduler; use `up` if it is down.
The console executes short application commands inside the existing scheduler
container, including validation, submission and result queries.

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

`status` counts locally recorded runs; use `ps` for workflow completion status.
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
run concurrently. Preserve the local catalog, broker volumes, scheduler volume,
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
Each node includes its mailbox broker. `nodes` also lists blob storage.

`top --once` (or piped `top`) prints a plain-text snapshot of every page. Rates
need two samples, so that first snapshot shows `—` for network and I/O rates.

`watch RUN` browses execution steps for running, completed, paused, failed, and
killed processes. It opens at the latest observation and follows new events.

The **Global view** shows workers in pages of three panels, each with
its observed location, code window, and resource graphs. The **Worker view**
expands that worker's code and metrics and filters the step list to that worker.
The visible `[Global] [Worker 1] [Worker 2] [Worker 3]` tabs identify the current view.
Use `[` and `]` to page through workers. Small terminals show compact panels; select one for full details.
When browsing history, switching workers
selects that worker's nearest preceding observation (or its first, if none precedes
the cursor). The banner distinguishes following live activity from browsing history.

- **Arrow keys:** select the previous or next step; browsing freezes the cursor.
- **PgUp / PgDn:** move a page of steps; **Home:** select the first step.
- **End / f:** return to the latest step and follow new observations.
- **g / 0:** Global view; **1 / 2 / 3:** select a worker on the visible page.
- **[ / ]:** previous or next page of workers.
- **Tab / Shift-Tab:** cycle through Global and every Worker view, including retired workers in history.
- **j / k:** scroll source; **a:** follow the selected step's source line.
- **q:** return to the prompt.

The trace shows the actor, location, activity, and operation. Selecting a mapped
step highlights its source line even if the worker has stopped. Each worker's
panel shows its last observation at that point in the trace. `>` identifies a mapped
step; `~` identifies the last mapped line at the same location and attempt when the
latest observation has no source mapping. Navigation never resumes or re-executes
the process. **Historical graphs use recorded samples at or before the cursor.**
They never fall back to current Docker stats. Missing samples say `not recorded`.
A noninteractive terminal or `--once` prints one frame without control sequences.

The console reads all retained Docker logs, including earlier worker incarnations,
and saves observations in each run's local `trace.json`. `down` and image replacement
collect logs after stopping actors and before removing their containers. Saved
steps remain browsable when Docker or the deployment is unavailable. Log rotation,
a dropped event, or containers removed outside the CLI can leave gaps; the cache
cannot reconstruct observations that were never collected. The display uses Docker
log timestamps, which do not establish causal order between concurrent workers.
Ordinary pure code and arbitrary lines inside an IO body are not instrumented.

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
While browsing history, or inspecting a completed, paused, or killed run, they use
resource counters attached to the worker's trace events. Collection happens in the
runtime even when no console is connected. Rebuild with `deploy` once to enable it
for future runs; already missing samples cannot be recovered.

The Linux container runtime samples cgroup v2 CPU, memory, and I/O counters,
network-interface counters, and root-filesystem usage at trace boundaries.
CPU and transfer rates use adjacent samples from the same process incarnation;
they are unavailable until two usable samples exist. Sampling is event-based,
so a long computation need not produce intermediate samples. A panel identifies
the last recorded sample's time. These are container-wide measurements, including
the node's RabbitMQ broker and other workflows sharing that worker. Unsupported
counters remain missing.
The [kernel's cgroup documentation](https://docs.kernel.org/admin-guide/cgroup-v2.html)
defines the CPU, memory, and I/O counters.

Both modes display:

- CPU utilization and memory usage/limit;
- network receive/send rates;
- block-device read/write rates;
- filesystem used/capacity where the container provides `df`.

CPU, memory, and filesystem usage have text meters. Their fill is green below
70%, yellow from 70%, and red from 90%. A CPU meter represents one core; usage
above 100% keeps its full numeric value and adds `+` to the meter. Memory and
filesystem meters use their reported capacity. The `nodes` table also shows CPU
and memory meters.

Network receive/send and disk read/write rates have distinct colored histories.
Graphs use `_` for measured zero and `·` for an unavailable rate; the first counter
sample has no rate yet. CPU and memory histories appear when the panel is wide
enough, scaled to one core and the reported memory limit respectively.

Node statistics include both Lean and its RabbitMQ broker. CPU can exceed 100% on
multiple cores. Filesystem capacity can be shared between containers; it is not
space attributed exclusively to the selected container. Missing samples are not
zero utilization. Rate series restart when a container restarts or counters reset.
Graphs display up to 30 samples from the chosen incarnation, ending at the selected
moment. Historical samples are retained with the trace cache and survive console
restart and deployment shutdown. Rate graphs scale independently.

## Validation

`lake test` includes shell parsing, input identifiers, source-map ambiguity,
terminal escape sanitization, metric units, counter resets, bounded history, and
historical source markers, trace deduplication, stable cursor selection during refresh,
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
Streaming tests cover split UTF-8/CRLF, partial lines, bounded output, editing and
scrolling during execution, resize, interruption, and finalizer failures.

`lake exe cloud_process_tests` exercises the native handler with Lean subprocesses:
incremental output, both pipes beyond pipe capacity, exit codes, invalid arguments,
SIGINT recovery, and cleanup of descendants, including when their parent exits first.

Run `lake exe cloud_console_tests` for the console's Docker smoke test. It checks
input rejection before launch, concurrent runs, retained images after replacing
the build tag, source events, and recovery after killing a worker and scheduler.
It checks stable node identities across submissions, pause/resume, terminal cancellation,
preserved completed results, and cancellation after deployment restart.
It cleans up its own containers, volumes, and image tags and retains its local
catalog for diagnosis.

The console smoke test also creates a separate user application, builds a custom
Lake executable with generated deployment files, and verifies results for sample
and supplied input. It checks deployment selection, status and diagnostics, then
takes the app down and verifies its results after `up` without rebuilding.
Tests use an isolated deployment index. Run only the generated-app check with
`lake exe cloud_console_tests --app-only`, or the shared-pool check with\n`lake exe cloud_console_tests --pool-only`.
