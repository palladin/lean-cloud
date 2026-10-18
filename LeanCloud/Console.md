# Cloud console

Run `lake exe lean_cloud`. Connect to a deployed scheduler:

```text
cloud> connect development http://127.0.0.1:8080 --token-file .deployment/client.token
cloud> programs
cloud> run sum-squares --id my-example
cloud> ps
cloud> watch my-example
cloud> result my-example
```

Local and remote deployments use the same HTTP client. No application checkout,
Docker, Kubernetes, or provider CLI is needed by the console. Use HTTPS for remote
endpoints. HTTP is accepted only on loopback, including private port-forwards.

`connect NAME URL` reads `LEAN_CLOUD_TOKEN` by default. Use `--token-env VARIABLE`
or `--token-file FILE` to reference another credential. Profiles save references,
never credential values. `connections` lists profiles; `use NAME` selects one.
The selected profile persists across sessions under `LEAN_CLOUD_HOME`, or the
user's local state directory.

| Command | Purpose |
| --- | --- |
| `programs` | List the deployed registry |
| `run PROGRAM [--input FILE] [--id NAME]` | Submit a workflow |
| `ps` | List runs with status, start/end times and elapsed time |
| `inspect RUN` | Inspect branches and scheduler progress |
| `result RUN` | Read its outcome or text blob result |
| `watch RUN [--once]` | Branch tree, source positions and worker metrics |
| `top [--once]` | Worker/scheduler resource graphs |
| `logs RUN [NODE]` | Latest retained workflow observations |
| `pause RUN`, `resume RUN`, `kill RUN` | Control execution |
| `remove RUN` | Retire a terminal run and remove its replay records |
| `status`, `doctor` | Check the scheduler API and node endpoints |
| `help [COMMAND]` | Help; also `COMMAND --help` |
| `quit` | Exit; workflows continue on the deployment |

The prompt and completion footer remain anchored. Scroll output with the mouse
wheel, select by dragging, or Ctrl-A on an empty prompt to select the transcript.
Ctrl-C copies a selection. Tab/Shift-Tab complete; up/down recall commands.

Watch selects branches with up/down and folds groups with left/right. A parallel
group shows all its workers; a branch shows its executing worker. Completed runs
show the last view with frozen metrics. There is no history timeline. Source,
telemetry and outcomes come from the API; caches allow a clearly labeled last
view during an outage. `logs` is not a complete container-log archive.

Use `@[cloud_func]` to describe a Cloud helper in `watch`:

```lean
@[cloud_func (descr := "Analyze a value") (opaque := true)]
def analyze (n : Nat) : Cloud IO Nat := cloud {
  let value ← Cloud.pure (fun _ => n * n) "square"
  return value + 1
}

def workflow : Cloud IO Nat := cloud {
  analyze 7  -- watch stays here while analyze executes
}
```

Both options are optional. `descr` defaults to the function name; `opaque`
defaults to `true`. The description appears beside the source location in the
branch panel and worker cards. Use `(opaque := false)` to follow the helper's
internal source lines while still displaying its description.

Opaque helpers hide implementation locations, including nested helper calls. User Cloud
computations passed into the helper retain their own source locations. After
the helper returns, `watch` follows the caller's next statement. The annotation
changes display metadata only; replay locations and recorded results are unchanged.

Both `watch` and `top` show each worker or scheduler's machine name, host logical
CPU count and total RAM. The CPU and memory meters show container usage and
capacity separately: 100% CPU means one logical CPU, and CPU capacity includes
visible affinity and quota limits. A Kubernetes node can host several workers;
on Docker Desktop, the host is its Linux VM. Missing metadata stays unavailable,
with the container hostname used when no machine name is supplied.
Capacity reflects limits visible inside the container. Parent limits can be
shared with other containers; they do not reserve those resources for a worker.

This requires an updated runtime image. The deployment helpers supply
`CLOUD_NODE_NAME` from Docker's engine name or Kubernetes `spec.nodeName`. Custom
deployment scripts can set the same environment variable; no infrastructure
access is needed by the console.

A submission prints its ID before sending. Retry with that same ID after an
uncertain response. Control requests persist an idempotency key before sending;
repeat the same command to resolve an uncertain result. Pause/kill acceptance
is not proof workers have stopped; inspect the reported phase.

Infrastructure operations live in [deployment helpers](../deploy/README.md).
The console does not build images, provision resources, scale containers, manage
backups, or run login commands. Users can supply their own deployment scripts.
