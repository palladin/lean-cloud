import LeanCloud.Worker
import LeanCloud.Scheduler
import LeanCloud.Telemetry
import LeanCloud.Observations
import Std.Time.DateTime.Timestamp

namespace LeanCloudRuntime.Trace
open Lean LeanCloud LeanEff

@[extern "lc_trace_emit"] private opaque emitLine (line : @&String) : IO Unit
@[extern "lc_trace_resources"] private opaque resourceCounters : IO String

initialize incarnation : String ← do
  return s!"{← IO.Process.getPID}-{← IO.monoNanosNow}"

def resources : IO (Option ResourceSample) := do
  try
    let json ← IO.ofExcept (Json.parse (← resourceCounters))
    return (fromJson? (json.setObjVal! "incarnation" (toJson incarnation))).toOption
  catch _ => return none

abbrev Recorder := Observations.Step → IO Unit

structure State where
  seq : Nat := 0
  attempt : Option Nat := none
  location : String := ""
  source : Option SourceSiteId := none
  branch : Option Location := none

structure Sink where
  worker : String
  session : String
  started : Nat
  state : IO.Ref State
  run : String := ""
  record : Recorder := fun _ => pure ()

def create (worker : String) (run : String := "") (record : Recorder := fun _ => pure ()) : IO Sink := do
  let started ← IO.monoMsNow
  return ⟨worker, s!"{← IO.Process.getPID}-{← IO.monoNanosNow}", started, ← IO.mkRef {}, run, record⟩

/-- Diagnostics never turn a successful operation into a workflow error.
Docker's bounded log driver retains recent events; gaps are allowed. -/
def Sink.emit (sink : Sink) (activity operation : String) (job : Option BranchObservation := none) : IO Unit := do
  try
    let state ← sink.state.get
    sink.state.set { state with seq := state.seq + 1 }
    let event : ExecutionEvent := ⟨sink.session, state.seq, (← IO.monoMsNow) - sink.started,
      sink.worker, state.attempt, state.location, activity, operation, sink.run, state.source⟩
    let resources ← Trace.resources
    let now := toString (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.val
    let timestamp := String.ofList (List.replicate (20 - now.length) '0') ++ now
    sink.record { timestamp, event, resources, branch := state.branch, job }
    let json := (toJson event).setObjVal! "resources" (toJson resources)
    let json := json.setObjVal! "branch" (toJson state.branch)
    let json := json.setObjVal! "job" (toJson job)
    emitLine ("@lean-cloud " ++ json.compress ++ "\n")
  catch _ => pure ()

def Sink.assign (sink : Sink) (assignment : Assignment) : IO Unit := do
  sink.state.modify fun state => { state with attempt := some assignment.attempt, location := assignment.branchStart.key, source := none, branch := some assignment.branchStart }
  sink.emit "assigned" ""

/-- Lease renewal changes no visible branch state. Emit deltas, not the entire
inspection tree on every heartbeat. These diagnostics never drive scheduling. -/
def Sink.branches (sink : Sink) (before after : Array Scheduler.Job) : IO Unit := do
  let previous := before.foldl (fun (found : Std.HashMap String BranchObservation) job =>
    found.insert job.branch.key (BranchObservation.ofJob job)) {}
  for job in after do
    let observation := BranchObservation.ofJob job
    if previous[job.branch.key]? == some observation then continue
    let (attempt, label) := match job.status with
      | .pending => (none, if job.joining then "joining" else "pending")
      | .running worker attempt _ => (some attempt, s!"running · {worker}")
      | .waiting children => (none, s!"waiting · {children.size} branches")
      | .done => (none, "completed")
    sink.state.modify fun state => { state with attempt, location := job.location.key, source := none, branch := some job.branch }
    sink.emit "branch-state" label (some observation)

/-- Set context before the interpreter touches a record, including replay hits. -/
def Sink.visit (sink : Sink) (location : Location) (source : Option SourceSiteId)
    (parallelLabel : Option String) : IO Unit := do
  sink.state.modify fun state => { state with location := location.key, source }
  if let some label := parallelLabel then sink.emit "parallel-label" label

/-- Joining probes child returns. Restore the parallel location before retaining
its source, rather than attributing the suspension to the last child read. -/
def Sink.suspend (sink : Sink) (location : Location) : IO Unit := do
  sink.state.modify fun state => { state with location := location.key }
  sink.emit "suspended" "parallel"

private def operation (request : Request) : String :=
  if request.kind == "exec" then request.payload.getStr?.toOption.getD "exec" else request.kind

private def recordLocation (key : String) : String :=
  ((key.splitOn "/value").head!).splitOn "/return" |>.head!

def Sink.records (sink : Sink) (store : ReplayStore IO) : ReplayStore IO where
  read key := do
    sink.state.modify fun state => { state with location := recordLocation key }
    sink.emit "read-record" ""
    let record ← store.read key
    if let some record := record then sink.emit "replay" (operation record.request)
    else sink.emit "missing-record" ""
    return record
  create key record := do
    sink.state.modify fun state => { state with location := recordLocation key }
    sink.emit "save-record" (operation record.request)
    let recorded ← store.create key record
    sink.emit "recorded" (operation recorded.request)
    return recorded

/-- Wrap only IO bodies, preserving the effect tree, requests, and record keys.
The bound limits diagnostic traversal; exhausting it leaves the program intact. -/
def Sink.instrument (sink : Sink) (fuel : Nat) (program : Cloud IO α) : Cloud IO α :=
  match fuel, program with
  | 0, _ => program
  | _, EffF.pure _ _ => program
  | fuel + 1, EffF.impure info control next =>
    let control := match control with
      | .command codec label body => .command codec label fun environment => do
          sink.emit "execute" label
          body environment
      | .parallel codec count branches label =>
          .parallel codec count (fun i => sink.instrument fuel (branches i)) label
      | other => other
    EffF.impure info control (.one fun value => sink.instrument fuel (ArrsF.apply next value))

end LeanCloudRuntime.Trace
