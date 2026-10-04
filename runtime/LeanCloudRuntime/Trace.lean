import LeanCloud.Worker
import LeanCloud.Telemetry

namespace LeanCloudRuntime.Trace
open Lean LeanCloud LeanEff

@[extern "lc_trace_emit"] private opaque emitLine (line : @&String) : IO Unit

structure State where
  seq : Nat := 0
  attempt : Option Nat := none
  location : String := ""

structure Sink where
  worker : String
  session : String
  started : Nat
  state : IO.Ref State
  run : String := ""

def create (worker : String) (run : String := "") : IO Sink := do
  let started ← IO.monoMsNow
  return ⟨worker, s!"{← IO.Process.getPID}-{started}", started, ← IO.mkRef {}, run⟩

/-- Diagnostics never turn a successful operation into a workflow error.
Docker's bounded log driver retains recent events; gaps are allowed. -/
def Sink.emit (sink : Sink) (activity operation : String) : IO Unit := do
  try
    let state ← sink.state.get
    sink.state.set { state with seq := state.seq + 1 }
    let event : ExecutionEvent := ⟨sink.session, state.seq, (← IO.monoMsNow) - sink.started,
      sink.worker, state.attempt, state.location, activity, operation, sink.run⟩
    emitLine ("@lean-cloud " ++ (toJson event).compress ++ "\n")
  catch _ => pure ()

def Sink.assign (sink : Sink) (assignment : Assignment) : IO Unit := do
  sink.state.modify fun state => { state with attempt := some assignment.attempt, location := assignment.location.key }
  sink.emit "assigned" ""

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

def Sink.blobs (sink : Sink) (storage : BlobStorage IO) : BlobStorage IO where
  putBlob bytes := do
    sink.emit "execute" "putBlob"
    storage.putBlob bytes
  readBlob ref := do
    sink.emit "execute" "readBlob"
    storage.readBlob ref
  resolveBlob name := do
    sink.emit "execute" "resolveBlob"
    storage.resolveBlob name

/-- Wrap only IO bodies, preserving the effect tree, requests, and record keys.
The bound limits diagnostic traversal; exhausting it leaves the program intact. -/
def Sink.instrument (sink : Sink) (fuel : Nat) (program : Cloud IO α) : Cloud IO α :=
  match fuel, program with
  | 0, _ => program
  | _, EffF.pure _ => program
  | fuel + 1, EffF.impure control next =>
    let control := match control with
      | .command codec (.exec label body) => .command codec (.exec label fun _ => do
          sink.emit "execute" label
          body ())
      | .parallel codec count branches => .parallel codec count fun i => sink.instrument fuel (branches i)
      | other => other
    EffF.impure control (.one fun value => sink.instrument fuel (ArrsF.apply next value))

end LeanCloudRuntime.Trace
