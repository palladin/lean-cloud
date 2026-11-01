import LeanBuild.Builders.Program
import LeanBuild.BuildIO
import LeanBuild.Prefetch
import LeanCloudRuntime.Parallel
import Std.Sync.Channel

namespace LeanBuild.Builders
open Lean LeanCloud LeanCloudRuntime LeanEff

private def readResultTyped (env : Environment IO) (name : String) : BuildIO (Option BuildResult) := do
  let some ref ← BuildIO.capture .network (env.blobs.readNamed (resultName name)) | return none
  let text ← BuildIO.capture .network (env.blobs.readText ref)
  let result : BuildResult ← liftExcept ((Json.parse text >>= fromJson?).mapError BuildError.protocol)
  unless result.name == name do throw (.protocol "Module result name mismatch")
  return some result

def readResult (env : Environment IO) (name : String) : IO (Option BuildResult) :=
  (readResultTyped env name).toIO

private def publishResultTyped (env : Environment IO) (result : BuildResult) : BuildIO BuildResult := do
  let ref ← BuildIO.capture .network (env.blobs.putText (toJson result).compress)
  let selected ← BuildIO.capture .network (env.blobs.publishNamed (resultName result.name) ref)
  if selected == ref then return result
  let text ← BuildIO.capture .network (env.blobs.readText selected)
  let value : BuildResult ← liftExcept ((Json.parse text >>= fromJson?).mapError BuildError.protocol)
  unless value.name == result.name do throw (.protocol "Module result name mismatch")
  return value

def publishResult (env : Environment IO) (result : BuildResult) : IO BuildResult :=
  (publishResultTyped env result).toIO

private structure Cache where
  results : Std.HashMap String BuildResult := {}
  reading : Std.HashMap String (IO.Promise (Except BuildError (Option BuildResult))) := {}
  /-- Artifacts and their full ancestry have finished preparation on this worker. -/
  prepared : Std.HashSet String := {}

/-- Only committed successes/failures are cached. Missing results may become
available at any time, so a negative lookup is never retained. -/
private def read (env : Environment IO) (state : Std.Mutex Cache)
    (limit : Parallel.Limit) (name : String) : BuildIO (Option BuildResult) := do
  let entry : BuildResult ⊕ (IO.Promise (Except BuildError (Option BuildResult)) × Bool) ← state.atomically do
    let s ← get
    if let some result := s.results[name]? then return .inl result
    if let some pending := s.reading[name]? then return .inr (pending, false)
    let pending ← IO.Promise.new
    set { s with reading := s.reading.insert name pending }
    return .inr (pending, true)
  match entry with
  | .inl result => return some result
  | .inr (pending, owner) =>
    if owner then
      -- Only the owner consumes IO capacity. Concurrent lookups share its
      -- result, including absence/errors; later lookups retry those outcomes.
      let outcome ← BuildIO.inspect (ExceptT.mk (limit.run (BuildIO.outcome (readResultTyped env name))))
      state.atomically do
        modify fun s => { s with
          reading := s.reading.erase name
          results := match outcome with
            | .ok (some result) => s.results.insert name result
            | _ => s.results }
      pending.resolve outcome
    liftExcept (← IO.wait pending.result!)

/-- One persistent compiler session. Submit queues work; the engine limits
compilation concurrency. Only the coordinator calls submit/poll. Preparation
and publication run in separate bounded pools. -/
structure Engine (α : Type) where
  /-- Start exactly one session with the worker's CPU budget. -/
  start : Nat → IO Unit := fun _ => pure ()
  prefetch : CancellationToken IO → Array BuildResult → IO Unit := fun _ _ => pure ()
  /-- Direct parents plus ancestors not already prepared by this session.
  Successful preparation/prefetch must retain their installed artifacts. -/
  prepare : CancellationToken IO → Module → Array BuildResult → IO Unit
  submit : Module → IO Unit
  poll : IO (Array (String × α))
  publish : CancellationToken IO → Module → α → IO BuildResult
  finish : IO Unit
  cancel : IO Unit

private structure Claim where
  delivery : WorkDelivery
  settled : Std.Mutex Bool

private def Claim.settle (claim : Claim) (queue : WorkQueue IO) (failed : Bool) : IO Unit :=
  claim.settled.atomically do
    unless ← get do
      queue.complete claim.delivery.receipt failed
      set true

private def Claim.release (claim : Claim) (queue : WorkQueue IO) : IO Unit :=
  claim.settled.atomically do
    unless ← get do
      queue.release claim.delivery.receipt
      set true

/-- Replicas carry the service's monotone revision. Watch displays one shared
counter, never adds overlapping worker knowledge. Telemetry cannot fail a build. -/
private def report (env : Environment IO) (queue : WorkQueue IO) (total : Nat)
    (activity : String) : IO Unit := do
  try
    let stats ← queue.progress
    env.progress.report "build" {
      completed := stats.completed, total := some total
      message := if stats.failed == 0 then "Modules finished" else s!"Modules finished · {stats.failed} failed/blocked"
      shared := some queueName, revision := stats.completed }
    env.progress.report "worker" { message := activity }
  catch _ => pure ()

/-- Interpret domain requests, scoped asynchronous jobs, and bounded maps.
Errors stay typed across child tasks, pool shutdown, and Eff continuations. -/
partial def runProgram
    (handle : {β : Type} → Operation α β → BuildIO β)
    (launch : BuildIO (Event α) → BuildIO Unit) (program : Program α β) : BuildIO β := do
  match program.run with
  | .pure _ result => liftExcept result
  | .impure _ (.request operation) next =>
    runProgram handle launch (ExceptT.mk (next.apply (← BuildIO.inspect (handle operation))))
  | .impure _ (.launch job) next =>
    launch (runProgram handle launch (ExceptT.mk job))
    runProgram handle launch (ExceptT.mk (next.apply ()))
  | .impure _ (.parallel limit count jobs) next =>
    let result ← BuildIO.inspect (BuildIO.parallel limit (Array.finRange count) fun i =>
      runProgram handle launch (ExceptT.mk (jobs i)))
    runProgram handle launch (ExceptT.mk (next.apply result))
  | .impure _ (.all limit count jobs) next =>
    let result ← BuildIO.inspect (BuildIO.all limit (Array.finRange count) fun i =>
      runProgram handle launch (ExceptT.mk (jobs i)))
    runProgram handle launch (ExceptT.mk (next.apply result))

private def dataHandle (env : Environment IO) : Operation α β → BuildIO β
  | .readResult name => readResultTyped env name
  | .commitResult result => publishResultTyped env result
  | .send items => BuildIO.capture .network ((env.queues.open queueName).send items)
  | _ => throw (.protocol "This operation requires an active builder session")

private def noLaunch (_ : BuildIO (Event α)) : BuildIO Unit :=
  throw (.protocol "This program cannot launch builder jobs")

def seed (env : Environment IO) (plan : Plan) : IO Unit :=
  (runProgram (dataHandle env) noLaunch (seedProgram (α := Unit) plan)).toIO

def results (env : Environment IO) (plan : Plan) : IO (Array BuildResult) :=
  (runProgram (dataHandle env) noLaunch (resultsProgram (α := Unit) plan env.currentWorker.cpus)).toIO

private structure Control where
  stopped : Bool := false
  error : Option BuildError := none
  claims : Std.HashMap String Claim := {}

/-- One scope owns all tasks, leases and transfer caches. Preserve the first
failure while collecting cleanup failures; every cleanup action is attempted. -/
def runTyped (env : Environment IO) (plan : Plan) (engine : Engine α) : BuildIO Unit := ExceptT.mk do
  let queue := env.queues.open queueName
  let cache ← Std.Mutex.new ({} : Cache)
  let reads ← Parallel.Limit.new (ioConcurrency env.currentWorker.cpus)
  let control ← Std.Mutex.new ({} : Control)
  let stop : CancellationToken IO := ⟨do
    return (← env.cancellation.isRequested) || (← control.atomically do return (← get).stopped)⟩
  let events ← Std.Channel.new (α := Event α)
  let tasks ← IO.mkRef (#[] : Array (Task (Except IO.Error Unit)))
  let fail (error : BuildError) : IO Unit := do
    if error.isCancelled && (← stop.isRequested) then return
    control.atomically (modify fun s => { s with stopped := true, error := s.error.orElse (fun _ => some error) })
  let launch (job : BuildIO (Event α)) : BuildIO Unit := BuildIO.capture .tool do
    unless ← stop.isRequested do
      let task ← IO.asTask (do
        match ← BuildIO.outcome job with
        | .ok event => unless ← stop.isRequested do events.sync.send event
        | .error error => fail error) .dedicated
      tasks.modify (·.push task)
  let ioSlots := max 2 (min 8 env.currentWorker.cpus)
  let settings := Settings.ofPlan plan env.currentWorker.cpus
  let activity ← Std.Mutex.new "Starting Lake"
  let session ← IO.mkRef ({} : LakeSession.State)
  -- All Lake operations originate from the coordinator thread. Launched jobs
  -- only prepare/publish/settle; they never access this session reference.
  -- Final engine cancellation also runs on the coordinator, before joining jobs.
  let lakeHandle : {β : Type} → LakeSession.Operation α β → BuildIO β := fun op =>
    match op with
    | .start cpus => do
      let next ← liftExcept ((← session.get).start.mapError BuildError.protocol)
      BuildIO.capture .tool (engine.start cpus)
      session.set next
    | .submit m => do
      let next ← liftExcept (((← session.get).submit m.name).mapError BuildError.protocol)
      BuildIO.capture .tool (engine.submit m)
      session.set next
    | .poll => do
      let results ← BuildIO.capture .tool engine.poll
      let next ← liftExcept (((← session.get).complete (results.map (·.1))).mapError BuildError.protocol)
      session.set next
      return results
    | .finish => do
      let next ← liftExcept ((← session.get).finish.mapError BuildError.protocol)
      BuildIO.capture .tool engine.finish
      session.set next
    | .cancel => do
      BuildIO.capture .tool engine.cancel
      session.modify (·.cancel)
  let handle : {β : Type} → Operation α β → BuildIO β := fun operation =>
    match operation with
    | .readResult name => read env cache reads name
    | .commitResult result => do
      if ← stop.isRequested then throw .cancelled
      let result ← publishResultTyped env result
      cache.atomically (modify fun s => { s with results := s.results.insert result.name result })
      return result
    | .prepared => cache.atomically do return (← get).prepared
    | .remember inputs => cache.atomically do
      modify fun s => { s with prepared := inputs.foldl (fun names r => names.insert r.name) s.prepared }
    | .install m inputs prefetch => do
      unless ← stop.isRequested do
        BuildIO.capture .tool (if prefetch then engine.prefetch stop inputs else engine.prepare stop m inputs)
    | .lake op => lakeHandle op
    | .publish m value => BuildIO.capture .network (engine.publish stop m value)
    | .receive count => do
      let deliveries ← BuildIO.capture .network (queue.receive count)
      for delivery in deliveries do
        let claim := { delivery, settled := ← Std.Mutex.new false : Claim }
        control.atomically do
          modify fun s => { s with claims := s.claims.insertIfNew delivery.receipt claim }
      let idle ← if deliveries.isEmpty then BuildIO.capture .network queue.isIdle else pure false
      return (deliveries, idle)
    | .send items => do unless ← stop.isRequested do BuildIO.capture .network (queue.send items)
    | .complete receipts failed => do
      for receipt in receipts do
        let some claim ← control.atomically do return (← get).claims[receipt]?
          | throw (.protocol "Unknown queue receipt")
        unless ← stop.isRequested do BuildIO.capture .network (claim.settle queue failed)
    | .release receipts => do
      for receipt in receipts do
        let some claim ← control.atomically do return (← get).claims[receipt]?
          | throw (.protocol "Unknown queue receipt")
        BuildIO.capture .network (claim.release queue)
    | .cancelled => stop.isRequested
    | .activity text => activity.atomically (set text)
    | .events => do
      IO.sleep 10
      if let some error ← control.atomically do return (← get).error then throw error
      if ← stop.isRequested then return (← IO.monoMsNow, #[.cancelled])
      tasks.set (← (← tasks.get).filterM fun task => return !(← IO.hasFinished task))
      control.atomically do
        let s ← get
        let claims ← s.claims.toArray.filterM fun (_, c) => return !(← c.settled.atomically get)
        set { s with claims := Std.HashMap.ofArray claims }
      let mut replies := #[]
      while let some event ← events.tryRecv do replies := replies.push event
      return (← IO.monoMsNow, replies)
  let background ← IO.mkRef (#[] : Array (Task (Except IO.Error Unit)))
  let startBackground (action : BuildIO Unit) : IO Unit := do
    let task ← IO.asTask (do
      if let .error error ← BuildIO.outcome action then fail error) .dedicated
    background.modify (·.push task)
  let body ← BuildIO.outcome do
    startBackground <| BuildIO.capture .network do
      let mut next := (← IO.monoMsNow) + 10000
      while !(← stop.isRequested) do
        if (← IO.monoMsNow) ≥ next then
          let claims ← control.atomically do return (← get).claims.toArray.map (·.2)
          discard <| Parallel.map ioSlots claims fun claim => claim.settled.atomically do
            unless ← get do queue.renew claim.delivery.receipt
          next := (← IO.monoMsNow) + 10000
        IO.sleep 50
    startBackground <| BuildIO.capture .tool do
      let mut next := 0
      while !(← stop.isRequested) do
        if (← IO.monoMsNow) ≥ next then
          report env queue plan.modules.size (← activity.atomically get)
          next := (← IO.monoMsNow) + 1000
        IO.sleep 50
    startBackground <| Prefetch.runTyped queue stop ioSlots fun childStop value => do
      let execute : {β : Type} → Operation α β → BuildIO β := fun op =>
        match op with
        | .cancelled => childStop.isRequested
        | .install m inputs warm => do
          if ← childStop.isRequested then throw .cancelled
          BuildIO.capture .tool (if warm then engine.prefetch childStop inputs else engine.prepare childStop m inputs)
          if ← childStop.isRequested then throw .cancelled
        | op => handle op
      try runProgram execute noLaunch (prefetch settings value)
      catch error => unless error.isCancelled && (← childStop.isRequested) do throw error
    runProgram handle launch (program plan env.currentWorker.cpus)
  if let .error error := body then fail error
  control.atomically (modify fun s => { s with stopped := true })
  -- No throwing finally: cancellation, joins and releases all run, and their
  -- failures are attached to the first build error instead of replacing it.
  let cancelled ← BuildIO.outcome (BuildIO.capture .tool engine.cancel)
  let mut joined : Except BuildError Unit := .ok ()
  for task in (← tasks.get) ++ (← background.get) do
    let result ← IO.wait task
    joined := BuildError.after joined (result.mapError (BuildError.tool ∘ toString))
  let first ← control.atomically do return (← get).error
  let mut result := BuildError.after (first.map Except.error |>.getD body) cancelled
  result := BuildError.after result joined
  let claims ← control.atomically do return (← get).claims.toArray.map (·.2)
  let released ← BuildIO.outcome <| BuildIO.capture .tool <|
    Parallel.map ioSlots claims fun claim => (BuildIO.capture .network (claim.release queue)).run
  match released with
  | .error error => result := BuildError.after result (.error error)
  | .ok outcomes => for outcome in outcomes do result := BuildError.after result outcome
  if result.isOk && !(← env.cancellation.isRequested) then report env queue plan.modules.size "Finished"
  return result

def run (env : Environment IO) (plan : Plan) (engine : Engine α) : IO Unit :=
  (runTyped env plan engine).toIO

end LeanBuild.Builders
