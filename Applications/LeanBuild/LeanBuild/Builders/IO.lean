import LeanBuild.Builders.Program
import LeanBuild.Prefetch
import LeanCloudRuntime.Parallel
import Std.Sync.Channel

namespace LeanBuild.Builders
open Lean LeanCloud LeanCloudRuntime LeanEff

def readResult (env : Environment IO) (name : String) : IO (Option BuildResult) := do
  let some ref ← env.blobs.readNamed (resultName name) | return none
  let result : BuildResult ← IO.ofExcept (Json.parse (← env.blobs.readText ref) >>= fromJson?)
  unless result.name == name do throw (IO.userError "Module result name mismatch")
  return some result

def publishResult (env : Environment IO) (result : BuildResult) : IO BuildResult := do
  let ref ← env.blobs.putText (toJson result).compress
  let selected ← env.blobs.publishNamed (resultName result.name) ref
  if selected == ref then return result
  let value : BuildResult ← IO.ofExcept (Json.parse (← env.blobs.readText selected) >>= fromJson?)
  unless value.name == result.name do throw (IO.userError "Module result name mismatch")
  return value

private structure Cache where
  results : Std.HashMap String BuildResult := {}
  reading : Std.HashMap String (IO.Promise (Except IO.Error (Option BuildResult))) := {}
  /-- Artifacts and their full ancestry have finished preparation on this worker. -/
  prepared : Std.HashSet String := {}

/-- Only committed successes/failures are cached. Missing results may become
available at any time, so a negative lookup is never retained. -/
private def read (env : Environment IO) (state : Std.Mutex Cache)
    (limit : Parallel.Limit) (name : String) : IO (Option BuildResult) := do
  let entry : BuildResult ⊕ (IO.Promise (Except IO.Error (Option BuildResult)) × Bool) ← state.atomically do
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
      let outcome ← (limit.run (readResult env name)).toBaseIO
      state.atomically do
        modify fun s => { s with
          reading := s.reading.erase name
          results := match outcome with
            | .ok (some result) => s.results.insert name result
            | _ => s.results }
      pending.resolve outcome
    IO.ofExcept (← IO.wait pending.result!)

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

/-- Interpret domain requests, scoped asynchronous jobs, and bounded maps. -/
partial def runProgram
    (handle : {β : Type} → Operation α β → IO β)
    (launch : IO (Event α) → IO Unit) (program : Program α β) : IO β := do
  match program.run with
  | .pure _ result => IO.ofExcept result
  | .impure _ (.request operation) next =>
    let result ← try pure (.ok (← handle operation)) catch e => pure (.error e.toString)
    runProgram handle launch (ExceptT.mk (next.apply result))
  | .impure _ (.launch job) next =>
    launch (runProgram handle launch (ExceptT.mk job))
    runProgram handle launch (ExceptT.mk (next.apply ()))
  | .impure _ (.parallel limit count jobs) next =>
    let result ← try
      pure (.ok (← Parallel.map limit (Array.finRange count) fun i =>
        runProgram handle launch (ExceptT.mk (jobs i))))
    catch e => pure (.error e.toString)
    runProgram handle launch (ExceptT.mk (next.apply result))
  | .impure _ (.all limit count jobs) next =>
    let result ← try
      pure (.ok (← Parallel.all limit (Array.finRange count) fun i =>
        runProgram handle launch (ExceptT.mk (jobs i))))
    catch e => pure (.error e.toString)
    runProgram handle launch (ExceptT.mk (next.apply result))

private def dataHandle (env : Environment IO) : Operation α β → IO β
  | .readResult name => readResult env name
  | .commitResult result => publishResult env result
  | .send items => (env.queues.open queueName).send items
  | _ => throw (IO.userError "This operation requires an active builder session")

private def noLaunch (_ : IO (Event α)) : IO Unit :=
  throw (IO.userError "This program cannot launch builder jobs")

def seed (env : Environment IO) (plan : Plan) : IO Unit :=
  runProgram (dataHandle env) noLaunch (seedProgram (α := Unit) plan)

def results (env : Environment IO) (plan : Plan) : IO (Array BuildResult) :=
  runProgram (dataHandle env) noLaunch (resultsProgram (α := Unit) plan env.currentWorker.cpus)

private structure Control where
  stopped : Bool := false
  error : Option IO.Error := none
  claims : Std.HashMap String Claim := {}

/-- One scope owns all tasks, leases and transfer caches. Scheduling decisions
live in `program`; this handler only executes requests and delivers replies. -/
def run (env : Environment IO) (plan : Plan) (engine : Engine α) : IO Unit := do
  let queue := env.queues.open queueName
  let cache ← Std.Mutex.new ({} : Cache)
  let reads ← Parallel.Limit.new (ioConcurrency env.currentWorker.cpus)
  let control ← Std.Mutex.new ({} : Control)
  let stop : CancellationToken IO := ⟨do
    return (← env.cancellation.isRequested) || (← control.atomically do return (← get).stopped)⟩
  let events ← Std.Channel.new (α := Event α)
  let tasks ← IO.mkRef (#[] : Array (Task (Except IO.Error Unit)))
  let fail (error : IO.Error) : IO Unit := do
    unless ← env.cancellation.isRequested do
      control.atomically (modify fun s => { s with stopped := true, error := s.error.orElse (fun _ => some error) })
  let launch (job : IO (Event α)) : IO Unit := do
    unless ← stop.isRequested do
      let task ← IO.asTask (do
        try
          let event ← job
          unless ← stop.isRequested do events.sync.send event
        catch error => fail error) .dedicated
      tasks.modify (·.push task)
  let ioSlots := max 2 (min 8 env.currentWorker.cpus)
  let settings := Settings.ofPlan plan env.currentWorker.cpus
  let activity ← Std.Mutex.new "Starting Lake"
  let session ← IO.mkRef ({} : LakeSession.State)
  let lakeHandle : {β : Type} → LakeSession.Operation α β → IO β := fun op =>
    match op with
    | .start cpus => do
      let next ← IO.ofExcept (← session.get).start
      engine.start cpus
      session.set next
    | .submit m => do
      let next ← IO.ofExcept ((← session.get).submit m.name)
      engine.submit m
      session.set next
    | .poll => do
      let results ← engine.poll
      let next ← IO.ofExcept ((← session.get).complete (results.map (·.1)))
      session.set next
      return results
    | .finish => do
      let next ← IO.ofExcept (← session.get).finish
      engine.finish
      session.set next
    | .cancel => do
      engine.cancel
      session.modify (·.cancel)
  let handle : {β : Type} → Operation α β → IO β := fun {β} operation =>
    match operation with
    | .readResult name => read env cache reads name
    | .commitResult result => do
      if ← stop.isRequested then throw (IO.userError "Build cancelled")
      let result ← publishResult env result
      cache.atomically (modify fun s => { s with results := s.results.insert result.name result })
      return result
    | .prepared => cache.atomically do return (← get).prepared
    | .remember inputs => cache.atomically do
      modify fun s => { s with prepared := inputs.foldl (fun names r => names.insert r.name) s.prepared }
    | .install m inputs prefetch => do
      unless ← stop.isRequested do
        if prefetch then engine.prefetch stop inputs else engine.prepare stop m inputs
    | .lake op => lakeHandle op
    | .publish m value => engine.publish stop m value
    | .receive count => do
      let deliveries ← queue.receive count
      for delivery in deliveries do
        let claim := { delivery, settled := ← Std.Mutex.new false : Claim }
        control.atomically do
          modify fun s => { s with claims := s.claims.insertIfNew delivery.receipt claim }
      let idle ← if deliveries.isEmpty then queue.isIdle else pure false
      return (deliveries, idle)
    | .send items => do unless ← stop.isRequested do queue.send items
    | .complete receipts failed => do
      for receipt in receipts do
        let some claim ← control.atomically do return (← get).claims[receipt]?
          | throw (IO.userError "Unknown queue receipt")
        unless ← stop.isRequested do claim.settle queue failed
    | .release receipts => do
      for receipt in receipts do
        let some claim ← control.atomically do return (← get).claims[receipt]?
          | throw (IO.userError "Unknown queue receipt")
        claim.release queue
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
  let startBackground (action : IO Unit) : IO Unit := do
    let task ← IO.asTask action .dedicated
    background.modify (·.push task)
  try
    discard <| startBackground (do
      try
        let mut next := (← IO.monoMsNow) + 10000
        while !(← stop.isRequested) do
          if (← IO.monoMsNow) ≥ next then
            let claims ← control.atomically do return (← get).claims.toArray.map (·.2)
            discard <| Parallel.map ioSlots claims fun claim => claim.settled.atomically do
              unless ← get do queue.renew claim.delivery.receipt
            next := (← IO.monoMsNow) + 10000
          IO.sleep 50
      catch error => fail error)
    discard <| startBackground (do
      let mut next := 0
      while !(← stop.isRequested) do
        if (← IO.monoMsNow) ≥ next then
          report env queue plan.modules.size (← activity.atomically get)
          next := (← IO.monoMsNow) + 1000
        IO.sleep 50)
    discard <| startBackground (do
      try
        Prefetch.run queue stop ioSlots fun childStop value => do
          let execute : {β : Type} → Operation α β → IO β := fun op =>
            match op with
            | .cancelled => childStop.isRequested
            | .install m inputs warm => do
              if ← childStop.isRequested then throw (IO.userError "Prefetch cancelled")
              if warm then engine.prefetch childStop inputs else engine.prepare childStop m inputs
              if ← childStop.isRequested then throw (IO.userError "Prefetch cancelled")
            | op => handle op
          let outcome ← (runProgram execute noLaunch (prefetch settings value)).toBaseIO
          if let .error error := outcome then
            unless ← childStop.isRequested do throw error
      catch error => fail error)
    runProgram handle launch (program plan env.currentWorker.cpus)
    if let some error ← control.atomically do return (← get).error then throw error
    unless ← env.cancellation.isRequested do
      control.atomically (modify fun s => { s with stopped := true })
      for task in ← background.get do discard <| IO.wait task
      if let some error ← control.atomically do return (← get).error then throw error
      report env queue plan.modules.size "Finished"
  finally
    control.atomically (modify fun s => { s with stopped := true })
    try engine.cancel
    finally
      for task in ← tasks.get do discard <| IO.wait task
      for task in ← background.get do discard <| IO.wait task
      let claims ← control.atomically do return (← get).claims.toArray.map (·.2)
      discard <| Parallel.map ioSlots claims fun claim => do
        try claim.release queue catch _ => pure ()

end LeanBuild.Builders
