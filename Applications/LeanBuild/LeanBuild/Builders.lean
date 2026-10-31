import LeanBuild.Model
import LeanBuild.Prefetch
import LeanCloudRuntime.Parallel
import Std.Sync.Channel

namespace LeanBuild.Builders
open Lean LeanCloud LeanCloudRuntime

def queueName := "lean-build/v7/modules"
def resultName (module : String) := "lean-build/v7/results/" ++ module

/-- Network latency can be overlapped without consuming a compiler CPU slot. -/
def ioConcurrency (cpus : Nat) : Nat := max 4 (min 32 (4 * cpus))

/-- Longest chain from each module to an output, including the module itself.
The plan is topological: propagate each score to its imports in one reverse pass. -/
def priorities (modules : Array Module) : Std.HashMap String Nat :=
  modules.foldr (fun m scores =>
    let score := max 1 (scores[m.name]?.getD 0)
    m.imports.foldl (fun scores name => scores.insert name (max (score + 1) (scores[name]?.getD 0)))
      (scores.insert m.name score)) {}

private def item (scores : Std.HashMap String Nat) (m : Module) : WorkItem :=
  { key := m.name, value := toJson m.name, priority := scores[m.name]?.getD 1 }

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

def seed (env : Environment IO) (plan : Plan) : IO Unit := do
  IO.ofExcept (validateModules plan.modules)
  let roots := plan.modules.filter (·.imports.isEmpty)
  let scores := priorities plan.modules
  let queue := env.queues.open queueName
  for offset in [:((roots.size + 99) / 100)] do
    queue.send ((roots.extract (offset * 100) ((offset + 1) * 100)).map (item scores))

def results (env : Environment IO) (plan : Plan) : IO (Array BuildResult) :=
  Parallel.map (ioConcurrency env.currentWorker.cpus) plan.modules fun m => do
    let some result ← readResult env m.name | throw (IO.userError s!"Missing module result: {m.name}")
    return result

private structure State where
  results : Std.HashMap String BuildResult := {}

/-- Only committed successes/failures are cached. Missing results may become
available at any time, so a negative lookup is never retained. -/
private def read (env : Environment IO) (state : Std.Mutex State) (name : String) : IO (Option BuildResult) := do
  if let some result ← state.atomically do return (← get).results[name]? then return some result
  let result ← readResult env name
  if let some result := result then
    state.atomically (modify fun s => { s with results := s.results.insert name result })
  return result

/-- Union of transitive prerequisites, in the plan's topological order. -/
private def dependencies (modules targets : Array Module) : Array Module := Id.run do
  let mut needed := targets.foldl (fun set m => m.imports.foldl (·.insert ·) set) ({} : Std.HashSet String)
  for m in modules.reverse do
    if needed.contains m.name then needed := m.imports.foldl (·.insert ·) needed
  return modules.filter (needed.contains ·.name)


/-- Reserve headroom for scheduling, hashing and compression. This is a budget,
not CPU affinity. A single-CPU worker still has one compilation slot. -/
def compilerSlots (cpus : Nat) := max 1 (cpus - 1)

/-- One persistent compiler session. Only the coordinator calls submit/poll.
Preparation and publication run in separate bounded pools. -/
structure Engine (α : Type) where
  prefetch : CancellationToken IO → Array BuildResult → IO Unit := fun _ _ => pure ()
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

private structure Work where
  mod : Module
  claims : Std.Mutex (Array Claim)

private inductive Event where
  | received (claims : Array Claim) (idle : Bool)
  | prepared (name : String)
  | settled (name : String)

private structure Control where
  stopped : Bool := false
  error : Option IO.Error := none
  claims : Array Claim := #[]

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

/-- A rolling pipeline: receiving, restoring, compiling and publishing overlap.
A compilation completion frees its slot BEFORE publication. Leases remain live
through publication and successor notification. No group barrier exists. -/
def run (env : Environment IO) (plan : Plan) (engine : Engine α) : IO Unit := do
  IO.ofExcept (validateModules plan.modules)
  let queue := env.queues.open queueName
  let cache ← Std.Mutex.new ({} : State)
  let reads ← Parallel.Limit.new (ioConcurrency env.currentWorker.cpus)
  let read := fun name => reads.run (read env cache name)
  let control ← Std.Mutex.new ({} : Control)
  let stop : CancellationToken IO := ⟨do
    return (← env.cancellation.isRequested) || (← control.atomically do return (← get).stopped)⟩
  let events ← Std.Channel.new (α := Event)
  let tasks ← IO.mkRef (#[] : Array (Task (Except IO.Error Unit)))
  let spawn (action : IO Unit) : IO Unit := do
    let task ← IO.asTask (do
      try action catch error =>
        control.atomically (modify fun s => { s with stopped := true, error := s.error.orElse (fun _ => some error) })) .dedicated
    tasks.modify (·.push task)
  let slots := compilerSlots env.currentWorker.cpus
  let ioSlots := max 2 (min 8 env.currentWorker.cpus)
  let capacity := 3 * slots + ioSlots
  let activity ← Std.Mutex.new "Starting Lake"
  let byName := plan.modules.foldl (fun map m => map.insert m.name m) ({} : Std.HashMap String Module)
  let scores := priorities plan.modules
  let inputs (m : Module) : IO (Array BuildResult) :=
    Parallel.map (ioConcurrency env.currentWorker.cpus) (dependencies plan.modules #[m]) fun dep => do
      let some result ← read dep.name | throw (IO.userError "Missing transitive prerequisite")
      return result
  let dependents := plan.modules.foldl (fun map m => m.imports.foldl (fun map dep =>
    map.insert dep ((map[dep]?.getD #[]).push m)) map) ({} : Std.HashMap String (Array Module))
  let settle (work : Work) (result : BuildResult) : IO Unit := do
    if ← stop.isRequested then return
    cache.atomically (modify fun s => { s with results := s.results.insert result.name result })
    let candidates := dependents[result.name]?.getD #[]
    -- Stop checking a candidate as soon as one prerequisite is missing. Eagerly
    -- reading every parent of every dependent adds IO on the publication path.
    let ready ← Parallel.map (ioConcurrency env.currentWorker.cpus) candidates fun m => do
      if ← m.imports.allM (fun name => return (← read name).isSome) then
        return some (item scores m)
      return none
    let ready := ready.filterMap id
    for offset in [:((ready.size + 99) / 100)] do
      queue.send (ready.extract (offset * 100) ((offset + 1) * 100))
    work.claims.atomically do
      for claim in ← get do claim.settle queue (result.status != .built)
    events.sync.send (.settled work.mod.name)
  let prepare (work : Work) : IO Unit := do
    if ← stop.isRequested then return
    if let some result ← read work.mod.name then
      settle work result
      return
    let parents ← Parallel.map (ioConcurrency env.currentWorker.cpus) work.mod.imports read
    if parents.any Option.isNone then
      -- An early delivery remains eligible for a later attempt.
      work.claims.atomically do
        for claim in ← get do claim.release queue
      events.sync.send (.settled work.mod.name)
    else if parents.any (fun r => r.any (·.status != .built)) then
      if ← stop.isRequested then return
      settle work (← publishResult env {
        name := work.mod.name, status := .blocked, message := "A prerequisite failed" })
    else
      engine.prepare stop work.mod (← inputs work.mod)
      unless ← stop.isRequested do events.sync.send (.prepared work.mod.name)
  -- Renewal is independent of telemetry and compiler activity.
  let renewer ← IO.asTask (do
    try
      let mut next := (← IO.monoMsNow) + 10000
      while !(← stop.isRequested) do
        if (← IO.monoMsNow) ≥ next then
          let claims ← control.atomically do return (← get).claims
          discard <| Parallel.map ioSlots claims fun claim => claim.settled.atomically do
            unless ← get do queue.renew claim.delivery.receipt
          next := (← IO.monoMsNow) + 10000
        IO.sleep 50
    catch error =>
      control.atomically (modify fun s => { s with stopped := true, error := s.error.orElse (fun _ => some error) })) .dedicated
  let reporter ← IO.asTask (do
    let mut next := 0
    while !(← stop.isRequested) do
      if (← IO.monoMsNow) ≥ next then
        report env queue plan.modules.size (← activity.atomically get)
        next := (← IO.monoMsNow) + 1000
      IO.sleep 50) .dedicated
  -- Follow upcoming work, not past completions. Peek never claims a module;
  -- foreground preparation shares the same cached, in-flight artifact transfers.
  let prefetcher ← IO.asTask (do
    try
      Prefetch.run queue stop ioSlots fun stop value => do
        if ← stop.isRequested then return
        let name ← IO.ofExcept (fromJson? (α := String) value)
        let some m := byName[name]? | throw (IO.userError "Unknown queued module")
        if (← read name).isSome then return
        let parents ← Parallel.map (ioConcurrency env.currentWorker.cpus) m.imports read
        -- Failed/early deliveries are handled by the owning builder; there are
        -- no valid artifacts to warm until every prerequisite has succeeded.
        unless parents.all (fun result => result.any (·.status == .built)) do return
        engine.prefetch stop (← inputs m)
    catch error =>
      control.atomically (modify fun s => { s with stopped := true, error := s.error.orElse (fun _ => some error) })) .dedicated
  try
    let mut work : Std.HashMap String Work := {}
    let mut waiting : Array String := #[]
    let mut restoring : Std.HashSet String := {}
    let mut ready : Array String := #[]
    let mut compiling : Std.HashSet String := {}
    let mut completed : Array (String × α) := #[]
    let mut publishing : Std.HashSet String := {}
    let mut receiving := false
    let mut idle := false
    let mut nextReceive := 0
    repeat
      if ← stop.isRequested then break
      -- Finished tasks have already delivered their events (or recorded errors).
      tasks.set (← (← tasks.get).filterM fun task => return !(← IO.hasFinished task))
      -- Bound the registry to outstanding receipts, even on very large DAGs.
      control.atomically do
        let s ← get
        let claims ← s.claims.filterM fun c => return !(← c.settled.atomically get)
        set { s with claims }
      while let some event ← events.tryRecv do
        match event with
        | .received claims empty =>
          receiving := false
          idle := empty
          if claims.isEmpty then nextReceive := (← IO.monoMsNow) + 100
          for claim in claims do
            let name : String ← IO.ofExcept (fromJson? claim.delivery.value)
            let some m := byName[name]? | throw (IO.userError "Unknown queued module")
            if let some existing := work[name]? then
              existing.claims.atomically (modify (·.push claim))
            else
              work := work.insert name ⟨m, ← Std.Mutex.new #[claim]⟩
              waiting := waiting.push name
        | .prepared name =>
          unless restoring.contains name do throw (IO.userError "Unexpected preparation")
          restoring := restoring.erase name
          ready := ready.push name
        | .settled name =>
          -- A duplicate receipt can arrive during settlement. Settle any late
          -- receipts using the same committed result on the next pass.
          if let some w := work[name]? then
            let unfinished ← w.claims.atomically do
              (← get).anyM fun c => return !(← c.settled.atomically get)
            if unfinished then
              spawn (prepare w)
              continue
          work := work.erase name
          restoring := restoring.erase name
          publishing := publishing.erase name
      for (name, result) in ← engine.poll do
        unless compiling.contains name do throw (IO.userError "Unknown or duplicate Lake completion")
        compiling := compiling.erase name
        completed := completed.push (name, result)
      while compiling.size < slots && !ready.isEmpty do
        let name := ready[0]!
        ready := ready.extract 1 ready.size
        let some w := work[name]? | throw (IO.userError "Missing prepared work")
        engine.submit w.mod
        compiling := compiling.insert name
      while publishing.size < ioSlots && !completed.isEmpty do
        let some (name, value) := completed[0]? | break
        completed := completed.extract 1 completed.size
        let some w := work[name]? | throw (IO.userError "Missing compiled work")
        publishing := publishing.insert name
        spawn do
          let result ← engine.publish stop w.mod value
          unless result.name == name do throw (IO.userError "Builder returned an unrequested module")
          unless ← stop.isRequested do settle w (← publishResult env result)
      while restoring.size < ioSlots && !waiting.isEmpty do
        let name := waiting[0]!
        waiting := waiting.extract 1 waiting.size
        let some w := work[name]? | throw (IO.userError "Missing received work")
        restoring := restoring.insert name
        spawn (prepare w)
      if idle && work.isEmpty && !receiving then break
      -- Preparation reserves a compiler slot; do not lease an extra local
      -- backlog while other workers could run it. Artifact prefetching is
      -- independent, and publication does not occupy a compiler slot.
      let admission := slots - (waiting.size + restoring.size + ready.size + compiling.size)
      if !receiving && admission > 0 && work.size < capacity && (← IO.monoMsNow) ≥ nextReceive then
        receiving := true
        let count := min 100 (min admission (capacity - work.size))
        spawn do
          let deliveries ← queue.receive count
          let claims ← deliveries.mapM fun d => return (⟨d, ← Std.Mutex.new false⟩ : Claim)
          control.atomically (modify fun s => { s with claims := s.claims ++ claims })
          let idle ← if claims.isEmpty then queue.isIdle else pure false
          events.sync.send (.received claims idle)
      activity.atomically (set s!"compiling {compiling.size}/{slots} · restoring {restoring.size} · ready {ready.size} · publishing {publishing.size + completed.size}")
      IO.sleep 10
    if let some error ← control.atomically do return (← get).error then throw error
    unless ← env.cancellation.isRequested do
      engine.finish
      control.atomically (modify fun s => { s with stopped := true })
      discard <| IO.wait prefetcher
      if let some error ← control.atomically do return (← get).error then throw error
      discard <| IO.wait reporter
      report env queue plan.modules.size "Finished"
  finally
    control.atomically (modify fun s => { s with stopped := true })
    engine.cancel
    for task in ← tasks.get do discard <| IO.wait task
    discard <| IO.wait renewer
    discard <| IO.wait reporter
    discard <| IO.wait prefetcher
    let claims ← control.atomically do return (← get).claims
    discard <| Parallel.map ioSlots claims fun claim => do
      try claim.release queue catch _ => pure ()

end LeanBuild.Builders
