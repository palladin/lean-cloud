import LeanBuild.Model
import LeanCloudRuntime.Parallel

namespace LeanBuild.Builders
open Lean LeanCloud LeanCloudRuntime

def queueName := "lean-build/v6/modules"
def resultName (module : String) := "lean-build/v6/results/" ++ module

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
  let queue := env.queues.open queueName
  for offset in [:((roots.size + 99) / 100)] do
    queue.send ((roots.extract (offset * 100) ((offset + 1) * 100)).map fun m => ⟨m.name, toJson m.name⟩)

def results (env : Environment IO) (plan : Plan) : IO (Array BuildResult) :=
  Parallel.map (max 1 env.currentWorker.cpus) plan.modules fun m => do
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

/-- A few modules per CPU amortize Lake startup without hoarding the ready queue.
Receive returns immediately with whatever is available; it never waits to fill. -/
def batchSize (cpus : Nat) : Nat := min 100 (4 * max 1 cpus)

private structure Claim where
  delivery : WorkDelivery
  -- Serialize renewal with settlement, independently for each receipt.
  settled : Std.Mutex Bool

private def Claim.acknowledge (claim : Claim) (queue : WorkQueue IO) : IO Unit :=
  claim.settled.atomically do
    unless ← get do
      queue.acknowledge claim.delivery.receipt
      set true

private def Claim.release (claim : Claim) (queue : WorkQueue IO) : IO Unit :=
  claim.settled.atomically do
    unless ← get do
      queue.release claim.delivery.receipt
      set true

/-- One Lake batch at a time per worker, with bounded concurrent artifact IO.
The callback reports individual module completions while Lake keeps compiling.
Artifacts precede the immutable result; notifications precede ACK. Redelivery
therefore repairs an interrupted notification without rebuilding the module. -/
def run (env : Environment IO) (plan : Plan)
    (build : CancellationToken IO → Array Module → Array BuildResult →
      (BuildResult → IO Unit) → IO Unit) : IO Unit := do
  IO.ofExcept (validateModules plan.modules)
  let queue := env.queues.open queueName
  let state ← Std.Mutex.new ({} : State)
  let width := max 1 env.currentWorker.cpus
  let byName := plan.modules.foldl (fun map m => map.insert m.name m) ({} : Std.HashMap String Module)
  let dependents := plan.modules.foldl (fun map m => m.imports.foldl (fun map dep =>
    map.insert dep ((map[dep]?.getD #[]).push m)) map) ({} : Std.HashMap String (Array Module))
  let notify (name : String) : IO Unit := do
    let mut ready := #[]
    for m in dependents[name]?.getD #[] do
      let mut available := true
      for parent in m.imports do
        if (← read env state parent).isNone then available := false; break
      if available then ready := ready.push ⟨m.name, toJson m.name⟩
    for offset in [:((ready.size + 99) / 100)] do
      queue.send (ready.extract (offset * 100) ((offset + 1) * 100))
  repeat
    if ← env.cancellation.isRequested then break
    let deliveries ← queue.receive (batchSize width)
    if deliveries.isEmpty then
      -- Notifications precede ACK: empty INCLUDING leases means quiescence.
      if ← queue.isIdle then break
      env.progress.report "lake" { message := "Waiting for dependencies" }
      IO.sleep 250
      continue
    let claims ← deliveries.mapM fun delivery => return { delivery, settled := ← Std.Mutex.new false : Claim }
    let finished ← IO.mkRef false
    let leaseLost ← IO.mkRef false
    let renewal ← IO.asTask (do
      let mut next := (← IO.monoMsNow) + 10000
      while !(← finished.get) do
        if (← IO.monoMsNow) ≥ next then
          try
            discard <| Parallel.map width claims fun claim => claim.settled.atomically do
              unless ← get do queue.renew claim.delivery.receipt
          catch error => leaseLost.set true; throw error
          next := (← IO.monoMsNow) + 10000
        IO.sleep 50) .dedicated
    let stop : CancellationToken IO := ⟨do return (← env.cancellation.isRequested) || (← leaseLost.get)⟩
    try
      -- A queue may deliver the same key more than once. Build it once, then
      -- settle every receipt, including duplicates, after durable publication.
      let mut grouped : Std.HashMap String (Array Claim) := {}
      let mut queued := #[]
      for claim in claims do
        let name : String ← IO.ofExcept (fromJson? claim.delivery.value)
        let some m := byName[name]? | throw (IO.userError "Unknown queued module")
        unless grouped.contains name do queued := queued.push m
        grouped := grouped.insert name ((grouped[name]?.getD #[]).push claim)
      let settle (name : String) : IO Unit := do
        if ← stop.isRequested then return
        notify name
        for claim in grouped[name]?.getD #[] do claim.acknowledge queue
      let existing ← Parallel.map width queued fun m => do
        if (← read env state m.name).isSome then settle m.name; return none
        return some m
      let targets := existing.filterMap id
      let parents := targets.foldl (fun set m => m.imports.foldl (·.insert ·) set) ({} : Std.HashSet String)
      discard <| Parallel.map width parents.toArray (read env state)
      let outcomes ← Parallel.map width targets fun m => do
        let parents ← m.imports.mapM (read env state)
        if parents.any Option.isNone then return none
        if parents.any (fun r => r.any (·.status != .built)) then
          unless ← stop.isRequested do
            let result ← publishResult env { name := m.name, status := .blocked, message := "A prerequisite failed" }
            state.atomically (modify fun s => { s with results := s.results.insert m.name result })
            settle m.name
          return none
        return some m
      let targets := outcomes.filterMap id
      unless targets.isEmpty || (← stop.isRequested) do
        let inputs ← Parallel.map width (dependencies plan.modules targets) fun dep => do
          let some result ← read env state dep.name | throw (IO.userError "Missing transitive prerequisite")
          return result
        let requested := targets.foldl (fun set m => set.insert m.name) ({} : Std.HashSet String)
        let reported ← Std.Mutex.new ({} : Std.HashSet String)
        build stop targets inputs fun outcome => do
          unless requested.contains outcome.name do throw (IO.userError "Builder returned an unrequested module")
          reported.atomically do
            if (← get).contains outcome.name then throw (IO.userError "Builder returned a module twice")
            modify (·.insert outcome.name)
          if ← stop.isRequested then return
          let result ← publishResult env outcome
          state.atomically (modify fun s => { s with results := s.results.insert outcome.name result })
          settle outcome.name
          let count ← state.atomically do return (← get).results.size
          env.progress.report "build" { message := "Committed modules known to this worker", completed := count, total := some plan.modules.size }
        unless ← stop.isRequested do
          unless (← reported.atomically get).size == targets.size do
            throw (IO.userError "Builder omitted module results")
    finally
      finished.set true
      let renewed ← IO.wait renewal
      discard <| Parallel.map width claims fun claim => do
        try claim.release queue catch _ => pure ()
      -- Renewal transport errors are ordinary exec failures, not implicit retries.
      IO.ofExcept renewed
  env.progress.report "lake" { message := if ← env.cancellation.isRequested then "Stopped" else "Finished" }

end LeanBuild.Builders
