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
  active : Std.HashSet String := {}

/-- Only committed successes/failures are cached. Missing results may become
available at any time, so a negative lookup is never retained. -/
private def read (env : Environment IO) (state : Std.Mutex State) (name : String) : IO (Option BuildResult) := do
  if let some result ← state.atomically do return (← get).results[name]? then return some result
  let result ← readResult env name
  if let some result := result then
    state.atomically (modify fun s => { s with results := s.results.insert name result })
  return result

private def dependencies (modules : Array Module) (target : Module) : Array Module := Id.run do
  let mut needed := target.imports.foldl (·.insert ·) ({} : Std.HashSet String)
  for m in modules.reverse do
    if needed.contains m.name then needed := m.imports.foldl (·.insert ·) needed
  return modules.filter (needed.contains ·.name)

/-- One cloud command owns a persistent local pool. Artifacts precede the
immutable result; dependent notifications precede ACK, including on redelivery.
Thus a crash in any gap repeats harmless publication instead of losing work. -/
def run (env : Environment IO) (plan : Plan)
    (build : Nat → CancellationToken IO → Module → Array BuildResult → IO BuildResult) : IO Unit := do
  IO.ofExcept (validateModules plan.modules)
  let queue := env.queues.open queueName
  let state ← Std.Mutex.new ({} : State)
  let abort ← IO.mkRef false
  let byName := plan.modules.foldl (fun map m => map.insert m.name m) ({} : Std.HashMap String Module)
  let dependents := plan.modules.foldl (fun map m => m.imports.foldl (fun map dep =>
    map.insert dep ((map[dep]?.getD #[]).push m)) map) ({} : Std.HashMap String (Array Module))
  let cancelled : IO Bool := do return (← abort.get) || (← env.cancellation.isRequested)
  let isReady (m : Module) : IO Bool := do
    for parent in m.imports do
      if (← read env state parent).isNone then return false
    return true
  let notify (name : String) : IO Unit := do
    let mut ready := #[]
    for m in dependents[name]?.getD #[] do
      if ← isReady m then ready := ready.push ⟨m.name, toJson m.name⟩
    for offset in [:((ready.size + 99) / 100)] do
      queue.send (ready.extract (offset * 100) ((offset + 1) * 100))
  discard <| Parallel.map env.currentWorker.cpus (Array.range (max 1 env.currentWorker.cpus)) fun lane => do
    try
      repeat
        if ← cancelled then return ()
        let batch ← queue.receive 1
        if batch.isEmpty then
          -- Roots were seeded before builders started. Every notification is
          -- sent before ACK, so an empty queue INCLUDING leases is quiescent.
          -- The final collection still requires every planned module result.
          if ← queue.isIdle then
            env.progress.report s!"builder-{lane + 1}" { message := "Finished" }
            return ()
          env.progress.report s!"builder-{lane + 1}" { message := "Waiting for dependencies" }
          IO.sleep 250
          continue
        for delivery in batch do
          let name : String ← IO.ofExcept (fromJson? delivery.value)
          let some m := byName[name]? | throw (IO.userError "Unknown queued module")
          let acquired ← state.atomically do
            let s ← get
            if s.active.contains name then return false
            set { s with active := s.active.insert name }
            return true
          unless acquired do
            queue.release delivery.receipt
            IO.sleep 50
            continue
          let settled ← IO.mkRef false
          let finished ← IO.mkRef false
          let leaseLost ← IO.mkRef false
          let renewal ← IO.asTask (do
            let mut next := (← IO.monoMsNow) + 10000
            while !(← finished.get) do
              if (← IO.monoMsNow) ≥ next then
                try queue.renew delivery.receipt
                catch error => leaseLost.set true; throw error
                next := (← IO.monoMsNow) + 10000
              IO.sleep 50) .dedicated
          let stop : CancellationToken IO := ⟨do return (← cancelled) || (← leaseLost.get)⟩
          try
            let existing ← read env state name
            if existing.isNone then
              let parents ← m.imports.mapM (read env state)
              if parents.any Option.isNone then continue
              env.progress.report s!"builder-{lane + 1}" { message := name }
              let outcome ← if parents.any (fun r => r.any (·.status != .built)) then
                pure { name, status := .blocked, message := "A prerequisite failed" }
              else do
                let inputs ← (dependencies plan.modules m).mapM fun dep => do
                  let some result ← read env state dep.name | throw (IO.userError "Missing transitive prerequisite")
                  return result
                build lane stop m inputs
              if ← stop.isRequested then continue
              unless outcome.name == name do throw (IO.userError "Builder returned a different module")
              let result ← publishResult env outcome
              state.atomically (modify fun s => { s with results := s.results.insert name result })
            if ← stop.isRequested then continue
            notify name
            queue.acknowledge delivery.receipt
            settled.set true
            let count ← state.atomically do return (← get).results.size
            env.progress.report "build" { message := "Committed modules known to this builder", completed := count, total := some plan.modules.size }
          finally
            finished.set true
            let renewed ← IO.wait renewal
            state.atomically (modify fun s => { s with active := s.active.erase name })
            unless ← settled.get do
              try queue.release delivery.receipt catch _ => pure ()
              -- A transport failure is an ordinary exec failure, not an
              -- implicit retry. After ACK, a racing renewal may see no lease.
              IO.ofExcept renewed
      return ()
    catch error => abort.set true; throw error
  env.progress.report "build" { message := if ← cancelled then "Stopped" else "Builder finished" }

end LeanBuild.Builders
