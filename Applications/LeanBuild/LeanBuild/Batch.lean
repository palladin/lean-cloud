import LeanBuild.Model

namespace LeanBuild
open LeanCloud

/-- Partition a topological frontier into bounded jobs, weighted by advertised
CPU capacity. Continue unbranched dependency chains locally; stop at fan-out when
other workers can help, and at cross-job dependencies. A single worker can keep
an entire bounded subgraph local.
The callback's recorded environment makes this partition stable during replay. -/
def partition (pending : Array Module) (done : Array BuildResult)
    (environment : Environment) (limit : Nat) : Array (Array Module) := Id.run do
  let workers := if environment.workers.isEmpty then #[environment.currentWorker] else environment.workers
  let mut batches := workers.map fun _ => (#[] : Array Module)
  let largest := workers.foldl (fun n worker => max n worker.cpus) 1
  let limits := workers.map fun worker =>
    max 1 ((max 1 limit * max 1 worker.cpus + largest - 1) / largest)
  let completed := done.foldl (fun set r => set.insert r.name) ({} : Std.HashSet String)
  let consumers := pending.foldl (fun counts m => m.imports.foldl
    (fun counts dep => counts.insert dep (counts[dep]?.getD 0 + 1)) counts) ({} : Std.HashMap String Nat)
  let mut owners : Std.HashMap String Nat := {}
  for m in pending do
    let deps := m.imports.filter (!completed.contains ·)
    let mut selected : Option Nat := none
    if deps.isEmpty then
      for i in [:batches.size] do
        if batches[i]!.size ≥ limits[i]! then continue
        match selected with
        | none => selected := some i
        | some j =>
          -- Give ready work to every batch before weighting additional work.
          -- A small frontier must not collapse onto one nominally faster slot.
          if (batches[i]!.isEmpty && !batches[j]!.isEmpty) ||
              (batches[i]!.isEmpty == batches[j]!.isEmpty &&
                (batches[i]!.size + 1) * max 1 workers[j]!.cpus <
                (batches[j]!.size + 1) * max 1 workers[i]!.cpus) then selected := some i
    else if let some owner := owners[deps[0]!]? then
      if deps.all (fun dep => owners[dep]? == some owner &&
          (workers.size == 1 || consumers[dep]?.getD 0 == 1)) &&
          batches[owner]!.size < limits[owner]! then selected := some owner
    if let some i := selected then
      batches := batches.modify i (·.push m)
      owners := owners.insert m.name i
  return batches.filter (!·.isEmpty)

/-- Failure propagation needs no cloud jobs. Topological order also removes
transitively blocked descendants in this pass. -/
def skipBlocked (pending : Array Module) (done : Array BuildResult) : Array Module × Array BuildResult := Id.run do
  let mut results := done
  let mut failed := done.foldl (fun set r => if r.status == .built then set else set.insert r.name)
    ({} : Std.HashSet String)
  let mut remaining := #[]
  for m in pending do
    if m.imports.any failed.contains then
      results := results.push { name := m.name, status := .blocked, message := "A prerequisite failed" }
      failed := failed.insert m.name
    else remaining := remaining.push m
  return (remaining, results)

end LeanBuild
