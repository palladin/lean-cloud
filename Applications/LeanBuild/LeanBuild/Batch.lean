import LeanBuild.Model

namespace LeanBuild
open LeanCloud

private abbrev Names := Std.HashSet String
private abbrev Jobs := Array (Array Module)
private abbrev Consumers := Std.HashMap String (Array String)
private abbrev Affinity := Std.HashMap String (Array Nat)

private def moduleNames (modules : Array Module) (initial : Names := {}) : Names :=
  modules.foldl (fun names m => names.insert m.name) initial

/-- Use every advertised CPU; a missing pool falls back to the executing worker. -/
def workerCpus (environment : Environment) : Array Nat :=
  let workers := if environment.workers.isEmpty then #[environment.currentWorker] else environment.workers
  workers.map (max 1 ·.cpus)

/-- Longest remaining dependency paths first, with input order breaking ties.
The input is topological. Each module initially costs one CPU time unit. -/
def criticalOrder (modules : Array Module) : Array Module :=
  let ranks := modules.reverse.foldl (fun ranks m =>
    let rank := max 1 (ranks[m.name]?.getD 0)
    m.imports.foldl (fun ranks dep =>
      ranks.insert dep (max (ranks[dep]?.getD 0) (rank + 1))) (ranks.insert m.name rank))
    ({} : Std.HashMap String Nat)
  (modules.zipIdx.qsort fun (a, i) (b, j) =>
    let ra := ranks[a.name]?.getD 0
    let rb := ranks[b.name]?.getD 0
    ra > rb || (ra == rb && i < j)).map (·.1)

/-- Choose an eligible worker, keeping the earlier index on ties. -/
private def bestWorker (count : Nat) (eligible : Nat → Bool) (better : Nat → Nat → Bool) : Option Nat :=
  (Array.range count).foldl (fun best i =>
    if !eligible i then best
    else match best with
      | none => some i
      | some j => if better i j then some i else best) none

private def consumersOf (modules : Array Module) : Consumers :=
  modules.foldl (fun consumers m => m.imports.foldl (fun consumers dep =>
    consumers.insert dep ((consumers[dep]?.getD #[]).push m.name)) consumers) {}

/-- One unit of work per CPU. Affinity counts inputs already placed on each
worker, so future joins can remain local. -/
private structure Selection where
  jobs : Jobs
  affinity : Affinity

private def Selection.assign (consumers : Consumers) (selection : Selection)
    (worker : Nat) (m : Module) : Selection :=
  let empty := selection.jobs.map fun _ => 0
  { jobs := selection.jobs.modify worker (·.push m)
    affinity := (consumers[m.name]?.getD #[]).foldl (fun affinity child =>
      affinity.insert child ((affinity[child]?.getD empty).modify worker (· + 1))) selection.affinity }

/-- First place work tied to a worker by a local prerequisite. Then place free
work by shared consumers, breaking ties by CPU load. Cross-worker joins wait
for the next round, when their prerequisites have been published. -/
private def selectSlot (ready : Array Module) (owners : Std.HashMap String Nat)
    (consumers : Consumers) (cpus slots : Array Nat) (affinity : Affinity) : Selection :=
  let pinned := ready.foldl (fun selection m =>
    match (m.imports.filterMap (owners[·]?)).toList.eraseDups with
    | [i] => if selection.jobs[i]!.size < slots[i]! then selection.assign consumers i m else selection
    | _ => selection) { jobs := cpus.map fun _ => #[], affinity }
  let flexible := ready.filter fun m => m.imports.all fun dep => !owners.contains dep
  let rec placeFree : List Module → Selection → Selection
    | [], selection => selection
    | m :: rest, selection =>
      let empty := cpus.map fun _ => 0
      let shared := (consumers[m.name]?.getD #[]).foldl (fun counts child =>
        counts.zipWith (· + ·) (selection.affinity[child]?.getD empty)) empty
      let target := bestWorker cpus.size
        (fun i => selection.jobs[i]!.size < slots[i]!)
        (fun i j => shared[i]! > shared[j]! || (shared[i]! == shared[j]! &&
          selection.jobs[i]!.size * cpus[j]! < selection.jobs[j]!.size * cpus[i]!))
      match target with
      | none => selection
      | some i => placeFree rest (selection.assign consumers i m)
  placeFree flexible.toList pinned

private structure Round where
  jobs : Jobs
  available : Names
  owners : Std.HashMap String Nat := {}
  affinity : Affinity := {}
  remaining : Array Module

private def Round.append (round : Round) (selection : Selection) : Round :=
  let available := moduleNames selection.jobs.flatten round.available
  { jobs := round.jobs.zipWith (· ++ ·) selection.jobs
    available
    owners := selection.jobs.zipIdx.foldl (fun owners (job, i) =>
      job.foldl (fun owners m => owners.insert m.name i) owners) round.owners
    affinity := selection.affinity
    remaining := round.remaining.filter (!available.contains ·.name) }

/-- Fill successive CPU slots while prerequisites stay local. Stop before a
slot that would waste otherwise usable CPUs; publishing the round frees its
dependents to run elsewhere. Keep empty jobs for worker/CPU accounting. -/
private def fillRound (pending : Array Module) (completed : Names)
    (cpus : Array Nat) (limit : Nat) : Jobs :=
  let cpus := cpus.map fun n => if limit == 0 then n else min n limit
  let total := cpus.foldl (· + ·) 0
  let consumers := consumersOf pending
  let rec fill : Nat → Round → Jobs
    | 0, round => round.jobs
    | steps + 1, round =>
      let ready := round.remaining.filter fun m => m.imports.all round.available.contains
      if ready.isEmpty then round.jobs else
      let slots := cpus.mapIdx fun i n => if limit == 0 then n else min n (limit - round.jobs[i]!.size)
      let selection := selectSlot ready round.owners consumers cpus slots round.affinity
      let occupied := selection.jobs.foldl (fun n job => n + job.size) 0
      if occupied < min total ready.size then round.jobs
      else fill steps (round.append selection)
  -- Every accepted slot removes at least one module.
  fill pending.size { jobs := cpus.map fun _ => #[], available := completed, remaining := pending }

/-- Unit-cost duration of one job; imports outside the job are already built.
Use the same module priority for both separate and merged candidates. -/
private def jobTicks (ordered : Array Module) (cpus : Nat) : Nat :=
  let members := moduleNames ordered
  let rec count : Nat → Names → Array Module → Nat → Nat
    | 0, _, _, ticks => ticks
    | steps + 1, completed, remaining, ticks =>
      if remaining.isEmpty then ticks else
      let ready := (remaining.filter fun m => m.imports.all fun dep =>
        !members.contains dep || completed.contains dep).extract 0 cpus
      let completed := moduleNames ready completed
      count steps completed (remaining.filter (!completed.contains ·.name)) (ticks + 1)
  count ordered.size {} ordered 0

private def roundTicks (ordered : Array Module) (cpus : Array Nat) (jobs : Jobs) : Nat :=
  (jobs.mapIdx fun i job =>
    let members := moduleNames job
    jobTicks (ordered.filter fun m => members.contains m.name) cpus[i]!).foldl max 0

private structure Components where
  groups : Jobs := #[]
  owners : Std.HashMap String Nat := {}

private def Components.merge (components : Components) (target source : Nat) : Components :=
  if target == source then components else
  let moved := components.groups[source]!
  { groups := (components.groups.modify target (· ++ moved)).set! source #[]
    owners := moved.foldl (fun owners m => owners.insert m.name target) components.owners }

/-- A module connects all components containing its prerequisites. Merge into
the largest one to minimize copying; vacant component indices stay stable. -/
private def Components.add (components : Components) (m : Module) : Components :=
  let dependencies := (m.imports.filterMap (components.owners[·]?)).toList.eraseDups
  match dependencies with
  | [] =>
    { groups := components.groups.push #[m]
      owners := components.owners.insert m.name components.groups.size }
  | first :: rest =>
    let target := rest.foldl (fun best j =>
      if components.groups[j]!.size > components.groups[best]!.size then j else best) first
    let merged := dependencies.foldl (fun parts j => parts.merge target j) components
    { groups := merged.groups.modify target (·.push m)
      owners := merged.owners.insert m.name target }

/-- Removing a barrier requires each connected dependency component to stay
in one job. Place the largest components first on the least loaded CPU capacity.
An explicit job cap can make this impossible. -/
private def pack (ordered : Array Module) (cpus : Array Nat) (limit : Nat) : Option Jobs :=
  let components := ordered.foldl Components.add {}
  let largestFirst := (components.groups.zipIdx.filter (!·.1.isEmpty)).qsort fun (a, i) (b, j) =>
    a.size > b.size || (a.size == b.size && i < j)
  let place (jobs : Jobs) (component : Array Module) : Option Jobs :=
    let target := bestWorker cpus.size
      (fun i => limit == 0 || jobs[i]!.size + component.size ≤ limit)
      (fun i j => (jobs[i]!.size + component.size) * cpus[j]! <
        (jobs[j]!.size + component.size) * cpus[i]!)
    target.map fun i => jobs.modify i (· ++ component)
  let packed := largestFirst.foldlM (fun jobs (component, _) => place jobs component) (cpus.map fun _ => #[])
  packed.map fun jobs => jobs.map fun job =>
    let members := moduleNames job
    ordered.filter fun m => members.contains m.name

/-- Keep merging following rounds while their combined compute time does not
increase. A failed or slower merge leaves the last accepted plan unchanged. -/
private def mergeRounds (ordered : Array Module) (completed : Names)
    (cpus : Array Nat) (limit : Nat) (first : Jobs) : Jobs :=
  let rec merge : Nat → Jobs → Nat → Jobs
    | 0, jobs, _ => jobs
    | steps + 1, jobs, cost =>
      let chosen := moduleNames jobs.flatten
      let available := moduleNames jobs.flatten completed
      let remaining := ordered.filter (!available.contains ·.name)
      if remaining.isEmpty then jobs else
      let next := fillRound remaining available cpus limit
      if next.all (·.isEmpty) then jobs else
      let members := moduleNames next.flatten chosen
      match pack (ordered.filter fun m => members.contains m.name) cpus limit with
      | none => jobs
      | some combined =>
        let combinedCost := roundTicks ordered cpus combined
        if combinedCost > cost + roundTicks ordered cpus next then jobs
        else merge steps combined combinedCost
  -- Each successful merge adds at least one module to the current round.
  merge ordered.size first (roundTicks ordered cpus first)

/-- Prioritize long dependency paths, fill worker jobs, then remove barriers
that do not improve modeled compute time. No fixed worker count, desired round
count or utilization threshold is used.

There is one slot per advertised worker; the caller omits empty slots. Costs
assume one CPU time unit per module, not measured compilation or transfer times.
This is a deterministic heuristic, not an optimality or placement guarantee. -/
def partition (pending : Array Module) (done : Array BuildResult)
    (environment : Environment) (limit : Nat) : Array (Array Module) :=
  let cpus := workerCpus environment
  let ordered := criticalOrder pending
  let completed := done.foldl (fun names r => names.insert r.name) ({} : Names)
  let first := fillRound ordered completed cpus limit
  mergeRounds ordered completed cpus limit first

/-- Failure propagation needs no cloud jobs. Topological order also removes
transitively blocked descendants in this pass. -/
def skipBlocked (pending : Array Module) (done : Array BuildResult) : Array Module × Array BuildResult :=
  let failed := done.foldl (fun names r => if r.status == .built then names else names.insert r.name) ({} : Names)
  let (remaining, results, _) := pending.foldl (fun (remaining, results, failed) m =>
    if m.imports.any failed.contains then
      (remaining, results.push { name := m.name, status := .blocked, message := "A prerequisite failed" },
        failed.insert m.name)
    else (remaining.push m, results, failed)) (#[], done, failed)
  (remaining, results)

end LeanBuild
