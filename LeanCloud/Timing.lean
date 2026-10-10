import LeanCloud.Pool

/-! Small scheduler-owned timing summaries. These are observational metadata,
saved with coordination state; they never influence scheduling or replay. -/
namespace LeanCloud.Timing
open Lean

/-- UTC Unix milliseconds. Elapsed time includes queueing, pauses and retries. -/
structure Span where
  startedMs : Nat
  finishedMs : Option Nat := none
  deriving BEq, Repr, ToJson, FromJson

def Span.finish (span : Span) (now : Nat) : Span :=
  { span with finishedMs := span.finishedMs.orElse fun _ => some (max span.startedMs now) }

def Span.elapsed (span : Span) (now : Nat) : Nat :=
  span.finishedMs.getD now - span.startedMs

structure Run where
  span : Option Span := none
  branches : Array (Location × Span) := #[]
  groups : Array (Location × Span) := #[]
  /-- Scheduler clock at observation, so clients need not synchronize clocks. -/
  observedMs : Nat := 0
  deriving BEq, Repr, ToJson, FromJson

/-- Advance only from actual transitions. Loading an older database without
timings must not invent start times for work that already existed. -/
def observe (timing : Run) (before : Option Pool.Run) (after : Pool.Run) (now : Nat) : Run := Id.run do
  let now := max timing.observedMs now
  let mut timing := { timing with observedMs := now }
  if before.isNone then timing := { timing with span := some ⟨now, none⟩ }
  let previous := (before.map (·.scheduler.jobs) |>.getD #[]).foldl
    (fun (jobs : Std.HashMap String Scheduler.Job) job => jobs.insert job.branch.key job) {}
  let mut knownBranches := timing.branches.foldl (fun (keys : Std.HashSet String) pair => keys.insert pair.1.key) {}
  let mut knownGroups := timing.groups.foldl (fun (keys : Std.HashSet String) pair => keys.insert pair.1.key) {}
  let mut done : Std.HashSet String := {}
  let mut groupsDone : Std.HashMap String Bool := {}
  for job in after.scheduler.jobs do
    let key := job.branch.key
    if job.status == .done then done := done.insert key
    if job.branch.size > 1 then
      let group := Location.key (job.branch.extract 0 (job.branch.size - 1))
      groupsDone := groupsDone.insert group (groupsDone[group]?.getD true && job.status == .done)
    if !previous.contains key && !knownBranches.contains key then
      timing := { timing with branches := timing.branches.push (job.branch, ⟨now, none⟩) }
      knownBranches := knownBranches.insert key
    if let .waiting _ := job.status then
      unless knownGroups.contains job.location.key || previous[key]?.any (fun old => old.location == job.location &&
          match old.status with | .waiting _ => true | _ => false) do
        timing := { timing with groups := timing.groups.push (job.location, ⟨now, none⟩) }
        knownGroups := knownGroups.insert job.location.key
  let stopped := done.contains Location.root.key || after.terminalOutcome.isSome
  let branches := timing.branches.map fun (location, span) =>
    (location, if stopped || done.contains location.key
      then span.finish now else span)
  let groups := timing.groups.map fun (location, span) =>
    (location, if stopped || groupsDone[location.key]?.getD false then span.finish now else span)
  return { timing with branches, groups, span := timing.span.map fun span => if stopped then span.finish now else span }

/-- The ordinary status JSON with optional timings. Old runtimes remain readable. -/
structure Status extends Scheduler.Snapshot where
  timing : Option Run := none

instance : ToJson Status := ⟨fun status =>
  (toJson status.toSnapshot).setObjVal! "timing" (toJson status.timing)⟩

instance : FromJson Status where
  fromJson? json := do
    let timing ← match json.getObjVal? "timing" with
      | .ok value => fromJson? value
      | .error _ => pure none
    return { toSnapshot := ← fromJson? json, timing }

end LeanCloud.Timing
