import LeanCloudCli.Trace
import LeanCloudCli.Input
import LeanCloudCli.Styled
import LeanCloudCli.Time

namespace LeanCloudCli.BranchTree
open LeanCloud
open Trace (branch)

structure Entry where
  branch : Location
  job : Option BranchObservation := none
  control : String := ""
  labels : Std.HashMap String String := {}
  deriving Inhabited

private def ensure (entries : Array Entry) (known : Std.HashMap String Nat)
    (location : Location) : Array Entry × Std.HashMap String Nat := Id.run do
  let mut entries := entries
  let mut known := known
  for depth in [1:location.size + 1] do
    let ancestor := branch (location.extract 0 depth)
    unless known.contains ancestor.key do
      known := known.insert ancestor.key entries.size
      entries := entries.push { branch := ancestor }
  return (entries, known)

private def observeJob (entries : Array Entry) (known : Std.HashMap String Nat)
    (job : BranchObservation) : Array Entry × Std.HashMap String Nat := Id.run do
  let mut (entries, known) := ensure entries known job.branch
  if let .waiting children := job.status then
    for i in [:children] do
      (entries, known) := ensure entries known (job.location.child i)
  if let some index := known[job.branch.key]? then
    entries := entries.set! index { branch := job.branch, job := some job }
  return (entries, known)

/-- Reconstruct the latest branch tree from observed scheduler states. -/
def current (observed : Array Trace.Step) (jobs : Array BranchObservation := #[]) : Array Entry := Id.run do
  let mut entries := #[]
  let mut known : Std.HashMap String Nat := {}
  let mut control := ""
  let mut labels : Std.HashMap String (Std.HashMap String String) := {}
  for step in observed do
    if step.event.worker != "scheduler" && step.event.activity == "parallel-label" then
      if let some fork := Trace.location? step.event.location then
        let parent := (branch fork).key
        labels := labels.insert parent ((labels[parent]?.getD {}).insert fork.key step.event.operation)
    if step.event.worker == "scheduler" then
      match step.event.activity with
      | "paused" => control := "paused"
      | "sealed" | "killed" => control := "killed"
      | "failed" => control := "stopped"
      | "resumed" => control := ""
      | _ => pure ()
    let some location := step.owner | continue
    if location.isEmpty then continue
    (entries, known) := ensure entries known location
    if let some job := step.job then
      (entries, known) := observeJob entries known job
  for job in jobs do
    (entries, known) := observeJob entries known job
  return entries.map fun entry => { entry with control, labels := labels[entry.branch.key]?.getD {} }

/-- Replay may visit an ancestor's code while executing a child assignment.
Use assignment ownership, not the current record's location, to select code. -/
def observations (observed : Array Trace.Step) (location : Location) : Array Trace.Step :=
  observed.filter fun step => step.event.worker != "scheduler" && step.job.isNone && step.owner == some location

structure Navigation where
  selected : Option String := none
  /-- Explicit choices survive refreshes. Branches default open; parallel groups closed. -/
  expanded : Std.HashMap String Bool := {}
  deriving BEq, Inhabited

private def Navigation.isExpanded (nav : Navigation) (key : String) (default : Bool) : Bool :=
  nav.expanded[key]?.getD default

structure Row where
  key : String
  parent : Option String
  branch : Location
  fork : Option Location := none
  depth : Nat
  title : String
  status : String
  expandable : Bool
  deriving Inhabited

private def branchKey (location : Location) := "branch/" ++ location.key
private def forkKey (location : Location) := "parallel/" ++ location.key

private structure Index where
  forks : Std.HashMap String (Array Location) := {}
  children : Std.HashMap String (Array Entry) := {}

/-- Build adjacency once, rather than scanning the whole tree at every node. -/
private def indexTree (entries : Array Entry) : Index := Id.run do
  let mut index : Index := {}
  for entry in entries do
    if entry.branch.size ≤ 1 then continue
    let fork : Location := entry.branch.extract 0 (entry.branch.size - 1)
    unless index.children.contains fork.key do
      let parent := (branch fork).key
      let forks := (index.forks[parent]?.getD #[]).push fork
      index := { index with forks := index.forks.insert parent forks }
    let members := (index.children[fork.key]?.getD #[]).push entry
    index := { index with children := index.children.insert fork.key members }
  return {
    forks := index.forks.map fun _ forks => forks.qsort (fun a b => a.back!.2 < b.back!.2)
    children := index.children.map fun _ children => children.qsort (fun a b => a.branch.back!.1 < b.branch.back!.1) }

private def children (index : Index) (fork : Location) : Array Entry :=
  index.children[fork.key]?.getD #[]

private def label (index : Index) (entry : Entry) : String :=
  if !entry.control.isEmpty && !entry.job.any (·.status == .done) then entry.control else
  match entry.job with
  | none => "unknown"
  | some job => match job.status with
    | .pending => if job.joining then "joining" else "pending"
    | .running worker _ => worker
    | .waiting count =>
      let done := (children index job.location).filter (fun e => e.job.any (·.status == .done))
      s!"waiting {done.size}/{count}"
    | .done => "completed"

private def descend (index : Index) (nav : Navigation) :
    Nat → Entry → Nat → Option String → Array Row
  | 0, _, _, _ => #[]
  | fuel + 1, entry, depth, parent => Id.run do
    let groups := index.forks[entry.branch.key]?.getD #[]
    let key := branchKey entry.branch
    let title := if entry.branch == Location.root then "root" else s!"branch {entry.branch.back!.1}"
    let mut rows := #[{ key, parent, branch := entry.branch, depth, title, status := label index entry, expandable := !groups.isEmpty : Row }]
    if nav.isExpanded key true then
      for fork in groups do
        let key := forkKey fork
        let children := children index fork
        let done := children.filter (fun e => e.job.any (·.status == .done))
        let title := entry.labels[fork.key]?.filter (!·.isEmpty) |>.getD "parallel"
        rows := rows.push { key, parent := some (branchKey entry.branch), branch := entry.branch, fork := some fork, depth := depth + 1, title, status := s!"{done.size}/{children.size}", expandable := true }
        if nav.isExpanded key false then
          for child in children do
            rows := rows ++ descend index nav fuel child (depth + 2) (some key)
    return rows

def rows (entries : Array Entry) (nav : Navigation) : Array Row :=
  match entries.find? (·.branch == Location.root) with
  | none => #[]
  | some root => descend (indexTree entries) nav (entries.size + 1) root 0 none

private def index (rows : Array Row) (nav : Navigation) : Nat :=
  (nav.selected >>= fun key => rows.findIdx? (·.key == key)).getD 0

def selected (entries : Array Entry) (nav : Navigation) : Option Row :=
  let visible := rows entries nav
  visible[index visible nav]?

def navigate (entries : Array Entry) (nav : Navigation)
    (key : Input.Key) : Navigation := Id.run do
  let visible := rows entries nav
  let index := index visible nav
  let some row := visible[index]? | return nav
  let select (index : Nat) := { nav with selected := (visible[min index (visible.size - 1)]?).map (·.key) }
  return match key with
    | .up => select (if index == 0 then visible.size - 1 else index - 1)
    | .down => select ((index + 1) % visible.size)
    | .left =>
      if row.expandable && nav.isExpanded row.key row.fork.isNone then
        { nav with selected := some row.key, expanded := nav.expanded.insert row.key false }
      else { nav with selected := row.parent.orElse (fun _ => some row.key) }
    | .right | .enter =>
      if !row.expandable then nav
      else if !nav.isExpanded row.key row.fork.isNone then
        { nav with selected := some row.key, expanded := nav.expanded.insert row.key true }
      else select (index + 1)
    | _ => nav

def lines (entries : Array Entry) (nav : Navigation)
    (height width : Nat) (timing : Option Timing.Run := none) : Array Styled.Line := Id.run do
  let visible := rows entries nav
  let index := index visible nav
  let labelWidth := width - 10
  let mut result := #[Styled.text (pad labelWidth " BRANCHES" ++ "   ELAPSED") .header]
  if visible.isEmpty then
    return result.push (Styled.text "Waiting for branches" .muted)
  let count := height - 2
  let start := min (index - count / 2) (visible.size - count)
  for i in [start:min visible.size (start + count)] do
    let row := visible[i]!
    let marker := if row.expandable then (if nav.isExpanded row.key row.fork.isNone then "▾" else "▸") else "·"
    let indent := String.ofList (List.replicate (min (width / 3) (row.depth * 2)) ' ')
    let heading := s!"{indent}{marker} {row.title} "
    let color := if i == index then Styled.Color.selected else .normal
    let statusColor := if i == index then .selected else if row.status.startsWith "worker" then .green else Styled.statusColor row.status
    let span : Option Timing.Span := timing >>= fun timing => do
      let found ← match row.fork with
        | some fork => timing.groups.find? (fun pair => pair.1 == fork)
        | none => timing.branches.find? (fun pair => pair.1 == row.branch)
      pure found.2
    let elapsed := Time.elapsed span (timing.map (·.observedMs) |>.getD 0)
    let label := Styled.slice (Styled.text heading color ++ Styled.text row.status statusColor) 0 labelWidth
    let padding := String.ofList (List.replicate (labelWidth - (Styled.plain label).length) ' ')
    result := result.push (label ++ Styled.text padding color ++
      Styled.text (String.ofList (List.replicate (10 - elapsed.length) ' ') ++ elapsed)
        (if i == index then .selected else .cyan))
  result := result.push (Styled.text s!"{index + 1}/{visible.size} · ↑↓ wrap · ←→ fold" .muted)
  return result

end LeanCloudCli.BranchTree
