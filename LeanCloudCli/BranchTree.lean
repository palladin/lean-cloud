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
  deriving Inhabited

private def ensure (entries : Array Entry) (location : Location) : Array Entry := Id.run do
  let mut entries := entries
  for depth in [1:location.size + 1] do
    let ancestor := branch (location.extract 0 depth)
    unless entries.any (·.branch == ancestor) do entries := entries.push { branch := ancestor }
  return entries

/-- Reconstruct the latest branch tree from observed scheduler states. -/
def current (observed : Array Trace.Step) : Array Entry := Id.run do
  let mut entries := #[]
  let mut control := ""
  for step in observed do
    if step.event.worker == "scheduler" then
      match step.event.activity with
      | "paused" => control := "paused"
      | "sealed" => control := "killed"
      | "failed" => control := "stopped"
      | "resumed" => control := ""
      | _ => pure ()
    let some location := step.owner | continue
    if location.isEmpty then continue
    entries := ensure entries location
    if let some job := step.job then
      if let .waiting children := job.status then
        for i in [:children] do entries := ensure entries (job.location.child i)
      if let some index := entries.findIdx? (·.branch == job.branch) then
        entries := entries.set! index { branch := job.branch, job := some job }
  return entries.map fun entry => { entry with control }

/-- Replay may visit an ancestor's code while executing a child assignment.
Use assignment ownership, not the current record's location, to select code. -/
def observations (observed : Array Trace.Step) (location : Location) : Array Trace.Step :=
  observed.filter fun step => step.event.worker != "scheduler" && step.job.isNone && step.owner == some location

structure Navigation where
  selected : Option String := none
  collapsed : Array String := #[]
  deriving BEq, Inhabited

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

private def forks (entries : Array Entry) (parent : Location) : Array Location :=
  (entries.foldl (fun all entry =>
    let fork := entry.branch.extract 0 (entry.branch.size - 1)
    if !fork.isEmpty && branch fork == parent && !all.contains fork then all.push fork else all) #[]).qsort
      (fun a b => a.back!.2 < b.back!.2)

private def children (entries : Array Entry) (fork : Location) : Array Entry :=
  (entries.filter fun e => e.branch.size == fork.size + 1 && e.branch.extract 0 fork.size == fork).qsort
    (fun a b => a.branch.back!.1 < b.branch.back!.1)

private def label (entries : Array Entry) (entry : Entry) : String :=
  if !entry.control.isEmpty && !entry.job.any (·.status == .done) then entry.control else
  match entry.job with
  | none => "unknown"
  | some job => match job.status with
    | .pending => if job.joining then "joining" else "pending"
    | .running worker _ => worker
    | .waiting count =>
      let done := (children entries job.location).filter (fun e => e.job.any (·.status == .done))
      s!"waiting {done.size}/{count}"
    | .done => "completed"

private def descend (entries : Array Entry) (nav : Navigation) :
    Nat → Entry → Nat → Option String → Array Row
  | 0, _, _, _ => #[]
  | fuel + 1, entry, depth, parent => Id.run do
    let groups := forks entries entry.branch
    let key := branchKey entry.branch
    let title := if entry.branch == Location.root then "root" else s!"branch {entry.branch.back!.1}"
    let mut rows := #[{ key, parent, branch := entry.branch, depth, title, status := label entries entry, expandable := !groups.isEmpty : Row }]
    unless nav.collapsed.contains key do
      for fork in groups do
        let key := forkKey fork
        let children := children entries fork
        let done := children.filter (fun e => e.job.any (·.status == .done))
        rows := rows.push { key, parent := some (branchKey entry.branch), branch := entry.branch, fork := some fork, depth := depth + 1, title := s!"parallel @{fork.back!.2}", status := s!"{done.size}/{children.size}", expandable := true }
        unless nav.collapsed.contains key do
          for child in children do
            rows := rows ++ descend entries nav fuel child (depth + 2) (some key)
    return rows

def rows (entries : Array Entry) (nav : Navigation) : Array Row :=
  match entries.find? (·.branch == Location.root) with
  | none => #[]
  | some root => descend entries nav (entries.size + 1) root 0 none

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
    | .up => select (index - 1)
    | .down => select (index + 1)
    | .left =>
      if row.expandable && !nav.collapsed.contains row.key then
        { nav with selected := some row.key, collapsed := nav.collapsed.push row.key }
      else { nav with selected := row.parent.orElse (fun _ => some row.key) }
    | .right | .enter =>
      if nav.collapsed.contains row.key then
        { nav with selected := some row.key, collapsed := nav.collapsed.filter (· != row.key) }
      else if row.expandable then select (index + 1) else nav
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
    let marker := if row.expandable then (if nav.collapsed.contains row.key then "▸" else "▾") else "·"
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
  result := result.push (Styled.text s!"{index + 1}/{visible.size} · ↑↓ select · ←→ fold" .muted)
  return result

end LeanCloudCli.BranchTree
