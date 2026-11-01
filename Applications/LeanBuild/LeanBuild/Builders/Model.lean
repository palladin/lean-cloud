import LeanBuild.Dependencies
import LeanCloud.ExecServices

namespace LeanBuild.Builders
open Lean LeanCloud

def queueName := "lean-build/v7/modules"
def resultName (module : String) := "lean-build/v7/results/" ++ module

def ioConcurrency (cpus : Nat) : Nat := max 4 (min 32 (4 * cpus))
/-- A compilation budget, not CPU affinity. Keep one CPU for coordination and IO. -/
def compilerSlots (cpus : Nat) : Nat := max 1 (cpus - 1)
/-- One compiling window and one window preparing or queued inside Lake. -/
def submissionWindow (cpus : Nat) : Nat := 2 * compilerSlots cpus

/-- Longest remaining dependency chain. The module array is topological. -/
def priorities (modules : Array Module) : Std.HashMap String Nat :=
  modules.foldr (fun m scores =>
    let score := max 1 (scores[m.name]?.getD 0)
    m.imports.foldl (fun scores name => scores.insert name (max (score + 1) (scores[name]?.getD 0)))
      (scores.insert m.name score)) {}

def item (scores : Std.HashMap String Nat) (m : Module) : WorkItem :=
  { key := m.name, value := toJson m.name, priority := scores[m.name]?.getD 1 }

structure Settings where
  modules : Dependencies.Index
  dependents : Std.HashMap String (Array Module)
  scores : Std.HashMap String Nat
  cpus : Nat

def Settings.ofPlan (plan : Plan) (cpus : Nat) : Settings := {
  modules := Dependencies.index plan.modules
  dependents := plan.modules.foldl (fun map m => m.imports.foldl (fun map dep =>
    map.insert dep ((map[dep]?.getD #[]).push m)) map) {}
  scores := priorities plan.modules
  cpus }

/-- Payloads are values, never tasks, callbacks into IO, or mutable cells. -/
inductive Event (α : Type) where
  | received (deliveries : Array WorkDelivery) (idle : Bool)
  | prepared (name : String)
  | compiled (name : String) (value : α)
  | published (result : BuildResult)
  | deferred (name : String)
  | settled (name : String) (receipts : Array String)
  | cancelled

inductive Action (α : Type) where
  | receive (count : Nat)
  | prepare (module : Module)
  | submit (module : Module)
  | publish (module : Module) (value : α)
  | settle (module : Module) (result : BuildResult) (receipts : Array String)
  | release (name : String) (receipts : Array String)

private structure Work where
  mod : Module
  receipts : Array String
  result : Option BuildResult := none

/-- Coordinator state is local, immutable and independent of the IO handler. -/
structure State (α : Type) where
  private work : Std.HashMap String Work := {}
  waiting : Array String := #[]
  restoring : Std.HashSet String := {}
  ready : Array String := #[]
  submitted : Std.HashSet String := {}
  completed : Array (String × α) := #[]
  uploading : Std.HashSet String := {}
  unlocking : Std.HashSet String := {}
  receiving : Bool := false
  idle : Bool := false
  nextReceive : Nat := 0
  cancelled : Bool := false

def State.finished (s : State α) : Bool := s.cancelled || (s.idle && s.work.isEmpty && !s.receiving)

def State.activity (s : State α) (cpus : Nat) : String :=
  s!"Lake jobs {s.submitted.size} running/queued · slots {compilerSlots cpus} · restoring {s.restoring.size} · ready {s.ready.size} · uploading {s.uploading.size} · awaiting upload {s.completed.size} · unlocking {s.unlocking.size}"

/-- Apply replies before admitting more work. A completion frees admission
capacity before its artifacts are published. Receipts stay live until settlement. -/
def advance (cfg : Settings) (now : Nat) (state : State α) (events : Array (Event α)) :
    Except String (State α × Array (Action α)) := do
  let mut s := state
  let mut actions := #[]
  for event in events do
    if s.cancelled then break
    match event with
    | .cancelled => s := { s with cancelled := true }; actions := #[]
    | .received deliveries idle =>
      unless s.receiving do throw "Unexpected queue response"
      s := { s with
        receiving := false
        idle := idle
        nextReceive := if deliveries.isEmpty then now + 100 else s.nextReceive }
      for delivery in deliveries do
        let name : String ← fromJson? delivery.value
        let some m := cfg.modules[name]? | throw "Unknown queued module"
        if let some w := s.work[name]? then
          unless w.receipts.contains delivery.receipt do
            s := { s with work := s.work.insert name { w with receipts := w.receipts.push delivery.receipt } }
        else
          s := { s with work := s.work.insert name ⟨m, #[delivery.receipt], none⟩, waiting := s.waiting.push name }
    | .prepared name =>
      unless s.restoring.contains name do throw "Unexpected preparation"
      s := { s with restoring := s.restoring.erase name, ready := s.ready.push name }
    | .compiled name value =>
      unless s.submitted.contains name do throw "Unknown or duplicate Lake completion"
      s := { s with submitted := s.submitted.erase name, completed := s.completed.push (name, value) }
    | .published result =>
      let some w := s.work[result.name]? | throw "Unknown published module"
      unless s.restoring.contains result.name || s.uploading.contains result.name do
        throw "Unexpected publication"
      s := { s with
        work := s.work.insert result.name { w with result := some result }
        restoring := s.restoring.erase result.name
        uploading := s.uploading.erase result.name
        unlocking := s.unlocking.insert result.name }
      actions := actions.push (.settle w.mod result w.receipts)
    | .deferred name =>
      let some w := s.work[name]? | throw "Unknown deferred module"
      unless s.restoring.contains name do throw "Unexpected deferred module"
      actions := actions.push (.release name w.receipts)
    | .settled name receipts =>
      let some w := s.work[name]? | throw "Unknown settled module"
      let remaining := w.receipts.filter (!receipts.contains ·)
      if remaining.isEmpty then
        s := { s with
          work := s.work.erase name
          restoring := s.restoring.erase name
          uploading := s.uploading.erase name
          unlocking := s.unlocking.erase name }
      else
        -- A duplicate can arrive while an earlier receipt is being settled.
        s := { s with work := s.work.insert name { w with receipts := remaining } }
        match w.result with
        | some result => actions := actions.push (.settle w.mod result remaining)
        | none => actions := actions.push (.release name remaining)
  if s.finished then return (s, actions)
  for name in s.ready do
    let some w := s.work[name]? | throw "Missing prepared work"
    actions := actions.push (.submit w.mod)
    s := { s with submitted := s.submitted.insert name }
  s := { s with ready := #[] }
  let ioSlots := max 2 (min 8 cfg.cpus)
  while s.uploading.size < ioSlots && !s.completed.isEmpty do
    let some (name, value) := s.completed[0]? | break
    let some w := s.work[name]? | throw "Missing compiled work"
    s := { s with completed := s.completed.extract 1 s.completed.size, uploading := s.uploading.insert name }
    actions := actions.push (.publish w.mod value)
  while s.restoring.size < ioSlots && !s.waiting.isEmpty do
    let name := s.waiting[0]!
    let some w := s.work[name]? | throw "Missing received work"
    s := { s with waiting := s.waiting.extract 1 s.waiting.size, restoring := s.restoring.insert name }
    actions := actions.push (.prepare w.mod)
  let admission := submissionWindow cfg.cpus - (s.waiting.size + s.restoring.size + s.ready.size + s.submitted.size)
  let capacity := 3 * compilerSlots cfg.cpus + ioSlots
  if !s.receiving && admission > 0 && s.work.size < capacity && now ≥ s.nextReceive then
    s := { s with receiving := true }
    actions := actions.push (.receive (min 100 (min admission (capacity - s.work.size))))
  return (s, actions)

end LeanBuild.Builders
