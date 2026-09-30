import LeanCloud.ReplayInterpreter

/-! Backend-independent proof factors of the existing completion code. The
runtime interpreter is unchanged; recovery and backend mapping share these terms. -/

universe u

namespace LeanCloud.Proofs.ReplayRecovery
open Lean ReplayInterpreter.Internal

/-- The common prefix of root and child completion in the actual worker. -/
def recordResult {m : Type → Type u} [Monad m] (db : Db σ m) (current : Location) (outcome : Exit) :
    ExceptT CloudError (StateT σ m) Unit := do
  match ← load db current with
  | none => save db current (.completed outcome)
  | some (.completed recorded) =>
    if recorded != outcome then throw ⟨.divergence, "Completion changed during replay"⟩
  | some (.suspended _) => throw ⟨.divergence, "Expected a completed computation"⟩

def readParent {m : Type → Type u} [Monad m] (db : Db σ m) (parent : Location) :
    ExceptT CloudError (StateT σ m) StepResult := do
  let some latest ← load db parent | throw ⟨.protocol, "Missing parent suspension"⟩
  return joinResponse parent latest

def publishParent {m : Type → Type u} [Monad m] (db : Db σ m) (parent : Location)
    (slots : Array (Option Exit)) (updated : Result) : ExceptT CloudError (StateT σ m) StepResult := do
  save db parent (.suspended slots)
  if let .completed _ := updated then save db parent updated
  readParent db parent

/-- Publication of a child's result to its parent. -/
def notifyParent {m : Type → Type u} [Monad m] (db : Db σ m) (parent : Location) (index : Nat) (outcome : Exit) : ExceptT CloudError (StateT σ m) StepResult := do
  let some group ← load db parent | throw ⟨.protocol, "Missing parent suspension"⟩
  match group with
  | .completed _ => return .runnable #[parent]
  | .suspended children =>
    let updated ← match Result.recordChild group index outcome with
      | .ok result => pure result
      | .error error => throw error
    publishParent db parent (children.set! index (some outcome)) updated

theorem finish_eq {m : Type → Type u} [Monad m] [LawfulMonad m] (db : Db σ m)
    (current : Location) (outcome : Exit) :
    finish db current outcome = (do
      recordResult db current outcome
      match current.parent? with
      | none => pure (.done outcome)
      | some (parent, index) => notifyParent db parent index outcome) := by
  simp only [finish, recordResult, notifyParent, publishParent, readParent, bind_assoc, pure_bind]
  congr 1
  funext recorded
  cases recorded with
  | none => rfl
  | some record =>
    cases record with
    | suspended _ => simp only [ExceptT.bind_throw]
    | completed previous =>
      by_cases different : (previous != outcome) = true <;>
        simp only [different, Bool.false_eq_true, ↓reduceIte, ExceptT.bind_throw, pure_bind]
      congr 1

theorem finish_child_eq {m : Type → Type u} [Monad m] [LawfulMonad m] (db : Db σ m)
    (current parent : Location) (index : Nat) (outcome : Exit)
    (linked : current.parent? = some (parent, index)) :
    finish db current outcome = (do
      recordResult db current outcome
      notifyParent db parent index outcome) := by rw [finish_eq, linked]

end LeanCloud.Proofs.ReplayRecovery
