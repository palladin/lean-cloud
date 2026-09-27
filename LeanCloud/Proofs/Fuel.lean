import LeanCloud.Proofs.Frontier
import Lean.Elab.Tactic.Basic

/-! Fuel accounting for the actual replay loop. Successful step results always
carry strictly less fuel, which justifies the driver's progress check. -/

namespace LeanCloud.Proofs
open Lean LeanEff ReplayInterpreter.Internal

/-- A postcondition on every successful result of a state action. Errors retain
their state but do not assert a successful-result postcondition. -/
def ActionPost (action : ExceptT CloudError (StateT Journal (StateM World)) α)
    (post : α → Prop) : Prop :=
  ∀ journal world value finalJournal finalWorld,
    action.run journal world = ((.ok value, finalJournal), finalWorld) → post value

namespace ActionPost

theorem pure_action (value : α) (post : α → Prop) (holds : post value) :
    ActionPost (World := World) (pure value) post := by
  intro journal world result finalJournal finalWorld executed
  have equal : value = result := Except.ok.inj (congrArg (fun result => result.1.1) executed)
  simpa only [← equal] using holds

theorem throw_action (error : CloudError) (post : α → Prop) :
    ActionPost (World := World) (throw error) post := by
  intro journal world result finalJournal finalWorld executed
  cases executed

theorem bind_action {α β : Type} (action : ExceptT CloudError (StateT Journal (StateM World)) α)
    (next : α → ExceptT CloudError (StateT Journal (StateM World)) β) (post : β → Prop)
    (rest : ∀ value, ActionPost (next value) post) : ActionPost (action >>= next) post := by
  intro journal world value finalJournal finalWorld executed
  rw [run_bind_state] at executed
  cases first : action.run journal world with
  | mk pair middleWorld => cases pair with
    | mk outcome middleJournal =>
      rw [first] at executed
      cases outcome with
      | error error => cases executed
      | ok result => exact rest result middleJournal middleWorld value finalJournal finalWorld executed

theorem mono {action : ExceptT CloudError (StateT Journal (StateM World)) α} {first second : α → Prop}
    (ensures : ActionPost action first) (implies : ∀ value, first value → second value) : ActionPost action second :=
  fun journal world value finalJournal finalWorld executed =>
    implies value (ensures journal world value finalJournal finalWorld executed)

end ActionPost

def remainingFuel : StepResult → Nat
  | .done _ _ fuel => fuel
  | .suspended _ fuel => fuel

-- Dispatch only on the action's syntactic head. Blindly applying a bind rule to
-- an unknown action can ask higher-order unification to invent a decomposition.
elab "fuel_post_step" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  let args := target.getAppArgs
  unless target.isAppOf ``ActionPost do throwError "expected an action postcondition"
  let action := args[args.size - 2]!.consumeMData
  if action.isAppOf ``Bind.bind then
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply ActionPost.bind_action; intro value))
  else if action.isAppOf ``Pure.pure then
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply ActionPost.pure_action; simp [remainingFuel]))
  else if action.isAppOf ``step.walk then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent `recurse) _ _ _))
  else
    Lean.Elab.Tactic.evalTactic (← `(tactic| first | exact ActionPost.throw_action _ _ | split))

set_option maxHeartbeats 1000000 in
/-- Every successful return from the inner loop has consumed at least one unit
of its supplied budget. This holds independently of the journal contents. -/
theorem walk_consumes_fuel {World : Type} (blobs : BlobModel World)
    (root : Cloud (StateM World) Json) (fuel : Nat)
    (program : Cloud (StateM World) Json) (current target : Location) :
    ActionPost (step.walk (modelStorage blobs) root fuel program current target)
      (fun result => remainingFuel result < fuel) := by
  induction fuel generalizing program current target with
  | zero => exact ActionPost.throw_action _ _
  | succ fuel ih =>
    have recurse (program : Cloud (StateM World) Json) (current target : Location) :
        ActionPost (step.walk (modelStorage blobs) root fuel program current target)
          (fun result => remainingFuel result < fuel + 1) :=
      (ih program current target).mono (fun _ bound => Nat.lt_trans bound (by omega))
    cases program with
    | pure value =>
      rw [step.walk]
      dsimp only
      repeat' fuel_post_step
    | impure request continuation =>
      cases request <;> rw [step.walk] <;> (try dsimp only)
      all_goals
        repeat' fuel_post_step

theorem step_consumes_fuel {World : Type} (blobs : BlobModel World)
    (root : Cloud (StateM World) Json) (fuel : Nat) (target : Location) :
    ActionPost (step (modelStorage blobs) fuel root target) (fun result => remainingFuel result < fuel) := by
  rw [step]
  split
  · exact ActionPost.throw_action _ _
  · exact walk_consumes_fuel blobs root fuel root Location.root target

end LeanCloud.Proofs
