import LeanCloud.Proofs.Fuel
import LeanCloud.Proofs.Transitions

/-! Naming the existing driver's continuation for compositional proofs. The
functions below call the actual `interpret.run`; they introduce no new recursive
interpreter. `run_eq_step` checks their connection by definitional equality. -/

namespace LeanCloud.Proofs
open Lean LeanEff ReplayInterpreter.Internal

/-- The continuation following `step` in the existing driver. -/
def continueStep {World α : Type} [Codec α] (blobs : BlobModel World) (budget : Nat)
    (root : Cloud (StateM World) Json) (result : StepResult) :
    ExceptT CloudError (StateT Journal (StateM World)) α := do
  match result with
  | .done value _ _ => decode (inferInstance : Codec α) value
  | .suspended location remaining =>
    let nextLocation ← match ← load (modelStorage blobs) location with
      | some (.suspended children) =>
        let some index := children.findIdx? Option.isNone
          | throw ⟨.protocol, "Suspended parallel has no unfinished child"⟩
        pure (location.child index)
      | some (.completed _) => pure location
      | none => throw ⟨.protocol, "Missing parallel suspension"⟩
    if remaining < budget then
      LeanCloud.interpret.run (modelStorage blobs) remaining root nextLocation
    else
      throw ⟨.protocol, "Step did not consume fuel"⟩

theorem run_eq_step {World α : Type} [Codec α] (blobs : BlobModel World) (fuel : Nat)
    (root : Cloud (StateM World) Json) (target : Location) :
    LeanCloud.interpret.run (α := α) (modelStorage blobs) fuel root target =
      (step (modelStorage blobs) fuel root target >>= continueStep blobs fuel root) := by
  rw [LeanCloud.interpret.run]
  rfl

/-- Observe a point inside the existing `walk`, followed by the real driver's
continuation. This expression lets simulation equations cross suspensions. -/
def driveWalk {World α : Type} [Codec α] (blobs : BlobModel World) (fuel : Nat)
    (root program : Cloud (StateM World) Json) (current target : Location) :
    ExceptT CloudError (StateT Journal (StateM World)) α :=
  step.walk (modelStorage blobs) root fuel program current target >>= continueStep blobs fuel root

theorem continueStep_budget {World α : Type} [Codec α] (blobs : BlobModel World)
    (root : Cloud (StateM World) Json) (result : StepResult) (first second : Nat)
    (firstEnough : remainingFuel result < first) (secondEnough : remainingFuel result < second) :
    continueStep (α := α) blobs first root result = continueStep blobs second root result := by
  cases result with
  | done value location fuel => rfl
  | suspended location fuel =>
    simp only [remainingFuel] at firstEnough secondEnough
    simp only [continueStep, firstEnough, secondEnough, ↓reduceIte]

/-- A larger enclosing budget does not change the driver's continuation after a
successful inner step: both progress checks accept its smaller remaining fuel. -/
theorem driveWalk_enclosing_budget {World α : Type} [Codec α] (blobs : BlobModel World)
    (fuel budget : Nat) (root program : Cloud (StateM World) Json) (current target : Location)
    (enough : fuel ≤ budget) :
    (step.walk (modelStorage blobs) root fuel program current target >>= continueStep (α := α) blobs budget root) =
      driveWalk blobs fuel root program current target := by
  funext journal world
  change (step.walk (modelStorage blobs) root fuel program current target >>=
    continueStep (α := α) blobs budget root).run journal world =
    (driveWalk (α := α) blobs fuel root program current target).run journal world
  rw [driveWalk, run_bind_state, run_bind_state]
  cases executed : (step.walk (modelStorage blobs) root fuel program current target).run journal world with
  | mk pair nextWorld => cases pair with
    | mk outcome nextJournal =>
      cases outcome with
      | error error => rfl
      | ok result =>
        have bound := walk_consumes_fuel blobs root fuel program current target
          journal world result nextJournal nextWorld executed
        exact congrArg (fun action => action.run nextJournal nextWorld)
          (continueStep_budget (α := α) blobs root result budget fuel (by omega) bound)

theorem driveWalk_frontier {World α : Type} [Codec α] (blobs : BlobModel World)
    (fuel : Nat) (root program : Cloud (StateM World) Json) (current target : Location)
    (nonempty : 0 < current.size) (atFrontier : current.before target = false) :
    driveWalk (α := α) blobs fuel root program current target = driveWalk blobs fuel root program current current := by
  unfold driveWalk
  rw [walk_at_frontier (modelStorage blobs) root fuel program current target nonempty atFrontier]

/-- Lift an equation between inner-loop runs through the real driver. This is
the composition rule used by sequential progress and parent reconstruction. -/
theorem driveWalk_reduce {World α : Type} [Codec α] (blobs : BlobModel World)
    (budget fuel : Nat) (root program next : Cloud (StateM World) Json)
    (current target nextCurrent nextTarget : Location) (journal nextJournal : Journal)
    (world nextWorld : World) (enough : fuel ≤ budget)
    (reduced : (step.walk (modelStorage blobs) root budget program current target).run journal world =
      (step.walk (modelStorage blobs) root fuel next nextCurrent nextTarget).run nextJournal nextWorld) :
    (driveWalk (α := α) blobs budget root program current target).run journal world =
      (driveWalk blobs fuel root next nextCurrent nextTarget).run nextJournal nextWorld := by
  conv => lhs; rw [driveWalk, run_bind_state, reduced]
  have enclosed := congrArg (fun action => action.run nextJournal nextWorld)
    (driveWalk_enclosing_budget (α := α) blobs fuel budget root next nextCurrent nextTarget enough)
  rw [run_bind_state] at enclosed
  exact enclosed

/-- An actual suspension transfers control to the driver's selected work item. -/
theorem driveWalk_suspended {World α : Type} [Codec α] (blobs : BlobModel World)
    (budget fuel : Nat) (root program : Cloud (StateM World) Json) (current target parent : Location)
    (journal nextJournal : Journal) (world nextWorld : World) (children : Array (Option Exit)) (index : Nat)
    (suspended : (step.walk (modelStorage blobs) root budget program current target).run journal world =
      ((.ok (.suspended parent fuel), nextJournal), nextWorld))
    (recorded : nextJournal parent.key = some (toJson (Result.suspended children)))
    (selected : children.findIdx? Option.isNone = some index) (decreased : fuel < budget) :
    (driveWalk (α := α) blobs budget root program current target).run journal world =
      (LeanCloud.interpret.run (α := α) (modelStorage blobs) fuel root (parent.child index)).run
        nextJournal nextWorld := by
  rw [driveWalk, run_bind_state, suspended]
  simp only [continueStep, run_bind_state, load_recorded blobs nextJournal nextWorld parent _ recorded,
    selected, run_pure_state, decreased, ↓reduceIte]

theorem driveWalk_delay {World α : Type} [Codec α] (blobs : BlobModel World)
    (root : Cloud (StateM World) Json) (fuel : Nat)
    (continuation : ArrsF (Control (StateM World)) Unit Json) (current target : Location) :
    driveWalk (α := α) blobs (fuel + 1) root (.impure .delay continuation) current target =
      driveWalk blobs fuel root (ArrsF.apply continuation ()) current target := by
  unfold driveWalk
  rw [step.walk]
  exact driveWalk_enclosing_budget blobs fuel (fuel + 1) root (ArrsF.apply continuation ()) current target (by omega)

theorem driveWalk_sequential {World α β : Type} [Codec β] (blobs : BlobModel World)
    (root : Cloud (StateM World) Json) (fuel : Nat) (codec : Codec α) (law : CodecLaw codec)
    (operation : Operation (StateM World) α) (continuation : ArrsF (Control (StateM World)) α Json)
    (current : Location) (journal : Journal) (world nextWorld : World) (value : α)
    (nonempty : 0 < current.size) (fresh : journal.Fresh current)
    (executed : ((modelStorage blobs).execute operation).run journal world = ((.ok value, journal), nextWorld)) :
    (driveWalk (α := β) blobs (fuel + 1) root (.impure (.sequential codec operation) continuation)
      current current).run journal world =
      (driveWalk blobs fuel root (ArrsF.apply continuation value) current.next current.next).run
        (journal.write current.key (toJson (Result.completed (.success (codec.encode value))))) nextWorld := by
  have reduced := walk_fresh_sequential blobs root fuel codec law operation continuation value current current
    journal world nextWorld (by simp [Location.before]) (fresh.missing nonempty) executed
  have driven := driveWalk_reduce (α := β) blobs (fuel + 1) fuel root _ _ current current current.next current
    journal _ world nextWorld (by omega) reduced
  rw [driveWalk_frontier blobs fuel root _ current.next current (Location.next_nonempty current nonempty)
    (Location.next_not_before nonempty (by simp [Location.before]))] at driven
  exact driven

/-- Reconstructing a certified route costs exactly its prefix length, after which
the real driver has the same behavior as execution directly at the frontier. -/
theorem ReplayRoute.drive {World α : Type} [Codec α] {blobs : BlobModel World} {journal : Journal}
    {root remaining : Cloud (StateM World) Json} {target : Location} {steps : Nat}
    (route : ReplayRoute journal root Location.root remaining target steps)
    (fuel : Nat) (world : World) :
    (LeanCloud.interpret.run (α := α) (modelStorage blobs) (fuel + steps) root target).run journal world =
      (driveWalk (α := α) blobs fuel root remaining target target).run journal world := by
  rw [run_eq_step, driveWalk, run_bind_state, run_bind_state, route.from_root]
  cases executed : (step.walk (modelStorage blobs) root fuel remaining target target).run journal world with
  | mk pair nextWorld => cases pair with
    | mk outcome nextJournal =>
      cases outcome with
      | error error => rfl
      | ok result =>
        have bound := walk_consumes_fuel blobs root fuel remaining target target
          journal world result nextJournal nextWorld executed
        exact congrArg (fun action => action.run nextJournal nextWorld)
          (continueStep_budget (α := α) blobs root result (fuel + steps) fuel (by omega) bound)

end LeanCloud.Proofs
