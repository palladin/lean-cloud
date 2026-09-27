import LeanCloud.Proofs.ReplayPrefix

/-! Reconstruction from the workflow root into nested branches. A route composes
certified sequential prefixes with descent through recorded partial groups. The
proofs apply to the existing `step` and `step.walk`, including their fuel budgets.
`Proofs.Transitions` constructs these certificates for fresh effects, suspension,
and child selection. `Proofs.WholeRun` establishes full fresh-run equivalence. -/

namespace LeanCloud.Proofs
open Lean LeanEff ReplayInterpreter.Internal

/-- A route to a computation reconstructed from recorded prefixes and partial
parallel groups. Descending selects the original branch with its captured values.
The target's own record is unrestricted, so the route survives its completion. -/
inductive ReplayRoute {World : Type} (journal : Journal) :
    Cloud (StateM World) Json → Location → Cloud (StateM World) Json → Location → Nat → Prop where
  | leaf {program current remaining target steps}
      (nonempty : 0 < current.size)
      (segment : ReplayPrefix journal program current
        remaining target steps) :
      ReplayRoute journal program current remaining target steps
  | child {α : Type} {codec : Codec α} {count : Nat}
      {branches : Fin count → Cloud (StateM World) α}
      {continuation program current fork remaining target prefixSteps childSteps}
      {children : Array (Option Exit)} {index : Fin count}
      (nonempty : 0 < current.size)
      (segment : ReplayPrefix journal program current
        (.impure (.parallel codec count branches) continuation) fork prefixSteps)
      (recorded : journal fork.key = some (toJson (Result.suspended children)))
      (size : children.size = count)
      (enters : fork.entersChild target = true)
      (selected : target[fork.size]!.1 = index.val)
      (rest : ReplayRoute journal (codec.encode <$> branches index)
        (fork.child index.val) remaining target childSteps) :
      ReplayRoute journal program current remaining target (prefixSteps + 1 + childSteps)

namespace ReplayRoute

variable {World : Type} {blobs : BlobModel World} {journal : Journal}
    {program remaining : Cloud (StateM World) Json} {current target : Location} {steps : Nat}

/-- Before any execution, the root is reached without reconstructing any prefix. -/
theorem initial (root : Cloud (StateM World) Json) :
    ReplayRoute journal root Location.root root Location.root 0 :=
  .leaf (by decide) .here

theorem nonempty (route : ReplayRoute journal program current remaining target steps) :
    0 < current.size := by
  cases route with
  | leaf nonempty _ => exact nonempty
  | child nonempty _ _ _ _ _ _ => exact nonempty

theorem depth_le (route : ReplayRoute journal program current remaining target steps) :
    current.size ≤ target.size := by
  cases route with
  | leaf _ segment => exact Nat.le_of_eq segment.same_depth
  | child _ segment _ _ enters _ _ =>
    have depth := segment.same_depth
    have deeper := Location.entersChild_size enters
    omega

theorem root_branch (route : ReplayRoute journal program current remaining target steps) :
    target[0]!.1 = current[0]!.1 := by
  induction route with
  | leaf nonempty segment => exact segment.root_branch nonempty
  | child nonempty segment _ _ _ _ _ ih =>
    have forkNonempty := nonempty
    rw [segment.same_depth] at forkNonempty
    exact ih.trans ((Location.child_root_branch _ forkNonempty _).trans (segment.root_branch nonempty))

/-- Reconstructing the complete route is identical to starting at the remaining
computation with the remaining fuel, journal, and external world. -/
theorem reconstruct (route : ReplayRoute journal program current remaining target steps)
    (root : Cloud (StateM World) Json) (fuel : Nat) (world : World) :
    (step.walk (modelStorage blobs) root (fuel + steps) program current target).run journal world =
    (step.walk (modelStorage blobs) root fuel remaining target target).run journal world := by
  induction route with
  | leaf nonempty segment => exact segment.reconstruct root fuel world nonempty
  | child nonempty segment recorded size enters selected _ ih =>
    have whole := (segment.reconstruct_towards root _ world _ (Or.inr enters) nonempty).trans
      ((walk_parallel_child blobs root _ _ _ _ _ _ _ _ world _ size enters _ selected recorded).trans ih)
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using whole

/-- Route reconstruction remains valid after changing completed-group records
at the target, while retaining completed prefixes and its suspended ancestors. -/
theorem preserve {updated : Journal}
    (route : ReplayRoute journal program current remaining target steps)
    (completed : Journal.PreservesCompleted journal updated)
    (ancestors : Journal.PreservesAncestors journal updated target) :
    ReplayRoute updated program current remaining target steps := by
  induction route with
  | leaf nonempty segment => exact .leaf nonempty (segment.preserve completed)
  | child nonempty segment recorded size enters selected _ ih =>
    have forkNonempty := nonempty
    rw [segment.same_depth] at forkNonempty
    have kept := ancestors _ forkNonempty (Location.entersChild_size enters)
    exact .child nonempty (segment.preserve completed) (kept.trans recorded) size enters selected (ih ancestors)

/-- The actual `step` entry point accepts the route's target as a valid root-based
location and reconstructs the requested nested computation. -/
theorem from_root {root : Cloud (StateM World) Json}
    (route : ReplayRoute journal root Location.root remaining target steps)
    (fuel : Nat) (world : World) :
    (step (modelStorage blobs) (fuel + steps) root target).run journal world =
    (step.walk (modelStorage blobs) root fuel remaining target target).run journal world := by
  have nonempty := route.depth_le
  simp only [Location.size_root] at nonempty
  have notEmpty : target.isEmpty = false := by
    simp [Array.isEmpty, Nat.ne_of_gt (by omega : 0 < target.size)]
  have rootBranch : target[0]!.1 = 0 := route.root_branch
  rw [step]
  simp only [notEmpty, rootBranch, bne_self_eq_false, Bool.false_or,
    Bool.false_eq_true, ↓reduceIte]
  exact route.reconstruct root fuel world

end ReplayRoute
end LeanCloud.Proofs
