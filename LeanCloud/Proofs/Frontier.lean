import LeanCloud.Proofs.Freshness

/-! After reconstruction has reached fresh work, the earlier replay target no
longer affects execution. This lets whole-run proofs describe the current
frontier instead of carrying the old target through each sequential command. -/

namespace LeanCloud.Location

theorem not_enters_of_not_before {current target : Location}
    (atFrontier : current.before target = false) : current.entersChild target = false := by
  simp only [before, Bool.or_eq_false_iff, decide_eq_false_iff_not] at atFrontier
  simp [entersChild, atFrontier.1]

theorem next_not_before {current target : Location} (nonempty : 0 < current.size)
    (atFrontier : current.before target = false) : current.next.before target = false := by
  simp only [before, Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt] at atFrontier ⊢
  simp only [size_next, next_command current nonempty]
  exact ⟨atFrontier.1, by omega⟩

end LeanCloud.Location

namespace LeanCloud.Proofs
open Lean LeanEff ReplayInterpreter.Internal

/-- The remaining behavior is identical for any two replay targets already
reached by the current location. The theorem applies to the actual loop, any
storage, and every fuel budget, including exhaustion. -/
theorem walk_frontier_targets {σ : Type} {m : Type → Type} [Monad m]
    (storage : Storage σ m) (root : Cloud m Json) (fuel : Nat)
    (program : Cloud m Json) (current firstTarget secondTarget : Location)
    (nonempty : 0 < current.size)
    (firstReached : current.before firstTarget = false)
    (secondReached : current.before secondTarget = false) :
    step.walk storage root fuel program current firstTarget =
      step.walk storage root fuel program current secondTarget := by
  induction fuel generalizing program current firstTarget secondTarget with
  | zero => rfl
  | succ fuel ih =>
    have firstNoChild := Location.not_enters_of_not_before firstReached
    have secondNoChild := Location.not_enters_of_not_before secondReached
    have sameCurrent (next : Cloud m Json) :=
      ih next current firstTarget secondTarget nonempty firstReached secondReached
    have sameNext (next : Cloud m Json) :=
      ih next current.next firstTarget secondTarget (Location.next_nonempty current nonempty)
        (Location.next_not_before nonempty firstReached) (Location.next_not_before nonempty secondReached)
    cases program with
    | pure value => simp only [step.walk, firstReached, secondReached]
    | impure request continuation =>
      cases request <;>
        simp only [step.walk, firstReached, secondReached, firstNoChild, secondNoChild,
          Bool.false_and, Bool.false_eq_true, ↓reduceIte, sameCurrent, sameNext]

theorem walk_at_frontier {σ : Type} {m : Type → Type} [Monad m]
    (storage : Storage σ m) (root : Cloud m Json) (fuel : Nat)
    (program : Cloud m Json) (current target : Location)
    (nonempty : 0 < current.size) (atFrontier : current.before target = false) :
    step.walk storage root fuel program current target = step.walk storage root fuel program current current := by
  exact walk_frontier_targets storage root fuel program current target current nonempty atFrontier
    (by simp [Location.before])

end LeanCloud.Proofs
