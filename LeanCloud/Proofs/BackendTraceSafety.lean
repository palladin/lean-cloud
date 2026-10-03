import LeanCloud.Proofs.BackendSafety
import LeanCloud.Backend.Recovery

namespace LeanCloud.Backend.Proofs
open Execution

/-- Every point of an abstract execution satisfies the invariant. This uses
only primitive service laws, not the executable model's queue policy. Crashes
may continue forever; fairness is unnecessary for this safety result. -/
theorem trace_safe {valid : Backend.State → Prop} {grows : Backend.State → Backend.State → Prop}
    {post : Nat → α → Backend.State → Prop} {programs : Array (M α)}
    (refl : ∀ state, grows state state)
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    (fresh : ∀ index program, programs[index]? = some program → ∀ state,
      valid state → ProgramSafe valid grows (post index) program state)
    (trace : Trace programs) (initial : AllSafe valid grows post (trace.states 0)) (time : Nat) :
    grows (trace.states 0).services (trace.states time).services ∧
      AllSafe valid grows post (trace.states time) := by
  induction time with
  | zero => exact ⟨refl _, initial⟩
  | succ time ih =>
    have executed := trace.execution time
    cases event : trace.events time with
    | none =>
      simp only [event] at executed
      rw [executed]
      exact ih
    | some action =>
      simp only [event] at executed
      obtain ⟨growth, kept⟩ := Transition.safe refl trans fresh executed ih.2
      exact ⟨trans ih.1 growth, kept⟩

/-- The same invariant supplies monotonicity on every interval, not only
from the initial state. -/
theorem trace_growth {valid : Backend.State → Prop} {grows : Backend.State → Backend.State → Prop}
    {post : Nat → α → Backend.State → Prop} {programs : Array (M α)}
    (refl : ∀ state, grows state state)
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    (fresh : ∀ index program, programs[index]? = some program → ∀ state,
      valid state → ProgramSafe valid grows (post index) program state)
    (trace : Trace programs) (kept : ∀ time, AllSafe valid grows post (trace.states time))
    {first last : Nat} (later : first ≤ last) :
    grows (trace.states first).services (trace.states last).services := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le later
  induction offset with
  | zero => exact refl _
  | succ offset ih =>
    let time := first + offset
    change grows (trace.states first).services (trace.states (time + 1)).services
    have executed := trace.execution time
    cases event : trace.events time with
    | none =>
      simp only [event] at executed
      rw [executed]
      exact ih (by omega)
    | some action =>
      simp only [event] at executed
      exact trans (ih (by omega)) (Transition.safe refl trans fresh executed (kept time)).1

end LeanCloud.Backend.Proofs
