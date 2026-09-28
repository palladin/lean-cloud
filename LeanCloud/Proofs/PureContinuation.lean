import LeanCloud.Proofs.Assumptions

namespace LeanCloud.Proofs
open LeanEff

theorem PureProgram.bind {m : Type → Type} {program : Cloud m α} {next : α → Cloud m β}
    (head : PureProgram program) (tail : ∀ value, PureProgram (next value)) :
    PureProgram (EffF.bind program next) := by
  cases program with
  | pure value => exact tail value
  | impure request continuation => exact ⟨head.1, head.2, tail⟩

theorem PureProgram.map {m : Type → Type} {program : Cloud m α}
    (supported : PureProgram program) (f : α → β) : PureProgram (f <$> program) :=
  supported.bind (fun _ => trivial)

private theorem PureContinuation.viewLAppend {m : Type → Type}
    (first : ArrsF (Control m) α β) (rest : ArrsF (Control m) β γ)
    (supported : PureContinuation (.append first rest)) :
    match ArrsF.viewLAppend first rest with
    | .one k => ∀ value, PureProgram (k value)
    | .cons k remaining => (∀ value, PureProgram (k value)) ∧ PureContinuation remaining := by
  match first with
  | .one k => exact supported
  | .append first second =>
    exact PureContinuation.viewLAppend first (.append second rest)
      ⟨supported.1.1, supported.1.2, supported.2⟩
termination_by sizeOf first

private theorem PureContinuation.viewL {m : Type → Type}
    {continuation : ArrsF (Control m) α β} (supported : PureContinuation continuation) :
    match ArrsF.viewL continuation with
    | .one k => ∀ value, PureProgram (k value)
    | .cons k remaining => (∀ value, PureProgram (k value)) ∧ PureContinuation remaining := by
  cases continuation with
  | one k => exact supported
  | append first rest => exact supported.viewLAppend first rest

/-- Reconstructing a continuation retains lawful codecs and excludes unsupported
requests, including when lean-eff reassociates its continuation queue. -/
theorem PureContinuation.apply {m : Type → Type}
    {continuation : ArrsF (Control m) α β} (supported : PureContinuation continuation) (value : α) :
    PureProgram (ArrsF.apply continuation value) := by
  have exposed := supported.viewL
  rw [ArrsF.apply]
  cases view : ArrsF.viewL continuation with
  | one k =>
    simp only [view] at exposed
    exact exposed value
  | cons k rest =>
    simp only [view] at exposed
    exact (exposed.1 value).bind (fun next => exposed.2.apply next)
termination_by sizeOf continuation
decreasing_by simpa [view] using ArrsF.viewL_rest_lt continuation

end LeanCloud.Proofs
