import LeanEff.Core
import LeanCloud.Proofs.ArrayEffects
import Init.Data.List.Monadic

/-! A structural property of the requests in an existing lean-eff program.
This is proof bookkeeping, not another interpreter. It also follows every
continuation, so the property survives suspension and a later reply. -/

namespace LeanCloud.Proofs.Effects
open LeanEff

universe u
variable {μ : Type}
variable {e : Type → Type u} (allowed : {α : Type} → e α → Prop)

mutual
  def Program : EffF e μ α → Prop
    | .pure _ _ => True
    | .impure _ request next => allowed request ∧ Continuation next
  termination_by structural program => program

  def Continuation : ArrsF e μ α β → Prop
    | .one next => ∀ value, Program (next value)
    | .append first rest => Continuation first ∧ Continuation rest
  termination_by structural next => next
end

theorem pure (value : α) : Program allowed (EffF.pure info value : EffF e μ α) := trivial

theorem bind {program : EffF e μ α} {next : α → EffF e μ β}
    (first : Program allowed program) (rest : ∀ value, Program allowed (next value)) :
    Program allowed (EffF.bind program next) := by
  cases program with
  | pure info value => exact rest value
  | impure info request continuation => exact ⟨first.1, first.2, rest⟩

theorem map (f : α → β) {program : EffF e μ α} (valid : Program allowed program) :
    Program allowed (f <$> program) := bind allowed valid (fun _ => trivial)

theorem send {request : e α} (valid : allowed request) :
    Program allowed (EffF.send (e := e) (μ := μ) request) := ⟨valid, fun _ => trivial⟩

theorem forIn_list (items : List α) (initial : β) (body : α → β → EffF e μ (ForInStep β))
    (valid : ∀ item state, Program allowed (body item state)) :
    Program allowed (forIn items initial body) := by
  induction items generalizing initial with
  | nil => trivial
  | cons item items ih =>
    rw [List.forIn_cons]
    apply bind allowed (valid item initial)
    intro step
    cases step with
    | done _ => trivial
    | yield next => exact ih next

theorem forIn_array (items : Array α) (initial : β) (body : α → β → EffF e μ (ForInStep β))
    (valid : ∀ item state, Program allowed (body item state)) :
    Program allowed (forIn items initial body) := by
  rw [← Array.forIn_toList]
  exact forIn_list allowed _ _ _ valid

theorem except_bind {program : ExceptT ε (EffF e μ) α} {next : α → ExceptT ε (EffF e μ) β}
    (valid : Program allowed program.run) (rest : ∀ value, Program allowed (next value).run) :
    Program allowed (program >>= next).run := by
  apply bind allowed valid
  intro result
  cases result with
  | error _ => trivial
  | ok value => exact rest value

theorem except_lift {program : EffF e μ α} (valid : Program allowed program) :
    Program allowed (ExceptT.lift (ε := ε) program).run := map allowed Except.ok valid

theorem except_catch {program : ExceptT ε (EffF e μ) α} {handler : ε → ExceptT ε (EffF e μ) α}
    (valid : Program allowed program.run) (handled : ∀ error, Program allowed (handler error).run) :
    Program allowed (ExceptT.tryCatch program handler).run := by
  apply bind allowed valid
  intro result
  cases result with
  | error error => exact handled error
  | ok _ => trivial

theorem except_mapM (items : Array α) (body : α → ExceptT ε (EffF e μ) β)
    (valid : ∀ item, Program allowed (body item).run) :
    Program allowed (items.mapM body).run :=
  array_mapM_preserves (m := ExceptT ε (EffF e μ)) (fun program => Program allowed program.run)
    (fun {_} value => pure allowed (Except.ok (ε := ε) value))
    (fun _ _ => except_bind allowed) items body valid

private def View : ArrsF.ViewL e μ α β → Prop
  | .one next => ∀ value, Program allowed (next value)
  | .cons next rest => (∀ value, Program allowed (next value)) ∧ Continuation allowed rest

private theorem viewLAppend (first : ArrsF e μ α β) (rest : ArrsF e μ β γ)
    (firstValid : Continuation allowed first) (restValid : Continuation allowed rest) :
    View allowed (first.viewLAppend rest) := by
  cases first with
  | one next => exact ⟨firstValid, restValid⟩
  | append first second =>
    exact viewLAppend first (second.append rest) firstValid.1 ⟨firstValid.2, restValid⟩
termination_by sizeOf first

private theorem viewL (next : ArrsF e μ α β) (valid : Continuation allowed next) :
    View allowed next.viewL := by
  cases next with
  | one next => exact valid
  | append first rest => exact viewLAppend allowed first rest valid.1 valid.2

/-- A reply resumes only requests satisfying the original property, regardless
of the association of lean-eff's continuation queue. -/
theorem apply (next : ArrsF e μ α β) (valid : Continuation allowed next) (value : α) :
    Program allowed (next.apply value) := by
  have viewed := viewL allowed next valid
  rw [ArrsF.apply]
  split
  next continuation found =>
    rw [found] at viewed
    exact viewed value
  next continuation rest found =>
    rw [found] at viewed
    exact bind allowed (viewed.1 value) (apply rest viewed.2)
termination_by sizeOf next
decreasing_by
  have smaller := ArrsF.viewL_rest_lt next
  simp_all

end LeanCloud.Proofs.Effects
