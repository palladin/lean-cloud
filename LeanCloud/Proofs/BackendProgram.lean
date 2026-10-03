import LeanCloud.Backend.Execution

/-! A proof view of the existing freer program. It removes only continuation
queue association, retaining every typed request and every possible reply.
The runtime continues to execute `EffF`; this is not another interpreter. -/

namespace LeanCloud.Backend.Proofs
open LeanEff

inductive Program (α : Type) where
  | pure : α → Program α
  | request {β : Type} : Request β → (β → Program α) → Program α

namespace Program

def bind (program : Program α) (next : α → Program β) : Program β :=
  match program with
  | .pure value => next value
  | .request operation rest => .request operation (fun value => (rest value).bind next)

theorem bind_assoc (program : Program α) (first : α → Program β) (second : β → Program γ) :
    (program.bind first).bind second = program.bind (fun value => (first value).bind second) := by
  induction program with
  | pure value => rfl
  | request operation rest ih => simp only [bind]; congr 1; funext value; exact ih value

mutual
  def ofEff (program : M α) : Program α :=
    match program with
    | .pure value => .pure value
    | .impure operation next => .request operation (ofArrs next)
  def ofArrs (next : ArrsF Request α β) (value : α) : Program β :=
    match next with
    | .one next => ofEff (next value)
    | .append first rest => (ofArrs first value).bind (ofArrs rest)
end

theorem ofEff_bind (program : M α) (next : α → M β) :
    ofEff (program >>= next) = (ofEff program).bind (fun value => ofEff (next value)) := by
  cases program <;> rfl

private theorem ofArrs_viewAppend (first : ArrsF Request α β) (rest : ArrsF Request β γ)
    (value : α) :
    (match ArrsF.viewLAppend first rest with
      | .one next => ofEff (next value)
      | .cons next tail => (ofEff (next value)).bind (ofArrs tail)) =
    (ofArrs first value).bind (ofArrs rest) := by
  cases first with
  | one next => rfl
  | append left right =>
    rw [ArrsF.viewLAppend, ofArrs_viewAppend left (.append right rest), ofArrs, bind_assoc]
    rfl
termination_by sizeOf first

private theorem ofArrs_view (next : ArrsF Request α β) (value : α) :
    (match ArrsF.viewL next with
      | .one next => ofEff (next value)
      | .cons next tail => (ofEff (next value)).bind (ofArrs tail)) = ofArrs next value := by
  cases next with
  | one next => rfl
  | append first rest => exact ofArrs_viewAppend first rest value

theorem ofEff_apply (next : ArrsF Request α β) (value : α) :
    ofEff (ArrsF.apply next value) = ofArrs next value := by
  rw [ArrsF.apply]
  have viewed := ofArrs_view next value
  cases h : ArrsF.viewL next with
  | one first => simpa only [h] using viewed
  | cons first rest =>
    change ofEff ((first value) >>= ArrsF.apply rest) = _
    rw [ofEff_bind]
    have ih : (fun value => ofEff (ArrsF.apply rest value)) = ofArrs rest :=
      funext (ofEff_apply rest)
    rw [ih]
    simpa only [h] using viewed
termination_by sizeOf next
decreasing_by simpa [h] using ArrsF.viewL_rest_lt next

def uses (allowed : {β : Type} → Request β → Prop) : Program α → Prop
  | .pure _ => True
  | .request operation next => allowed operation ∧ ∀ value, (next value).uses allowed

theorem uses_bind {allowed : {β : Type} → Request β → Prop}
    {program : Program α} {next : α → Program β}
    (first : program.uses allowed) (rest : ∀ value, (next value).uses allowed) :
    (program.bind next).uses allowed := by
  induction program with
  | pure value => exact rest value
  | request operation next ih => exact ⟨first.1, fun value => ih value (first.2 value)⟩

end Program

def Uses (allowed : {β : Type} → Request β → Prop) (program : M α) : Prop :=
  (Program.ofEff program).uses allowed

theorem Uses.pure (allowed : {β : Type} → Request β → Prop) (value : α) :
    Uses allowed (pure value) := trivial

theorem Uses.request {allowed : {β : Type} → Request β → Prop} (operation : Request α)
    (permitted : allowed operation) : Uses allowed (Backend.request operation) :=
  ⟨permitted, fun _ => trivial⟩

theorem Uses.bind {allowed : {β : Type} → Request β → Prop}
    {program : M α} {next : α → M β}
    (first : Uses allowed program) (rest : ∀ value, Uses allowed (next value)) :
    Uses allowed (program >>= next) := by
  unfold Uses
  rw [Program.ofEff_bind]
  exact Program.uses_bind first rest

theorem Uses.mono {first second : {β : Type} → Request β → Prop} {program : M α}
    (uses : Uses first program) (implies : ∀ {β} (request : Request β), first request → second request) :
    Uses second program := by
  unfold Uses at *
  generalize Program.ofEff program = shape at uses ⊢
  induction shape with
  | pure value => trivial
  | request operation next ih => exact ⟨implies operation uses.1, fun value => ih value (uses.2 value)⟩

end LeanCloud.Backend.Proofs
