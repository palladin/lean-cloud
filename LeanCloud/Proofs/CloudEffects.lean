import LeanCloud.Core
import LeanCloud.Proofs.Effects

/-! Lift a property of user actions through the existing higher-order Cloud
syntax. Parallel branches and all continuations are included. No new program
representation or restriction is added to the runtime API. -/

namespace LeanCloud.Proofs.CloudEffects
open LeanEff

universe u
variable {m : Type → Type u} (allowed : {α : Type} → m α → Prop)

mutual
  def Program : Cloud m α → Prop
    | EffF.pure _ => True
    | .impure request next => Request request ∧ Continuation next
  termination_by structural program => program

  def Continuation : ArrsF (Control m) α β → Prop
    | .one next => ∀ value, Program (next value)
    | .append first rest => Continuation first ∧ Continuation rest
  termination_by structural next => next

  def Request : Control m α → Prop
    | .parallel _ _ branches => ∀ index, Program (branches index)
    | .choice _ _ branches => ∀ index, Program (branches index)
    | .sequential _ (.exec _ body) => allowed (body ())
    | .delay | .fail _ | .sequential _ (.putBlob _) |
        .sequential _ (.readBlob _) | .sequential _ (.resolveBlob _) => True
  termination_by structural request => request
end

mutual
  private theorem program_iff (program : Cloud m α) :
      Program allowed program ↔ Effects.Program (Request allowed) program :=
    match program with
    | EffF.pure _ => Iff.rfl
    | .impure _ next => and_congr Iff.rfl (continuation_iff next)
  termination_by structural program

  private theorem continuation_iff (next : ArrsF (Control m) α β) :
      Continuation allowed next ↔ Effects.Continuation (Request allowed) next :=
    match next with
    | .one next => forall_congr' fun value => program_iff (next value)
    | .append first rest => and_congr (continuation_iff first) (continuation_iff rest)
  termination_by structural next
end

theorem pure (value : α) : Program allowed (EffF.pure value : Cloud m α) := trivial

theorem bind {program : Cloud m α} {next : α → Cloud m β}
    (valid : Program allowed program) (rest : ∀ value, Program allowed (next value)) :
    Program allowed (EffF.bind program next) := by
  rw [program_iff] at valid ⊢
  exact Effects.bind _ valid (fun value => (program_iff allowed _).mp (rest value))

theorem map (f : α → β) {program : Cloud m α} (valid : Program allowed program) :
    Program allowed (f <$> program) := bind allowed valid (fun _ => trivial)

theorem send {request : Control m α} (valid : Request allowed request) :
    Program allowed (Cloud.send request) := ⟨valid, fun _ => trivial⟩

theorem delay (body : Unit → Cloud m α) (valid : Program allowed (body ())) :
    Program allowed (Cloud.delay body) := by
  unfold Cloud.delay
  apply bind allowed
  · exact ⟨trivial, fun _ => trivial⟩
  · intro value
    cases value
    exact valid

theorem exec [Codec α] (body : Unit → m α) (label : String) (valid : allowed (body ())) :
    Program allowed (Cloud.exec (m := m) (α := α) body label) := send allowed valid

theorem parallel [Codec α] (branches : Array (Cloud m α))
    (valid : ∀ index : Fin branches.size, Program allowed branches[index]) :
    Program allowed (Cloud.parallel branches) := send allowed valid

theorem apply (next : ArrsF (Control m) α β) (valid : Continuation allowed next) (value : α) :
    Program allowed (next.apply value) := by
  rw [continuation_iff] at valid
  exact (program_iff allowed _).mpr (Effects.apply _ next valid value)

end LeanCloud.Proofs.CloudEffects
