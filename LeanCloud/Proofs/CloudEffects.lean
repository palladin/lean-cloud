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
    | EffF.pure _ _ => True
    | .impure _ request next => Request request ∧ Continuation next
  termination_by structural program => program

  def Continuation : ArrsF (Control m) SourceSiteId α β → Prop
    | .one next => ∀ value, Program (next value)
    | .append first rest => Continuation first ∧ Continuation rest
  termination_by structural next => next

  def Request : Control m α → Prop
    | .parallel _ _ branches => ∀ index, Program (branches index)
    | .command _ (.exec _ body) => allowed (body ())
    | .delay | .fail _ | .command _ (.putBlob _) |
        .command _ (.readBlob _) | .command _ (.resolveBlob _) => True
  termination_by structural request => request
end

mutual
  private theorem program_iff (program : Cloud m α) :
      Program allowed program ↔ Effects.Program (Request allowed) program :=
    match program with
    | EffF.pure _ _ => Iff.rfl
    | .impure _ _ next => and_congr Iff.rfl (continuation_iff next)
  termination_by structural program

  private theorem continuation_iff (next : ArrsF (Control m) SourceSiteId α β) :
      Continuation allowed next ↔ Effects.Continuation (Request allowed) next :=
    match next with
    | .one next => forall_congr' fun value => program_iff (next value)
    | .append first rest => and_congr (continuation_iff first) (continuation_iff rest)
  termination_by structural next
end

theorem apply (next : ArrsF (Control m) SourceSiteId α β) (valid : Continuation allowed next) (value : α) :
    Program allowed (next.apply value) := by
  rw [continuation_iff] at valid
  exact (program_iff allowed _).mpr (Effects.apply _ next valid value)

end LeanCloud.Proofs.CloudEffects
