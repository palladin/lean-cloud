import LeanCloud.Proofs.SimulationLogic

/-! Reuse a checked program contract under a stronger shared invariant.
The existing operation guarantees must establish that invariant; strengthening
an invariant alone is not enough. No interpreter code is traversed again. -/

namespace LeanCloud.Proofs.SimulationLogic
open LeanEff Simulation

structure Refinement (first second : Rules δ) : Prop where
  invariant : ∀ world, second.invariant world → first.invariant world
  interference : ∀ before after, second.interference before after → first.interference before after
  orphan : ∀ before after, second.orphanInterference before after → first.orphanInterference before after
  commit : ∀ remote before after, second.invariant before → first.invariant after →
    first.guarantee remote before after → second.invariant after ∧ second.guarantee remote before after

namespace Refinement
variable {first second : Rules δ}

theorem atomic (refinement : Refinement first second)
    {remote : Bool} {operation : δ → α × δ} {pre : δ → Prop} {post : α → δ → Prop}
    (valid : first.Operation remote operation pre post) : second.Operation remote operation pre post := by
  constructor
  · intro before after firstValid lastValid moves holds
    exact valid.waiting before after (refinement.invariant _ firstValid) (refinement.invariant _ lastValid)
      (refinement.interference _ _ moves) holds
  · intro remote before after firstValid lastValid moves holds
    exact valid.orphan remote before after (refinement.invariant _ firstValid) (refinement.invariant _ lastValid)
      (refinement.orphan _ _ moves) holds
  · intro value before after firstValid lastValid moves holds
    exact valid.replying value before after (refinement.invariant _ firstValid) (refinement.invariant _ lastValid)
      (refinement.interference _ _ moves) holds
  · intro world invariant holds
    obtain ⟨preserved, guaranteed, result⟩ := valid.execute world (refinement.invariant _ invariant) holds
    obtain ⟨preserved', guaranteed'⟩ := refinement.commit remote world (operation world).2 invariant preserved guaranteed
    exact ⟨preserved', guaranteed', result⟩

mutual
  theorem program (refinement : Refinement first second) (source : SimM δ α) {pre : δ → Prop} {post : α → δ → Prop}
      (valid : first.Program pre post source) : second.Program pre post source :=
    match source with
    | .pure value => fun world invariant holds => valid world (refinement.invariant _ invariant) holds
    | .impure (.step _ _ _) next => by
      obtain ⟨required, reply, entails, operation, rest⟩ := valid
      exact ⟨required, reply, fun world invariant holds => entails world (refinement.invariant _ invariant) holds,
        refinement.atomic operation, continuation refinement next rest⟩
  termination_by structural source

  theorem continuation (refinement : Refinement first second) (next : ArrsF (Atomic δ) α β)
      {pre : α → δ → Prop} {post : β → δ → Prop}
      (valid : first.Continuation pre post next) : second.Continuation pre post next :=
    match next with
    | .one next => fun value => program refinement (next value) (valid value)
    | .append first rest => by
      obtain ⟨middle, firstValid, restValid⟩ := valid
      exact ⟨middle, continuation refinement first firstValid, continuation refinement rest restValid⟩
  termination_by structural next
end

end Refinement
end LeanCloud.Proofs.SimulationLogic
