import LeanCloud.Proofs.SnapshotWork
import LeanCloud.Proofs.SnapshotPreservation

/-! Changes outside a branch preserve both its snapshot and its processed work. -/

namespace LeanCloud.Proofs
open Lean

mutual
  theorem SnapshotWork.preserve {journal updated : Journal} {program : Cloud Id Json}
      {parent branch command status pending spent}
      {snapshot : ReplaySnapshot journal program parent branch command status pending}
      (cost : SnapshotWork snapshot spent)
      (same : journal.AgreesBetween updated (commandLocation parent branch command) (parent.child (branch + 1))) :
      ∃ result : ReplaySnapshot updated program parent branch command status pending, SnapshotWork result spent := by
    match cost with
    | .pending program parent branch command fresh => exact ⟨_, .pending program parent branch command (fresh.preserve same)⟩
    | .returned value recorded => exact ⟨_, .returned value (same.command.trans recorded)⟩
    | .failed error continuation recorded => exact ⟨_, .failed error continuation (same.command.trans recorded)⟩
    | .delay rest =>
      obtain ⟨_, result⟩ := rest.preserve same
      exact ⟨_, .delay result⟩
    | .parallel children recorded fresh =>
      obtain ⟨_, result⟩ := children.preserve (fun index _ => same.child index)
      exact ⟨_, .parallel result (same.command.trans recorded) (fresh.preserve same.next)⟩
    | .parallelSuccess children collected recorded rest =>
      obtain ⟨_, result⟩ := rest.preserve same.next
      exact ⟨_, .parallelSuccess children collected (same.command.trans recorded) result⟩
    | .parallelFailure continuation children collected recorded =>
      exact ⟨_, .parallelFailure continuation children collected (same.command.trans recorded)⟩
  termination_by structural cost

  theorem ChildrenSnapshotWork.preserve {α : Type} {journal updated : Journal} {codec : Codec α} {count : Nat}
      {branches : Fin count → Cloud Id α} {parent offset outcomes pending spent}
      {snapshot : ChildSnapshots journal codec branches parent offset outcomes pending}
      (cost : ChildrenSnapshotWork snapshot spent)
      (same : ∀ index, offset ≤ index → journal.AgreesBetween updated (parent.child index) (parent.child (index + 1))) :
      ∃ result : ChildSnapshots updated codec branches parent offset outcomes pending, ChildrenSnapshotWork result spent := by
    match cost with
    | .empty codec branches parent offset => exact ⟨_, .empty codec branches parent offset⟩
    | .cons head tail =>
      obtain ⟨_, first⟩ := head.preserve (same offset (Nat.le_refl _))
      obtain ⟨_, rest⟩ := tail.preserve (fun index later => same index (by omega))
      exact ⟨_, .cons first rest⟩
  termination_by structural cost
end

end LeanCloud.Proofs

