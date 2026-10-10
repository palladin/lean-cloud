import LeanCloud.ReplayFaults
import LeanCloud.Proofs.ReplayModel
import LeanCloud.Proofs.Routing

namespace LeanCloud.Proofs.RecoveryCursor
open Lean LeanEff ReplayFaults ReplayModel ReplayInterpreter Routing

variable [rootCodec : Codec α] (source : Cloud WorkerM α)

/-- A typed position reached through already recorded ancestors. The cost counts
source instructions, not storage operations, so retries use the same bound. -/
inductive Cursor : Journal → {β : Type} → Location → (β → Json) → Cloud WorkerM β → Nat → Prop where
  | root : Cursor journal Location.root rootCodec.encode source 0
  | delay {info} (cursor : Cursor journal current encode (.impure info .delay next) cost) :
      Cursor journal current encode (next.apply ()) (cost + 1)
  | exec {info} (codec : Codec β) (label : String) (body : Unit → β)
      (next : ArrsF (Control WorkerM) SourceSiteId β γ)
      (cursor : Cursor journal current encode (.impure info (.command codec (.exec label (fun _ => pure (body ())))) next) cost)
      (present : journal.lookup (ReplayStore.valueKey current) =
        some ⟨Internal.request codec (.exec label (fun _ => pure (body ()) : Unit → WorkerM β)), .success (codec.encode (body ()))⟩)
      (decoded : codec.decode (codec.encode (body ())) = .ok (body ())) :
      Cursor journal current.next encode (next.apply (body ())) (cost + 1)
  | joined {info} (codec : Codec β) (count : Nat) (branches : Fin count → Cloud WorkerM β)
      (next : ArrsF (Control WorkerM) SourceSiteId (Array β) γ) (values : Array β)
      (cursor : Cursor journal current encode (.impure info (.parallel codec count branches) next) cost)
      (present : journal.lookup (ReplayStore.valueKey current) =
        some ⟨⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩, .success (Json.arr (values.map codec.encode))⟩)
      (decoded : (@instCodecArray β codec).decode (Json.arr (values.map codec.encode)) = .ok values)
      (size : values.size = count) :
      Cursor journal current.next encode (next.apply values) (cost + 1)
  | child {info} (codec : Codec β) (count : Nat) (branches : Fin count → Cloud WorkerM β)
      (next : ArrsF (Control WorkerM) SourceSiteId (Array β) γ)
      (cursor : Cursor journal current encode (.impure info (.parallel codec count branches) next) cost)
      (index : Fin count) : Cursor journal (current.child index) codec.encode (branches index) (cost + 1)

theorem Cursor.extend {before after current} {encode : β → Json} {program : Cloud WorkerM β} {cost}
    (cursor : Cursor source before current encode program cost) (extension : Extends before after) :
    Cursor source after current encode program cost := by
  induction cursor with
  | root => exact .root
  | delay cursor ih => exact .delay (ih extension)
  | exec codec label body next cursor present decoded ih => exact .exec codec label body next (ih extension) (extension _ _ present) decoded
  | joined codec count branches next values cursor present decoded size ih =>
    exact .joined codec count branches next values (ih extension) (extension _ _ present) decoded size
  | child codec count branches next cursor index ih => exact .child codec count branches next (ih extension) index

theorem Cursor.route {journal current} {encode : β → Json} {program : Cloud WorkerM β} {cost}
    (cursor : Cursor source journal current encode program cost) :
    Follows Location.root current ∧ current.size ≤ cost + 1 := by
  induction cursor with
  | root => exact ⟨.refl _ (by decide), by decide⟩
  | delay cursor ih => exact ⟨ih.1, by omega⟩
  | exec codec label body next cursor present decoded ih =>
    exact ⟨ih.1.trans (next_follows _ (Nat.lt_of_lt_of_le (by decide) ih.1.depth)), by simpa [LeanCloud.Location.next] using Nat.le_trans ih.2 (Nat.le_succ _)⟩
  | joined codec count branches next values cursor present decoded size ih =>
    exact ⟨ih.1.trans (next_follows _ (Nat.lt_of_lt_of_le (by decide) ih.1.depth)), by simpa [LeanCloud.Location.next] using Nat.le_trans ih.2 (Nat.le_succ _)⟩
  | child codec count branches next cursor index ih =>
    exact ⟨ih.1.trans (child_follows _ (Nat.lt_of_lt_of_le (by decide) ih.1.depth) index), by simpa [LeanCloud.Location.child] using Nat.add_le_add_right ih.2 1⟩

end LeanCloud.Proofs.RecoveryCursor
