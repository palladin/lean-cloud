import LeanCloud.Proofs.Checkpoint
import LeanCloud.Proofs.ReplayModel
import LeanCloud.Proofs.Routing

namespace LeanCloud.Proofs.ReplayCursor
open Lean LeanEff ReplayInterpreter

/-- A proof cursor may already lie inside the assigned branch, after replaying
its recorded prefix. This selects the corresponding *actual* interpreter phase;
it does not evaluate effects or add a runtime interpreter. -/
def atPoint [Monad m] (store : ReplayStore m) (blobs : BlobStorage m) (point : Checkpoint)
    (fuel : Nat) (encode : α → Json) (program : Cloud m α) (current : Location) :
    ExceptT CloudError m Progress :=
  if current.size == point.location.size then
    replay store blobs point.branch fuel encode program current
  else reconstruct store blobs point.branch fuel encode program current

theorem at_target [Monad m] (store : ReplayStore m) (blobs : BlobStorage m)
    (point : Checkpoint) (fuel : Nat) (encode : α → Json) (program : Cloud m α) :
    atPoint store blobs point fuel encode program point.location =
      replay store blobs point.branch fuel encode program point.location := by simp [atPoint]

theorem before_branch {point : Checkpoint} {current : Location}
    (branch : point.branch = Location.branchStart point.location)
    (different : current.size ≠ point.location.size) : current ≠ point.branch := by
  intro same
  apply different
  simpa [branch] using congrArg Array.size same

theorem delay [Monad m] (store : ReplayStore m) (blobs : BlobStorage m)
    (point : Checkpoint) (branch : point.branch = Location.branchStart point.location)
    (fuel : Nat) (encode : α → Json) (next : ArrsF (Control m) SourceSiteId Unit α)
    (info : Option SourceSiteId) (current : Location) :
    atPoint store blobs point (fuel + 1) encode (.impure info .delay next) current =
      atPoint store blobs point fuel encode (next.apply ()) current := by
  by_cases same : current.size = point.location.size
  · simp [atPoint, same, replay]
  · simp [atPoint, same, reconstruct, beq_eq_false_iff_ne.mpr (before_branch branch same)]

/-- At a branch boundary this proof cursor is exactly real reconstruction. -/
theorem boundary [Monad m] (store : ReplayStore m) (blobs : BlobStorage m)
    (point : Checkpoint) (branch : point.branch = Location.branchStart point.location)
    (fuel : Nat) (encode : α → Json) (program : Cloud m α) (current : Location)
    (route : Routing.Follows current point.location)
    (start : Location.branchStart current = current) :
    atPoint store blobs point fuel encode program current =
      reconstruct store blobs point.branch fuel encode program current := by
  by_cases depth : current.size = point.location.size
  · have same : point.branch = current := branch.trans ((route.same_branch depth).symm.trans start)
    cases fuel <;> simp [atPoint, depth, same, reconstruct, replay]
  · simp [atPoint, depth]

theorem child [Monad m] (store : ReplayStore m) (blobs : BlobStorage m)
    (point : Checkpoint) (branch : point.branch = Location.branchStart point.location)
    (fuel : Nat) (encode : β → Json) (codec : Codec α) (count : Nat)
    (branches : Fin count → Cloud m α) (next : ArrsF (Control m) SourceSiteId (Array α) β)
    (info : Option SourceSiteId) (current : Location) (index : Fin count)
    (enters : current.entersChild point.location = true)
    (selected : point.location[current.size]!.1 = index.val)
    (route : Routing.Follows (current.child index) point.location) :
    atPoint store blobs point (fuel + 1) encode (.impure info (.parallel codec count branches) next) current =
      atPoint store blobs point fuel codec.encode (branches index) (current.child index) := by
  have depth := ((Routing.entersChild_iff _ _).mp enters).1
  have ancestor : current.entersChild point.branch = true := by
    rw [branch, Routing.enters_branchStart depth, enters]
  have chosen : point.branch[current.size]!.1 = index.val := by
    simpa [branch, Location.branchStart_index _ _ depth] using selected
  rw [boundary store blobs point branch fuel codec.encode (branches index) _ route (by simp)]
  simp [atPoint, Nat.ne_of_lt depth, reconstruct,
    beq_eq_false_iff_ne.mpr (before_branch branch (Nat.ne_of_lt depth)), ancestor, chosen, index.isLt]

open ReplayModel

theorem command (journal : Journal) (blobs : BlobStorage M) (point : Checkpoint)
    (branch : point.branch = Location.branchStart point.location)
    (current : Location) (fuel : Nat) (encode : β → Json) (codec : Codec α)
    (operation : Operation M α) (next : ArrsF (Control M) SourceSiteId α β) (info : Option SourceSiteId)
    (record : ReplayRecord) (wire : Json) (value : α)
    (present : journal.lookup (ReplayStore.valueKey current) = some record)
    (checked : (record.request == Internal.request codec operation) = true)
    (success : record.outcome = .success wire) (decoded : codec.decode wire = .ok value) :
    (atPoint store blobs point (fuel + 1) encode (.impure info (.command codec operation) next) current).run journal =
      (atPoint store blobs point fuel encode (next.apply value) current.next).run journal := by
  by_cases same : current.size = point.location.size
  · simp only [atPoint, same, beq_self_eq_true, ite_true, LeanCloud.Location.next, Array.size_set!, replay]
    simp only [Internal.command, bind_assoc]
    erw [read_then]
    simp [present, Internal.check, checked, success, Internal.resume, Internal.decode, decoded]
  · simp only [atPoint, beq_eq_false_iff_ne.mpr same, LeanCloud.Location.next, Array.size_set!, reconstruct,
      beq_eq_false_iff_ne.mpr (before_branch branch same)]
    simp only [Internal.recorded, bind_assoc]
    erw [read_then]
    simp [present, Internal.check, checked, success, Internal.decode, decoded]

theorem joined (journal : Journal) (blobs : BlobStorage M) (point : Checkpoint)
    (branch : point.branch = Location.branchStart point.location)
    (current : Location) (fuel : Nat) (encode : β → Json) (codec : Codec α) (count : Nat)
    (branches : Fin count → Cloud M α) (next : ArrsF (Control M) SourceSiteId (Array α) β) (info : Option SourceSiteId)
    (record : ReplayRecord) (wire : Json) (values : Array α)
    (route : Routing.Follows current point.location) (skip : current.entersChild point.location = false)
    (present : journal.lookup (ReplayStore.valueKey current) = some record)
    (checked : (record.request == ⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩) = true)
    (success : record.outcome = .success wire)
    (decoded : (@instCodecArray α codec).decode wire = .ok values) (size : values.size = count) :
    (atPoint store blobs point (fuel + 1) encode (.impure info (.parallel codec count branches) next) current).run journal =
      (atPoint store blobs point fuel encode (next.apply values) current.next).run journal := by
  by_cases same : current.size = point.location.size
  · simp only [atPoint, same, beq_self_eq_true, ite_true, LeanCloud.Location.next, Array.size_set!, replay]
    erw [read_then]
    simp [present, Internal.check, checked, success, Internal.resume, Internal.decodeGroup, Internal.decode, decoded, size]
  · have skipped : current.entersChild point.branch = false := by
      rw [branch, Routing.enters_branchStart (by have := route.depth; omega), skip]
    simp only [atPoint, beq_eq_false_iff_ne.mpr same, ite_false, LeanCloud.Location.next, Array.size_set!, reconstruct,
      beq_eq_false_iff_ne.mpr (before_branch branch same), skipped, Bool.false_eq_true, Internal.recorded, bind_assoc]
    erw [read_then]
    simp [present, Internal.check, checked, success, Internal.decodeGroup, Internal.decode, decoded, size]

end LeanCloud.Proofs.ReplayCursor
