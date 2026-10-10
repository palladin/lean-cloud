import LeanCloud.Proofs.RecoveryBatch
import LeanCloud.RestartingParallelReplay

namespace LeanCloud.Proofs.RecoveryProgress
open ReplayFaults ReplayModel JournalMerge JournalRegion RecoveryStep RecoveryBatch

/-- Finite, immutable storage bounds the amount of unfinished work. -/
def Unique (journal : Journal) := (journal.map Prod.fst).Nodup

theorem unique_after {region before after} (writes : Writes region before after)
    (unique : Unique before) : Unique after := by
  obtain ⟨records, rfl, fresh, absent⟩ := writes
  rw [Unique, List.map_append, List.nodup_append]
  refine ⟨fresh, unique, ?_⟩
  intro key member other present same
  obtain ⟨entry, inRecords, rfl⟩ := List.mem_map.mp member
  obtain ⟨old, inBefore, rfl⟩ := List.mem_map.mp present
  have different := List.lookup_eq_none_iff.mp (absent entry inRecords).1 old inBefore
  simp [same] at different

theorem length_le {before after region} (writes : Writes region before after) : before.length ≤ after.length := by
  obtain ⟨records, rfl, _⟩ := writes
  simp

theorem length_lt {before after region key value} (writes : Writes region before after)
    (absent : before.lookup key = none) (present : after.lookup key = some value) : before.length < after.length := by
  obtain ⟨records, rfl, _⟩ := writes
  cases records with
  | nil => simp [absent] at present
  | cons head tail => simp; omega

theorem size_bound {journal expected : Journal} (unique : Unique journal) (consistent : Extends journal expected) :
    journal.length ≤ expected.length := by
  have subset : journal.map Prod.fst ⊆ expected.map Prod.fst := by
    intro key member
    obtain ⟨entry, inJournal, rfl⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨entry, lookup_member (consistent _ _ (member_lookup unique entry inJournal)), rfl⟩
  simpa using unique.length_le_of_subset subset

/-- One descent reduces depth allowance. Finishing an incomplete group consumes
at least one missing record before its parent is resumed. -/
def rank (expected journal : Journal) (budget depth : Nat) : Nat :=
  (expected.length - journal.length) * (budget + 2) + (budget + 1 - depth)

theorem descend {expected before after : Journal} {budget depth}
    (grows : before.length ≤ after.length) (below : depth < budget + 1) :
    rank expected after budget (depth + 1) < rank expected before budget depth := by
  have smaller : (expected.length - after.length) * (budget + 2) ≤
      (expected.length - before.length) * (budget + 2) := Nat.mul_le_mul_right _ (by omega)
  unfold rank
  omega

theorem advanced {expected before after : Journal} {budget depth}
    (grows : before.length < after.length) (bounded : after.length ≤ expected.length) :
    rank expected after budget depth < rank expected before budget depth := by
  have smaller : (expected.length - after.length + 1) * (budget + 2) ≤
      (expected.length - before.length) * (budget + 2) := Nat.mul_le_mul_right _ (by omega)
  simp only [Nat.add_mul, Nat.one_mul] at smaller
  unfold rank
  omega

def children (location : Location) (count : Nat) : List Assignment :=
  (List.range count).map fun index => ⟨0, location.child index⟩

theorem children_separate (location : Location) (count : Nat) : Separate (children location count) := by
  rw [Separate, children, List.pairwise_map]
  apply List.nodup_range.imp
  intro i j different key first second
  exact Under.separate different (first location i rfl) (second location j rfl)

theorem children_region {location branch count key}
    (same : branch = Proofs.Location.branchStart location) (inside : Region (children location count) key) :
    Owns branch key := by
  obtain ⟨a, member, owned⟩ := inside
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
  exact Owns.child same owned

variable [Codec α] {source : Cloud WorkerM α}

theorem reported_extend {expected budget before middle after assignment reply}
    (valid : Reported source expected budget before middle assignment reply) (grows : Extends middle after) :
    Reported source expected budget before after assignment reply := by
  cases reply with
  | done value => exact ⟨grows _ _ valid.1, valid.2⟩
  | fork location count => exact ⟨valid.1, fun i => (valid.2.1 i).extend grows, valid.2.2⟩

/-- Returned outcomes are backed by the actual journal and agree with the
workflow specification. The list keeps assignment order. -/
inductive Returned (expected journal : Journal) : List Assignment → List Exit → Prop
  | nil : Returned expected journal [] []
  | cons {assignment outcome assignments outcomes} :
      journal.lookup (ReplayStore.returnKey assignment.branchStart) = some ⟨ReplayStore.returnRequest, outcome⟩ →
      expected.lookup (ReplayStore.returnKey assignment.branchStart) = some ⟨ReplayStore.returnRequest, outcome⟩ →
      Returned expected journal assignments outcomes →
      Returned expected journal (assignment :: assignments) (outcome :: outcomes)

theorem Returned.present {expected journal assignments outcomes}
    (returned : Returned expected journal assignments outcomes) {assignment} (member : assignment ∈ assignments) :
    ∃ value, journal.lookup (ReplayStore.returnKey assignment.branchStart) = some ⟨ReplayStore.returnRequest, value⟩ := by
  induction returned with
  | nil => simp at member
  | cons found known rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, found⟩
    · exact ih member

end LeanCloud.Proofs.RecoveryProgress
