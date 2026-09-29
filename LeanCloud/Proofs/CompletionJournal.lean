import LeanCloud.Proofs.CompletionView

/-! The exact finite upper bound for one child completion. This is proof data:
the actual interpreter continues to publish each record separately. -/

namespace LeanCloud.Proofs.ReplayRecovery
open Lean JournalDb JournalLayout JournalAdapter

def completionJournal (initial : Journal) (current parent : Location) (index : Nat)
    (outcome : Exit) (slots : Array (Option Exit)) : Journal :=
  let published := (initial.write (resultKey current.key) (toJson outcome)).write
    (childKey parent.key index) (toJson outcome)
  match Result.settle slots with
  | .suspended _ => published
  | .completed result => published.write (resultKey parent.key) (toJson result)

theorem completionJournal_bounded {initial expected : Journal} {current parent : Location} {index outcome slots}
    (bounded : Extends initial expected)
    (own : expected (resultKey current.key) = some (toJson outcome))
    (child : expected (childKey parent.key index) = some (toJson outcome))
    (cache : ∀ result, Result.settle slots = .completed result →
      expected (resultKey parent.key) = some (toJson result)) :
    Between initial expected (completionJournal initial current parent index outcome slots) := by
  obtain ⟨ownGrowth, ownBound⟩ := extends_write bounded own
  obtain ⟨childGrowth, childBound⟩ := extends_write ownBound child
  unfold completionJournal
  cases settled : Result.settle slots with
  | suspended _ => exact ⟨ownGrowth.trans childGrowth, childBound⟩
  | completed result =>
    obtain ⟨cacheGrowth, cacheBound⟩ := extends_write childBound (cache result settled)
    exact ⟨(ownGrowth.trans childGrowth).trans cacheGrowth, cacheBound⟩

/-- Only the child cache, its parent slot, and a possible parent cache change.
All other records, including unfinished siblings, retain their exact values. -/
theorem completionJournal_fields (initial : Journal) (current parent : Location)
    (index : Nat) (outcome : Exit) (slots : Array (Option Exit))
    (linked : current.parent? = some (parent, index))
    (uncached : initial (resultKey parent.key) = none) :
    let expected := completionJournal initial current parent index outcome slots
    expected (resultKey current.key) = some (toJson outcome) ∧
      expected (childKey parent.key index) = some (toJson outcome) ∧
      expected (resultKey parent.key) =
        (match Result.settle slots with | .suspended _ => none | .completed result => some (toJson result)) ∧
      ∀ key, key ≠ resultKey current.key → key ≠ childKey parent.key index → key ≠ resultKey parent.key →
        expected key = initial key := by
  have distinct : resultKey parent.key ≠ resultKey current.key :=
    fun same => Location.parent_key_ne linked (result_key_injective same)
  unfold completionJournal
  cases settled : Result.settle slots <;>
    simp only [Journal.write, result_ne_child,
      Ne.symm (result_ne_child parent.key parent.key index), distinct, Ne.symm distinct,
      ↓reduceIte, uncached, true_and, eq_self]
  all_goals intro key own child cache
  all_goals simp [own, child, cache]

end LeanCloud.Proofs.ReplayRecovery
