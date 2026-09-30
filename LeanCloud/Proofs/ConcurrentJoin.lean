import LeanCloud.Proofs.ConcurrentRead
import LeanCloud.Proofs.CompletionView

/-! Concurrent parallel joins. A durable completion can be represented by a
cache or by all child slots. A post-publication reread must recognize it even
when its individual reads overlap further compatible publications. -/

namespace LeanCloud.Proofs.ConcurrentJournal
open Lean LeanEff Simulation SimulationBackend JournalAdapter JournalDb ReplayRecovery

theorem Slots.at {key before after indices slots}
    (observed : Slots key before after indices slots) (index : Nat) (inside : index < indices.length) :
    Slot key before after indices[index]! slots[index]! := by
  induction observed generalizing index with
  | nil => simp at inside
  | cons head tail ih =>
    cases index with
    | zero => simpa using head
    | succ index => simpa using ih index (by simpa using inside)

/-- A completed group cannot be reconstructed as partial. Every slot was
already durable before the read; a later cache must name the same outcome. -/
theorem Observation.completed {expected : Journal} {key : String} {before after : Durable}
    {answer : Option Json} {outcome : Exit}
    (observed : Observation key before after answer)
    (completed : CompletedAt (view before) key outcome)
    (lower : Valid expected before) (upper : Valid expected after)
    (intended : expected (resultKey key) = some (toJson outcome)) :
    answer = some (toJson (Result.completed outcome)) := by
  cases observed with
  | missing result fork =>
    cases completed with
    | cached recorded => simp [result] at recorded
    | group slots descriptor filled settled => simp [fork] at descriptor
  | cached actual recorded =>
    have same : actual = outcome := toJson_injective exit_roundtrip
      (Option.some.inj ((upper _ _ recorded).symm.trans intended))
    subst actual
    rfl
  | fork children uncached descriptor slots =>
    cases completed with
    | cached recorded => simp [uncached] at recorded
    | group original fork filled settled =>
      have size : children.size = original.size := toJson_injective (α := Nat) (fun _ => rfl)
        (Option.some.inj ((upper _ _ descriptor).symm.trans (lower _ _ fork)))
      have equal : children = original := by
        apply Array.ext size
        intro index leftInside rightInside
        have seen : Slot key before after index children[index]! := by
          simpa [leftInside] using slots.at index (by simpa using leftInside)
        obtain ⟨value, oldSlot, oldStored⟩ := filled index rightInside
        cases slot : children[index]! with
        | none =>
          have absent : view before (childKey key index) = none := by simpa [slot, Slot] using seen
          simp [absent] at oldStored
        | some actual =>
          have stored : view after (childKey key index) = some (toJson actual) := by
            simpa [slot, Slot] using seen
          have same : actual = value := toJson_injective exit_roundtrip
            (Option.some.inj ((upper _ _ stored).symm.trans (lower _ _ oldStored)))
          subst actual
          simpa only [getElem!_pos children index leftInside, getElem!_pos original index rightInside]
            using slot.trans oldSlot.symm
      simp [equal, settled]

/-- Successful publication of a full child array gives durable completion
without requiring a completed-result cache. -/
theorem Publication.completed {key : String} {slots : Array (Option Exit)}
    {returned : Bool × Unit} {state : Durable} {outcome : Exit}
    (published : Publication key (.suspended slots) returned state)
    (settled : Result.settle slots = .completed outcome) :
    CompletedAt (view state) key outcome := by
  obtain ⟨fork, records⟩ := published_fork published.2
  refine .group slots fork ?_ settled
  intro index inside
  obtain ⟨value, present⟩ := Result.settle_filled settled index inside
  exact ⟨value, present, records index inside value present⟩

/-- A stale partial snapshot is sufficient when it publishes the last missing
child. Siblings already durable before this publication supply the other slots. -/
theorem Publication.last_child {key : String} {before after : Durable}
    (outcomes : Array Exit) (index : Fin outcomes.size) (seen : Array (Option Exit))
    (size : seen.size = outcomes.size) {returned : Bool × Unit} {outcome : Exit}
    (published : Publication key (.suspended (seen.set! index.val (some outcomes[index]))) returned after)
    (growth : Grows before after)
    (siblings : ∀ i : Fin outcomes.size, i ≠ index →
      view before (childKey key i.val) = some (toJson outcomes[i]))
    (settled : Result.settle (outcomes.map some) = .completed outcome) :
    CompletedAt (view after) key outcome := by
  obtain ⟨fork, records⟩ := published_fork published.2
  refine .group (outcomes.map some) ?_ ?_ settled
  · simpa [size] using fork
  · intro i inside
    have bound : i < outcomes.size := by simpa using inside
    let child : Fin outcomes.size := ⟨i, bound⟩
    refine ⟨outcomes[child], ?_, ?_⟩
    · simp [getElem!_pos, bound, child]
    · by_cases same : child = index
      · have insideSeen : index.val < seen.size := by simp [size]
        have stored := records index.val (by simpa using insideSeen) outcomes[index]
          (Array.getElem!_set!_self seen index.val (some outcomes[index]) insideSeen)
        simpa [← same, child] using stored
      · exact growth _ _ (siblings child same)

/-- Once completion is durable, the actual reader returns that exact outcome
under arbitrary further compatible journal extensions. -/
theorem get_completed_safe (expected : Journal) (parent : Location)
    (format : Readable expected parent.key) (before state : Durable)
    (prior : Grows before state) (bounded : Valid expected before) (outcome : Exit)
    (completed : CompletedAt (view before) parent.key outcome)
    (intended : expected (resultKey parent.key) = some (toJson outcome)) :
    Safe (Valid expected) Grows
      (fun returned _ => returned.1 = some (toJson (Result.completed outcome)))
      (.ofProgram ((JournalDb.get rawDb parent.key).run ())) state := by
  apply (get_safe expected parent.key format before state prior).weaken
  intro returned current valid observation
  exact observation.completed completed bounded valid intended

/-- Decoding a ready reread and applying the actual final decision in `finish`
requests the parent. This is a wakeup request, not an enqueue acknowledgement. -/
theorem recheck_wakes_parent (expected : Journal) (parent : Location)
    (format : Readable expected parent.key) (before state : Durable)
    (prior : Grows before state) (bounded : Valid expected before) (outcome : Exit)
    (completed : CompletedAt (view before) parent.key outcome)
    (intended : expected (resultKey parent.key) = some (toJson outcome)) :
    Safe (Valid expected) Grows
      (fun returned _ => returned.1.map (fun value =>
        (fromJson? (α := Result) value).map (ReplayInterpreter.Internal.joinResponse parent)) =
          some (.ok (.runnable #[parent])))
      (.ofProgram ((JournalDb.get rawDb parent.key).run ())) state := by
  apply (get_completed_safe expected parent format before state prior bounded outcome completed intended).weaken
  intro returned current valid ready
  simp only [ready, Option.map_some, result_roundtrip, Except.map,
    ReplayInterpreter.Internal.joinResponse]

/-- Connect a successful last-child publication to the subsequent join reread.
The published snapshot may still have missing sibling slots; their immutable
records, rather than that old snapshot, make the group complete. -/
theorem last_child_recheck (expected : Journal) (parent : Location)
    (format : Readable expected parent.key) (before after : Durable)
    (outcomes : Array Exit) (index : Fin outcomes.size) (seen : Array (Option Exit))
    (size : seen.size = outcomes.size) (returned : Bool × Unit)
    (published : Publication parent.key (.suspended (seen.set! index.val (some outcomes[index]))) returned after)
    (growth : Grows before after) (bounded : Valid expected after)
    (siblings : ∀ i : Fin outcomes.size, i ≠ index →
      view before (childKey parent.key i.val) = some (toJson outcomes[i]))
    (outcome : Exit) (settled : Result.settle (outcomes.map some) = .completed outcome)
    (intended : expected (resultKey parent.key) = some (toJson outcome)) :
    Safe (Valid expected) Grows
      (fun reply _ => reply.1.map (fun value =>
        (fromJson? (α := Result) value).map (ReplayInterpreter.Internal.joinResponse parent)) =
          some (.ok (.runnable #[parent])))
      (.ofProgram ((JournalDb.get rawDb parent.key).run ())) after := by
  exact recheck_wakes_parent expected parent format after after (.refl _) bounded outcome
    (published.last_child outcomes index seen size growth siblings settled) intended

end LeanCloud.Proofs.ConcurrentJournal
