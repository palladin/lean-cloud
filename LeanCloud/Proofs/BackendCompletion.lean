import LeanCloud.Proofs.BackendAction
import LeanCloud.Proofs.CompletionView

namespace LeanCloud.Backend.Proofs.Journal
open Lean LeanCloud.Proofs JournalDb JournalAdapter ReplayRecovery ReplayInterpreter.Internal

def Coherent (expected : View) (key : String) : Prop :=
  ∀ slots outcome, JournalAdapter.Published (records key (.suspended slots)) expected →
    Result.settle slots = .completed outcome → expected (resultKey key) = some (toJson outcome)

theorem Slots.at {key before after indices slots}
    (observed : Slots key before after indices slots) (index : Nat) (inside : index < indices.length) :
    Slot key before after indices[index]! slots[index]! := by
  induction observed generalizing index with
  | nil => simp at inside
  | cons head tail ih =>
    cases index with
    | zero => simpa using head
    | succ index => simpa using ih index (by simpa using inside)

theorem Observation.later {key before current after answer}
    (observed : Observation key before current answer) (growth : Grows current after) :
    Observation key before after answer := by
  cases observed with
  | missing result fork => exact .missing result fork
  | cached outcome stored => exact .cached outcome (growth _ _ stored)
  | fork children uncached descriptor slots =>
    exact .fork children uncached (growth _ _ descriptor) (slots.later growth)

/-- A group complete before a read cannot be returned as partial. -/
theorem Observation.completed {expected : View} {key : String} {before after : Backend.State}
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

theorem slots_published {key : String} {before after : Backend.State}
    {slots : Array (Option Exit)}
    (descriptor : view after (forkKey key) = some (toJson slots.size))
    (seen : Slots key before after (List.range slots.size) slots.toList) :
    JournalAdapter.Published (records key (.suspended slots)) (view after) := by
  apply published_suspended key slots (view after) descriptor
  intro index inside outcome present
  have observed : Slot key before after index slots[index]! := by
    simpa [inside] using seen.at index (by simpa using inside)
  simpa [Slot, present] using observed

theorem completed_intended {expected : View} {state : Backend.State} {key : String} {outcome : Exit}
    (coherent : Coherent expected key) (kept : Valid expected state)
    (completed : CompletedAt (view state) key outcome) :
    expected (resultKey key) = some (toJson outcome) := by
  cases completed with
  | cached stored => exact kept _ _ stored
  | group slots fork filled settled =>
    apply coherent slots outcome ?_ settled
    apply published_suspended _ _ _ (kept _ _ fork)
    intro index inside value present
    obtain ⟨actual, same, stored⟩ := filled index inside
    rw [present] at same
    cases same
    exact kept _ _ stored

theorem published_completed {key : String} {slots : Array (Option Exit)}
    {state : Backend.State} {outcome : Exit}
    (published : JournalAdapter.Published (records key (.suspended slots)) (view state))
    (settled : Result.settle slots = .completed outcome) :
    CompletedAt (view state) key outcome := by
  obtain ⟨fork, records⟩ := published_fork published
  refine .group slots fork ?_ settled
  intro index inside
  obtain ⟨value, present⟩ := Result.settle_filled settled index inside
  exact ⟨value, present, records index inside value present⟩

inductive ReadResult (key : String) (before after : Backend.State) : Option Result → Prop where
  | missing : view before (resultKey key) = none → view before (forkKey key) = none →
      ReadResult key before after none
  | completed (outcome : Exit) : CompletedAt (view after) key outcome →
      ReadResult key before after (some (.completed outcome))
  | suspended (slots : Array (Option Exit)) :
      JournalAdapter.Published (records key (.suspended slots)) (view after) →
      (∀ outcome, ¬ CompletedAt (view before) key outcome) →
      Result.settle slots = .suspended slots →
      ReadResult key before after (some (.suspended slots))

theorem ReadResult.later {key before current after result}
    (seen : ReadResult key before current result) (growth : Grows current after) :
    ReadResult key before after result := by
  cases seen with
  | missing absent fork => exact .missing absent fork
  | completed outcome completed => exact .completed outcome (completed.grow growth.reads)
  | suspended slots published incomplete settled =>
    exact .suspended slots (fun entry member => growth _ _ (published entry member)) incomplete settled

theorem observation_result {expected : View} {key : String} {before after : Backend.State}
    (coherent : Coherent expected key) (lower : Valid expected before) (upper : Valid expected after)
    {answer : Option Json} (seen : Observation key before after answer) :
    ∃ result, answer = result.map toJson ∧ ReadResult key before after result := by
  have notCompleted (slots : Array (Option Exit))
      (encoded : answer = some (toJson (Result.suspended slots))) :
      ∀ outcome, ¬ CompletedAt (view before) key outcome := by
    intro outcome ready
    have same := seen.completed ready lower upper (completed_intended coherent lower ready)
    rw [encoded] at same
    have impossible := toJson_injective result_roundtrip (Option.some.inj same)
    cases impossible
  cases seen with
  | missing result fork => exact ⟨none, rfl, .missing result fork⟩
  | cached outcome stored => exact ⟨some (.completed outcome), rfl, .completed outcome (.cached stored)⟩
  | fork slots uncached descriptor observed =>
    have published := slots_published descriptor observed
    cases settled : Result.settle slots with
    | completed outcome =>
      exact ⟨some (.completed outcome), rfl, .completed outcome (published_completed published settled)⟩
    | suspended remaining =>
      have same := Result.settle_suspended settled
      subst remaining
      exact ⟨some (.suspended slots), rfl, .suspended slots published (notCompleted slots (by rw [settled])) settled⟩

theorem load_checked (expected : View) (location : Location)
    (format : Readable expected location.key) (coherent : Coherent expected location.key)
    (state : Backend.State) (kept : Valid expected state) :
    ActionChecked expected (load workerDb location)
      (fun result final => ReadResult location.key state final result) state := by
  have lifted := (get_checked_logical expected location.key format state kept).lift kept
    (fun _ _ _ growth observed => observed.later growth)
  unfold load
  apply lifted.bind kept
  intro answer current valid growth observed
  obtain ⟨result, rfl, seen⟩ := observation_result coherent kept valid observed
  cases result with
  | none => exact action_pure _ _ current fun final finalValid later => seen.later later
  | some result =>
    simp only [Option.map_some, result_roundtrip]
    exact action_pure _ _ current fun final finalValid later => seen.later later

theorem save_checked (expected : View) (location : Location) (result : Result)
    (agrees : Agrees (records location.key result) expected)
    (state : Backend.State) (kept : Valid expected state) :
    ActionChecked expected (save workerDb location result)
      (fun _ final => JournalAdapter.Published (records location.key result) (view final)) state := by
  have lifted := (put_checked expected location.key result agrees state kept).lift kept (by
    intro accepted before after growth result
    exact ⟨result.1, fun entry member => growth _ _ (result.2 entry member)⟩)
  unfold save
  apply lifted.bind kept
  intro accepted current valid growth result
  obtain ⟨rfl, published⟩ := result
  simp only [↓reduceIte]
  exact action_pure _ _ current fun final finalValid later entry member => later _ _ (published entry member)

end LeanCloud.Backend.Proofs.Journal
