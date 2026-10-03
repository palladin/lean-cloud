import LeanCloud.Proofs.BackendJournal
import LeanCloud.Proofs.ConcurrentRead

/-! The physical journal reader over the common Db contract. Each present slot
is durable, while absence is bounded by the beginning of the read. The result
need not correspond to one atomic snapshot of the whole group. -/

namespace LeanCloud.Backend.Proofs.Journal
open Lean LeanEff LeanCloud.Proofs JournalDb JournalAdapter

abbrev Readable := LeanCloud.Proofs.ConcurrentJournal.Readable

def Slot (key : String) (before after : Backend.State) (index : Nat) : Option Exit → Prop
  | none => view before (childKey key index) = none
  | some outcome => view after (childKey key index) = some (toJson outcome)

inductive Slots (key : String) (before after : Backend.State) : List Nat → List (Option Exit) → Prop where
  | nil : Slots key before after [] []
  | cons {index slot indices slots} (head : Slot key before after index slot)
      (tail : Slots key before after indices slots) : Slots key before after (index :: indices) (slot :: slots)

inductive Observation (key : String) (before after : Backend.State) : Option Json → Prop where
  | missing (result : view before (resultKey key) = none)
      (fork : view before (forkKey key) = none) : Observation key before after none
  | cached (outcome : Exit) (stored : view after (resultKey key) = some (toJson outcome)) :
      Observation key before after (some (toJson (Result.completed outcome)))
  | fork (children : Array (Option Exit))
      (uncached : view before (resultKey key) = none)
      (descriptor : view after (forkKey key) = some (toJson children.size))
      (slots : Slots key before after (List.range children.size) children.toList) :
      Observation key before after (some (toJson (Result.settle children)))

theorem Slot.later {key before current after index value}
    (observed : Slot key before current index value) (growth : Grows current after) :
    Slot key before after index value := by
  cases value with
  | none => exact observed
  | some value => exact growth _ _ observed

theorem Slots.length {key before after indices slots}
    (observed : Slots key before after indices slots) : indices.length = slots.length := by
  induction observed with
  | nil => rfl
  | cons head tail ih => simp [ih]

theorem Slots.later {key before current after indices slots}
    (observed : Slots key before current indices slots) (growth : Grows current after) :
    Slots key before after indices slots := by
  induction observed with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.later growth) ih

private abbrev getChild (key : String) (index : Nat)
    (acc : Option (Option Json) × Array (Option Exit)) :
    StateT Unit Replay.M (ForInStep (Option (Option Json) × Array (Option Exit))) := do
  match ← Replay.rawDb.get (childKey key index) with
  | none => return .yield (none, acc.2.push none)
  | some value =>
    match fromJson? (α := Exit) value with
    | .ok outcome => return .yield (none, acc.2.push (some outcome))
    | .error error => return .done (some (some (Json.str s!"Invalid child result: {error}")), acc.2)

private theorem getChild_checked (expected : View) (key : String) (format : Readable expected key)
    (index : Nat) (acc : Array (Option Exit)) (before state : Backend.State)
    (prior : Grows before state) (kept : Valid expected state) :
    Checked expected (getChild key index (none, acc))
      (fun returned final => ∃ slot, returned = .yield (none, acc.push slot) ∧
        Slot key before final index slot) state := by
  unfold getChild
  apply (get_checked expected _ (child_separate key index) state).bind kept
  intro value current currentValid growth stored
  cases value with
  | none =>
    apply checked_pure
    intro final finalValid later
    exact ⟨none, rfl, prior.absent stored⟩
  | some value =>
    obtain ⟨outcome, rfl⟩ := format.child index value (currentValid _ _ stored)
    dsimp only
    rw [exit_roundtrip]
    apply checked_pure
    intro final finalValid later
    exact ⟨some outcome, rfl, later _ _ stored⟩

private theorem getChildren_checked (expected : View) (key : String) (format : Readable expected key)
    (before : Backend.State) (indices : List Nat) (acc : Array (Option Exit))
    (state : Backend.State) (prior : Grows before state) (kept : Valid expected state) :
    Checked expected (forIn indices (none, acc) (getChild key))
      (fun returned final => ∃ slots, returned = (none, acc ++ slots.toArray) ∧
        Slots key before final indices slots) state := by
  induction indices generalizing state acc with
  | nil =>
    apply checked_pure
    intro final finalValid growth
    exact ⟨[], by simp, .nil⟩
  | cons index rest ih =>
    rw [List.forIn_cons]
    apply (getChild_checked expected key format index acc before state prior kept).bind kept
    intro returned current currentValid growth result
    obtain ⟨slot, rfl, observed⟩ := result
    apply (ih (acc.push slot) current (prior.trans growth) currentValid).remember.weaken
    intro returned final result
    obtain ⟨later, slots, rfl, observedTail⟩ := result
    refine ⟨slot :: slots, ?_, .cons (observed.later later) observedTail⟩
    rw [List.push_append_toArray]

theorem get_checked_logical (expected : View) (key : String) (format : Readable expected key)
    (state : Backend.State) (kept : Valid expected state) :
    Checked expected (JournalDb.get Replay.rawDb key)
      (fun answer final => Observation key state final answer) state := by
  unfold JournalDb.get
  apply (get_checked expected _ (result_separate key) state).bind kept
  intro cached current currentValid growth observed
  cases cached with
  | some value =>
    obtain ⟨outcome, rfl⟩ := format.result value (currentValid _ _ observed)
    dsimp only
    rw [exit_roundtrip]
    apply checked_pure
    intro final finalValid later
    exact .cached outcome (later _ _ observed)
  | none =>
    apply (get_checked expected _ (fork_separate key) current).bind currentValid
    intro descriptor after afterValid later found
    cases descriptor with
    | none =>
      apply checked_pure
      intro final finalValid last
      exact .missing observed (growth.absent found)
    | some value =>
      obtain ⟨count, rfl⟩ := format.fork value (afterValid _ _ found)
      dsimp only
      rw [show fromJson? (α := Nat) (toJson count) = .ok count from rfl]
      simp only [state_pure_bind]
      simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
        Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
      apply (getChildren_checked expected key format state (List.range count) #[] after
        (growth.trans later) afterValid).bind afterValid
      intro returned read readValid extended result
      obtain ⟨slots, rfl, seen⟩ := result
      have length : slots.length = count := by simpa using seen.length.symm
      apply checked_pure
      intro final finalValid last
      apply Observation.fork _ observed
      · simpa [length] using last _ _ (extended _ _ found)
      · simpa [length] using seen.later last

end LeanCloud.Backend.Proofs.Journal
