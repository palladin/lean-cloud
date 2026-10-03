import LeanCloud.Proofs.BackendTraceSafety
import LeanCloud.Backend.Replay
import LeanCloud.Proofs.JournalRecovery
import LeanCloud.Proofs.SimulationHistory

/-! The real journal primitives over the shared service laws. A fixed expected
journal describes agreement of writes; the workflow proof will derive it from
the pure program. No service law assumes that a worker returns successfully. -/

namespace LeanCloud.Backend.Proofs.Journal
open Lean LeanEff LeanCloud.Proofs

abbrev View := String → Option Json

/-- Location records and the run's completion record share the same Db. The
step proof projects out the completion key; the queue proof checks it separately. -/
def view (state : Backend.State) (key : String) : Option Json :=
  if key = CompletionStore.key then none else Backend.Db.view state key

theorem view_eq (state : Backend.State) {key : String} (separate : key ≠ CompletionStore.key) :
    view state key = Backend.Db.view state key := by simp [view, separate]

theorem result_separate (key : String) : JournalDb.resultKey key ≠ CompletionStore.key := by
  intro same
  have member : '/' ∈ (JournalDb.resultKey key).toList := by
    simp only [JournalDb.resultKey, String.toList_append, List.mem_append]
    exact .inr (by decide)
  rw [same] at member
  exact (by decide : '/' ∉ CompletionStore.key.toList) member

theorem fork_separate (key : String) : JournalDb.forkKey key ≠ CompletionStore.key := by
  intro same
  have member : '/' ∈ (JournalDb.forkKey key).toList := by
    simp only [JournalDb.forkKey, String.toList_append, List.mem_append]
    exact .inr (by decide)
  rw [same] at member
  exact (by decide : '/' ∉ CompletionStore.key.toList) member

theorem child_separate (key : String) (index : Nat) : JournalDb.childKey key index ≠ CompletionStore.key := by
  intro same
  have member : '/' ∈ (JournalDb.childKey key index).toList := by
    simp only [JournalDb.childKey, String.toList_append, List.mem_append]
    exact .inl (.inr (by decide))
  rw [same] at member
  exact (by decide : '/' ∉ CompletionStore.key.toList) member

def history (state : Backend.State) : Simulation.History.Store (List (String × Json)) :=
  ⟨state.records, state.pastRecords⟩

structure Grows (before after : Backend.State) : Prop where
  reads : ∀ key value, Journal.view before key = some value → Journal.view after key = some value
  lineage : Simulation.History.Grows (Journal.history before) (Journal.history after)

instance {before after : Backend.State} : CoeFun (Grows before after)
    (fun _ => ∀ key value, view before key = some value → view after key = some value) := ⟨Grows.reads⟩

instance {before after : Backend.State} :
    Coe (Grows before after) (JournalAdapter.Extends (view before) (view after)) := ⟨Grows.reads⟩

def Valid (expected : View) (state : Backend.State) : Prop :=
  ∀ key value, view state key = some value → expected key = some value

theorem Grows.refl (state : Backend.State) : Grows state state := ⟨fun _ _ stored => stored, .refl _⟩

theorem Grows.snapshot (state : Backend.State) : Grows state.snapshot.state state :=
  ⟨fun _ _ stored => stored, .refl _⟩

theorem Grows.to_snapshot {before after : Backend.State} (growth : Grows before after) :
    Grows before after.snapshot.state := ⟨growth.reads, growth.lineage⟩

theorem Grows.trans {first middle last : Backend.State}
    (a : Grows first middle) (b : Grows middle last) : Grows first last :=
  ⟨fun key value stored => b key value (a key value stored), a.lineage.trans b.lineage⟩

def snapshotView (records : List (String × Json)) : View := view { records }

def Ordered (state : Backend.State) : Prop :=
  Simulation.History.Ordered (fun first last => JournalAdapter.Extends (snapshotView first) (snapshotView last)) (history state)

theorem Ordered.initial (state : Backend.State) (empty : state.pastRecords = []) : Ordered state := by
  unfold Ordered history
  rw [empty]
  exact Simulation.History.Ordered.initial _ _

theorem Ordered.write {before after : Backend.State} (ordered : Ordered before)
    (growth : Grows before after) (recorded : after.pastRecords = before.records :: before.pastRecords) :
    Ordered after := by
  have added := Simulation.History.Ordered.append ordered
    (fun _ => JournalAdapter.Extends.refl _) (fun a b => a.trans b) growth.reads
  simpa only [Ordered, history, Simulation.History.Store.states, recorded] using added

theorem Grows.between {first middle last : Backend.State}
    (ordered : Ordered last) (a : Grows first last) (b : Grows middle last)
    (length : first.pastRecords.length ≤ middle.pastRecords.length) : Grows first middle := by
  have before : Simulation.History.Grows (history first) (history middle) := a.lineage.between b.lineage length
  exact ⟨(ordered.earlier b.lineage).growth (fun _ => JournalAdapter.Extends.refl _) before, before⟩

theorem Grows.latest {count : Nat} (nonempty : 0 < count)
    (observed : Fin count → Backend.State) (final : Backend.State) (ordered : Ordered final)
    (before : ∀ i, Grows (observed i) final) : ∃ latest, ∀ i, Grows (observed i) (observed latest) := by
  let lengths := List.ofFn fun i => (observed i).pastRecords.length
  have nonnil : lengths ≠ [] := by
    intro empty
    have := congrArg List.length empty
    simp [lengths] at this
    omega
  obtain ⟨latest, largest⟩ := List.mem_ofFn.mp (List.max_mem nonnil)
  refine ⟨latest, fun i => Grows.between ordered (before i) (before latest) ?_⟩
  rw [largest]
  exact List.le_max_of_mem (l := lengths) (List.mem_ofFn.mpr ⟨i, rfl⟩)

theorem Grows.absent {before after : Backend.State} (growth : Grows before after)
    {key : String} (absent : view after key = none) : view before key = none := by
  cases stored : view before key with
  | none => rfl
  | some value => have := growth key value stored; simp [absent] at this

/-- Compatibility forces a successful response. The write may use a different
physical representation; only its observable single-key behavior is needed. -/
theorem put_preserves {expected : View} {key : String} {value : Json}
    (separate : key ≠ CompletionStore.key) (intended : expected key = some value)
    {before after : Backend.State} {accepted : Bool}
    (valid : Valid expected before) (law : Backend.Db.Put key value before accepted after) :
    accepted = true ∧ Valid expected after ∧ Grows before after ∧ view after key = some value := by
  have compatible : Backend.Db.Compatible key value before := by
    cases stored : view before key with
    | none => exact .inl ((view_eq before separate).symm.trans stored)
    | some old => exact .inr ((view_eq before separate).symm.trans
        (stored.trans ((valid key old stored).symm.trans intended)))
  cases accepted with
  | false => exact False.elim (law.1 compatible)
  | true =>
    rcases law with ⟨stored, unchanged, queue, recorded⟩
    have stored : view after key = some value := (view_eq after separate).trans stored
    have unchanged : ∀ other, other ≠ key → view after other = view before other := by
      intro other different
      by_cases reserved : other = CompletionStore.key
      · simp [view, reserved]
      · simpa only [view_eq after reserved, view_eq before reserved] using unchanged other different
    refine ⟨rfl, ?_, ?_, stored⟩
    · intro other actual found
      by_cases same : other = key
      · subst other
        have : actual = value := Option.some.inj (found.symm.trans stored)
        simpa [this] using intended
      · exact valid other actual ((unchanged other same).symm.trans found)
    · refine ⟨?_, ?_⟩
      · intro other actual found
        by_cases same : other = key
        · subst other
          have : actual = value := Option.some.inj ((valid key actual found).symm.trans intended)
          simpa [this] using stored
        · exact (unchanged other same).trans found
      · exact ⟨[after.records], by simp [history, Simulation.History.Store.states, recorded]⟩

abbrev run (action : StateT Unit Replay.M α) : Backend.M (Except String (α × Unit)) :=
  (action.run ()).run

theorem state_pure_bind (value : α) (next : α → StateT Unit Replay.M β) :
    (pure value >>= next) = next value := rfl

/-- An actual raw read can return a stale absence, but a present value persists.
There is no snapshot requirement for a sequence of different-key reads. -/
theorem get_safe (expected : View) (key : String) (separate : key ≠ CompletionStore.key)
    (state : Backend.State) :
    ProgramSafe (Valid expected) Grows
      (fun returned final => ∃ value, returned = .ok (value, ()) ∧
        match value with
        | none => view state key = none
        | some value => view final key = some value)
      (run (Replay.rawDb.get key)) state := by
  apply Safe.request
  · intro current value after kept growth law
    obtain ⟨same, rfl⟩ := law
    exact ⟨kept, .refl _⟩
  · intro current value after kept growth law
    obtain ⟨observed, same⟩ := law
    rw [← view_eq current separate] at observed
    subst after
    subst value
    apply Safe.pure
    intro final finalValid later
    refine ⟨view current key, rfl, ?_⟩
    cases stored : view current key with
    | none => exact growth.absent stored
    | some value => exact later key value stored

theorem rawPut_safe (expected : View) (key : String) (value : Json)
    (separate : key ≠ CompletionStore.key) (intended : expected key = some value) (state : Backend.State) :
    ProgramSafe (Valid expected) Grows
      (fun returned final => returned = .ok (true, ()) ∧ view final key = some value)
      (run (Replay.rawDb.put key value)) state := by
  apply Safe.request
  · intro current accepted after kept growth law
    have proved := put_preserves separate intended kept law
    exact ⟨proved.2.1, proved.2.2.1⟩
  · intro current accepted after kept growth law
    obtain ⟨rfl, afterValid, later, stored⟩ := put_preserves separate intended kept law
    exact .pure fun final finalValid last => ⟨rfl, last key value stored⟩

/-- This is `JournalDb.putSame`, including the absent-read/write race. A reply
saved before another writer publishes is safe to resume afterwards. -/
theorem putSame_safe (expected : View) (key : String) (value : Json)
    (separate : key ≠ CompletionStore.key) (intended : expected key = some value)
    (reflexive : (value == value) = true)
    (state : Backend.State) :
    ProgramSafe (Valid expected) Grows
      (fun returned final => returned = .ok (true, ()) ∧ view final key = some value)
      (run (JournalDb.putSame Replay.rawDb key value)) state := by
  apply Safe.request
  · intro current old after kept growth law
    obtain ⟨same, rfl⟩ := law
    exact ⟨kept, .refl _⟩
  · intro current old after kept growth law
    obtain ⟨observed, same⟩ := law
    rw [← view_eq current separate] at observed
    subst after
    subst old
    cases stored : view current key with
    | none =>
      change Safe _ _ _ (Program.ofEff (run (Replay.rawDb.put key value))) current
      exact rawPut_safe expected key value separate intended current
    | some old =>
      have same : old = value := Option.some.inj ((kept key old stored).symm.trans intended)
      subst old
      change Safe _ _ _ (.pure (Except.ok (ε := String) ((value == value), ()))) current
      rw [reflexive]
      exact .pure fun final finalValid later => ⟨rfl, later key value stored⟩

/-- A successful call to the actual backend action, with a durable result
property. Infrastructure failure is excluded by proof, not erased from its type. -/
def Checked (expected : View) (action : StateT Unit Replay.M α)
    (post : α → Backend.State → Prop) (state : Backend.State) : Prop :=
  ProgramSafe (Valid expected) Grows
    (fun returned final => ∃ value, returned = .ok (value, ()) ∧ post value final)
    (run action) state

theorem checked_pure {expected : View} (value : α) (post : α → Backend.State → Prop)
    (state : Backend.State)
    (done : ∀ final, Valid expected final → Grows state final → post value final) :
    Checked expected (pure value) post state :=
  .pure fun final kept growth => ⟨value, rfl, done final kept growth⟩

theorem Checked.bind {expected : View} {action : StateT Unit Replay.M α}
    {next : α → StateT Unit Replay.M β} {first : α → Backend.State → Prop}
    {post : β → Backend.State → Prop} {state : Backend.State}
    (safe : Checked expected action first state) (kept : Valid expected state)
    (resume : ∀ value current, Valid expected current → Grows state current → first value current →
      Checked expected (next value) post current) :
    Checked expected (action >>= next) post state := by
  apply ProgramSafe.bind Grows.refl (fun first last => first.trans last) safe kept
  intro returned current currentValid growth result
  obtain ⟨value, rfl, result⟩ := result
  exact resume value current currentValid growth result

theorem Checked.weaken {expected : View} {action : StateT Unit Replay.M α}
    {first post : α → Backend.State → Prop} {state : Backend.State}
    (safe : Checked expected action first state)
    (implies : ∀ value final, first value final → post value final) :
    Checked expected action post state := by
  apply Safe.weaken safe
  intro returned final kept result
  obtain ⟨value, rfl, result⟩ := result
  exact ⟨value, rfl, implies value final result⟩

theorem Checked.remember {expected : View} {action : StateT Unit Replay.M α}
    {post : α → Backend.State → Prop} {state : Backend.State}
    (safe : Checked expected action post state) :
    Checked expected action (fun value final => Grows state final ∧ post value final) state := by
  apply Safe.weaken (Safe.remember safe (fun first last => first.trans last) state (.refl _))
  intro returned final kept result
  obtain ⟨growth, value, rfl, done⟩ := result
  exact ⟨value, rfl, growth, done⟩

theorem get_checked (expected : View) (key : String) (separate : key ≠ CompletionStore.key)
    (state : Backend.State) :
    Checked expected (Replay.rawDb.get key)
      (fun value final => match value with
        | none => view state key = none
        | some value => view final key = some value) state :=
  get_safe expected key separate state

theorem putSame_checked (expected : View) (key : String) (value : Json)
    (separate : key ≠ CompletionStore.key) (intended : expected key = some value)
    (reflexive : (value == value) = true)
    (state : Backend.State) :
    Checked expected (JournalDb.putSame Replay.rawDb key value)
      (fun accepted final => accepted = true ∧ view final key = some value) state := by
  apply Safe.weaken (putSame_safe expected key value separate intended reflexive state)
  intro returned final kept result
  obtain ⟨rfl, stored⟩ := result
  exact ⟨true, rfl, rfl, stored⟩

open JournalAdapter

private abbrev putChild (key : String) (children : Array (Option Exit))
    (index : Nat) (_ : Option Bool × Unit) : StateT Unit Replay.M (ForInStep (Option Bool × Unit)) := do
  match children[index]! with
  | some outcome =>
    if ← JournalDb.putSame Replay.rawDb (JournalDb.childKey key index) (toJson outcome) then
      return .yield (none, ())
    else return .done (some false, ())
  | _ => return .yield (none, ())

private theorem putChild_checked (expected : View) (key : String) (children : Array (Option Exit))
    (index : Nat) (agrees : Agrees (([index]).filterMap (childRecord key children)) expected)
    (state : Backend.State) (kept : Valid expected state) :
    Checked expected (putChild key children index (none, ()))
      (fun returned final => returned = .yield (none, ()) ∧
        JournalAdapter.Published ([index].filterMap (childRecord key children)) (view final)) state := by
  cases slot : children[index]! with
  | none =>
    simp only [putChild, slot]
    apply checked_pure
    intro final finalValid growth
    exact ⟨rfl, by simp [JournalAdapter.Published, childRecord, slot]⟩
  | some outcome =>
    have intended := agrees (JournalDb.childKey key index, toJson outcome) (by simp [childRecord, slot])
    simp only [putChild, slot]
    apply (putSame_checked expected _ _ (child_separate key index) intended.1 intended.2 state).bind kept
    intro accepted current currentValid growth result
    obtain ⟨rfl, written⟩ := result
    simp only [↓reduceIte]
    apply checked_pure
    intro final finalValid later
    refine ⟨rfl, ?_⟩
    simpa [JournalAdapter.Published, childRecord, slot] using later _ _ written

private theorem putChildren_checked (expected : View) (key : String)
    (children : Array (Option Exit)) (indices : List Nat)
    (agrees : Agrees (indices.filterMap (childRecord key children)) expected)
    (state : Backend.State) (kept : Valid expected state) :
    Checked expected (forIn indices (none, ()) (putChild key children))
      (fun returned final => returned = (none, ()) ∧
        JournalAdapter.Published (indices.filterMap (childRecord key children)) (view final)) state := by
  induction indices generalizing state with
  | nil =>
    apply checked_pure
    intro final finalValid growth
    exact ⟨rfl, by simp [JournalAdapter.Published]⟩
  | cons index rest ih =>
    have head : Agrees ([index].filterMap (childRecord key children)) expected := by
      intro entry member
      apply agrees entry
      change entry ∈ ([index] ++ rest).filterMap (childRecord key children)
      rw [List.filterMap_append, List.mem_append]
      exact .inl member
    have tail : Agrees (rest.filterMap (childRecord key children)) expected := by
      intro entry member
      apply agrees entry
      simp only [List.filterMap_cons]
      cases childRecord key children index <;> simp [member]
    rw [List.forIn_cons]
    apply (putChild_checked expected key children index head state kept).bind kept
    intro returned current currentValid growth result
    obtain ⟨rfl, written⟩ := result
    apply (ih tail current currentValid).remember.weaken
    intro returned final result
    obtain ⟨later, rfl, published⟩ := result
    refine ⟨rfl, ?_⟩
    intro entry member
    change entry ∈ ([index] ++ rest).filterMap (childRecord key children) at member
    rw [List.filterMap_append, List.mem_append] at member
    rcases member with head | tail
    · exact later _ _ (written entry head)
    · exact published entry tail

/-- The actual physical publisher is safe under individually atomic Db calls.
Its whole batch is not atomic: any prefix may survive an interrupted attempt. -/
theorem put_checked (expected : View) (key : String) (result : Result)
    (agrees : Agrees (records key result) expected)
    (state : Backend.State) (kept : Valid expected state) :
    Checked expected (JournalDb.put Replay.rawDb key (toJson result))
      (fun accepted final => accepted = true ∧
        JournalAdapter.Published (records key result) (view final)) state := by
  unfold JournalDb.put
  rw [result_roundtrip]
  simp only [state_pure_bind]
  cases result with
  | completed outcome =>
    have intended := agrees (JournalDb.resultKey key, toJson outcome) (by simp [records])
    apply (putSame_checked expected _ _ (result_separate key) intended.1 intended.2 state).weaken
    intro accepted final result
    simpa [JournalAdapter.Published, records] using result
  | suspended children =>
    have head := agrees (JournalDb.forkKey key, toJson children.size) (by simp [records])
    have tail : Agrees ((List.range children.size).filterMap (childRecord key children)) expected :=
      fun entry member => agrees entry (by simp [records, member])
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
    apply (putSame_checked expected _ _ (fork_separate key) head.1 head.2 state).bind kept
    intro accepted current currentValid growth result
    obtain ⟨rfl, descriptor⟩ := result
    simp only [↓reduceIte]
    apply (putChildren_checked expected key children _ tail current currentValid).bind currentValid
    intro returned after afterValid later result
    obtain ⟨rfl, published⟩ := result
    apply checked_pure
    intro final finalValid last
    refine ⟨rfl, ?_⟩
    intro entry member
    simp only [records, List.mem_cons] at member
    rcases member with rfl | member
    · exact last _ _ (later _ _ descriptor)
    · exact last _ _ (published entry member)

end LeanCloud.Backend.Proofs.Journal
