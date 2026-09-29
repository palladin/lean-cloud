import LeanCloud.Proofs.JournalAdapter
import LeanCloud.Proofs.CrashSpec

/-! Crash safety and idempotence of the actual adapter over individually
atomic reads and writes. Attempts are serialized; same-key agreement is stated
explicitly. No transaction over an entire publication is assumed. -/

namespace LeanCloud.Proofs.JournalAdapter
open Lean JournalDb CrashModel CrashRecovery

/-- Every previously recorded value is retained, including records outside the
current publication. -/
def Extends (before after : Journal) : Prop :=
  ∀ key value, before key = some value → after key = some value

theorem Extends.refl (journal : Journal) : Extends journal journal := fun _ _ h => h

theorem Extends.trans {a b c : Journal} (ab : Extends a b) (bc : Extends b c) : Extends a c :=
  fun k v h => bc k v (ab k v h)

def Published (entries : List Record) (journal : Journal) : Prop :=
  ∀ entry ∈ entries, journal entry.1 = some entry.2

/-- The intended records agree with a fixed journal. JSON comparison is partial
in Lean, so reflexivity on these encoded values is an explicit hypothesis. -/
def Agrees (entries : List Record) (expected : Journal) : Prop :=
  ∀ entry ∈ entries, expected entry.1 = some entry.2 ∧ (entry.2 == entry.2) = true

/-- Raw callbacks use the same atomic crash boundary as the recovery tests. -/
def atomicDb : Db Unit (M Journal) where
  get key _ := atomic fun journal => ((journal key, ()), journal)
  put key value _ := atomic fun journal => ((true, ()), journal.write key value)

def writeOne (key : String) (value : Json) : M Journal Bool := do
  let existing ← atomic fun journal => (journal key, journal)
  match existing with
  | some existing => pure (existing == value)
  | none => atomic fun journal => (true, journal.write key value)

def publication : List Record → M Journal Bool
  | [] => pure true
  | (key, value) :: rest => do
    if ← writeOne key value then publication rest else pure false

theorem putSame_atomic (key : String) (value : Json) :
    (putSame atomicDb key value) () = (fun accepted => (accepted, ())) <$> writeOne key value := by
  change (putSame atomicDb key value).run () = _
  unfold putSame
  rw [StateT.run_bind]
  simp only [atomicDb, StateT.run]
  rw [atomic_map (fun journal : Journal => (journal key, journal)) (fun value => (value, ()))]
  unfold writeOne
  simp only [bind_map_left, map_bind]
  congr 1
  funext existing
  cases existing
  · exact atomic_map (fun journal : Journal => (true, journal.write key value))
      (fun accepted => (accepted, ()))
  · rfl

theorem publish_atomic (entries : List Record) :
    (publish atomicDb entries) () = (fun accepted => (accepted, ())) <$> publication entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨key, value⟩
    change (publish atomicDb ((key, value) :: rest)).run () = _
    unfold publish
    rw [StateT.run_bind]
    simp only [StateT.run, putSame_atomic, publication, bind_map_left, map_bind]
    congr 1
    funext accepted
    cases accepted
    · rfl
    · simpa only [↓reduceIte] using ih

/-- Connect the crash proof to `JournalDb.put`, not merely to a similar model. -/
theorem put_atomic (key : String) (result : Result) :
    (JournalDb.put atomicDb key (toJson result)) () =
      (fun accepted => (accepted, ())) <$> publication (records key result) := by
  rw [put_eq_publish, publish_atomic]

/-- Adding a prescribed value cannot change any previously accepted value. -/
theorem extends_write {initial expected : Journal} (bounded : Extends initial expected)
    {key value} (intended : expected key = some value) :
    Extends initial (initial.write key value) ∧ Extends (initial.write key value) expected := by
  constructor
  · intro other old recorded
    by_cases same : other = key
    · subst other
      have equal := (bounded _ _ recorded).symm.trans intended
      cases equal
      exact Journal.read_write _ _ _
    · simpa [Journal.write, same] using recorded
  · intro other old recorded
    by_cases same : other = key
    · subst other
      rw [Journal.read_write] at recorded
      cases recorded
      exact intended
    · exact bounded _ _ (by simpa [Journal.write, same] using recorded)

/-- A compatible write preserves any invariant closed under immutable journal
extension. A crash may happen at the read or on either side of the write. -/
theorem writeOne_spec (expected : Journal) (invariant : Journal → Prop)
    (key : String) (value : Json) (intended : expected key = some value)
    (reflexive : (value == value) = true)
    (bounded : ∀ journal, invariant journal → Extends journal expected)
    (stable : ∀ before after, invariant before → Extends before after →
      Extends after expected → invariant after) :
    Triple invariant (writeOne key value)
      (fun accepted journal => accepted = true ∧ invariant journal ∧ journal key = some value)
      invariant := by
  unfold writeOne
  apply Triple.bind (Triple.atomic (fun journal : Journal => (journal key, journal))
    (post := fun existing journal => existing = journal key ∧ invariant journal)
    (fun _ h => ⟨rfl, h⟩) (fun _ h => h) (fun _ h => h))
  intro existing
  cases existing with
  | none =>
    have kept (journal : Journal) (valid : none = journal key ∧ invariant journal) :
        invariant (journal.write key value) := by
      obtain ⟨growth, bound⟩ := extends_write (bounded _ valid.2) intended
      exact stable _ _ valid.2 growth bound
    exact Triple.atomic _ (fun journal h => ⟨rfl, kept journal h, Journal.read_write _ _ _⟩)
      (fun _ h => h.2) kept
  | some old =>
    intro start ⟨observed, valid⟩
    have equal : old = value := Option.some.inj ((bounded _ valid _ _ observed.symm).symm.trans intended)
    subst old
    simp only [reflexive]
    exact ⟨Nat.le_refl _, rfl, valid, observed.symm⟩

/-- Publishing a list composes the one-record specification. Earlier entries
remain published, and the same invariant holds on success and interruption. -/
theorem publication_spec (expected : Journal) (invariant : Journal → Prop)
    (entries : List Record) (agrees : Agrees entries expected)
    (bounded : ∀ journal, invariant journal → Extends journal expected)
    (stable : ∀ before after, invariant before → Extends before after →
      Extends after expected → invariant after) :
    Triple invariant (publication entries)
      (fun accepted journal => accepted = true ∧ invariant journal ∧ Published entries journal)
      invariant := by
  induction entries generalizing invariant with
  | nil =>
    exact (Triple.pure _ true).weaken (fun _ h => h)
      (fun _ _ h => ⟨h.1, h.2, by simp [Published]⟩) (fun _ h => h)
  | cons entry rest ih =>
    obtain ⟨intended, reflexive⟩ := agrees entry (by simp)
    unfold publication
    apply Triple.bind (writeOne_spec expected invariant entry.1 entry.2 intended reflexive bounded stable)
    intro accepted start ⟨acceptedTrue, valid, recorded⟩
    subst accepted
    simp only [↓reduceIte]
    apply (ih (fun journal => invariant journal ∧ journal entry.1 = some entry.2)
      (fun e member => agrees e (List.mem_cons_of_mem _ member)) (fun _ h => bounded _ h.1)
      (fun _ _ h growth bound => ⟨stable _ _ h.1 growth bound, growth _ _ h.2⟩)).weaken
        (post' := fun accepted journal => accepted = true ∧ invariant journal ∧ Published (entry :: rest) journal)
        (fun _ h => h) ?_ (fun _ h => h.1) start ⟨valid, recorded⟩
    intro result journal ⟨accepted, kept, published⟩
    refine ⟨accepted, kept.1, ?_⟩
    intro e member
    rcases List.mem_cons.mp member with rfl | member
    · exact kept.2
    · exact published e member

/-- A single attempt of the actual adapter, discarding only its unit handle. -/
def attempt (key : String) (result : Result) : M Journal Bool :=
  Prod.fst <$> (JournalDb.put atomicDb key (toJson result)) ()

theorem attempt_eq (key : String) (result : Result) :
    attempt key result = publication (records key result) := by
  simp [attempt, put_atomic, Functor.map_map]

/-- Actual `JournalDb.put`: success publishes every record, while both return
and crash retain all earlier records and stay below the agreed journal. -/
theorem put_spec (expected initial : Journal) (key : String) (result : Result)
    (agrees : Agrees (records key result) expected) :
    Triple (fun journal => Extends initial journal ∧ Extends journal expected) (attempt key result)
      (fun accepted journal => accepted = true ∧
        (Extends initial journal ∧ Extends journal expected) ∧ Published (records key result) journal)
      (fun journal => Extends initial journal ∧ Extends journal expected) := by
  rw [attempt_eq]
  exact publication_spec expected _ _ agrees (fun _ h => h.2)
    (fun _ _ h growth bound => ⟨h.1.trans growth, bound⟩)

theorem Extends.antisymm {left right : Journal} (forward : Extends left right)
    (backward : Extends right left) : left = right := by
  funext key
  cases a : left key with
  | some value => exact (forward key value a).symm
  | none =>
    cases b : right key with
    | none => rfl
    | some value => have := backward key value b; simp [a] at this

/-- Republishing records already present cannot change the durable journal,
even if the duplicate attempt crashes. Only fault-harness bookkeeping changes. -/
theorem put_duplicate (key : String) (result : Result) (start : State Journal)
    (recorded : Published (records key result) start.durable)
    (reflexive : ∀ entry ∈ records key result, (entry.2 == entry.2) = true) :
    ((attempt key result).run start).2.durable = start.durable := by
  have safe := put_spec start.durable start.durable key result
    (fun entry member => ⟨recorded entry member, reflexive entry member⟩) start ⟨.refl _, .refl _⟩
  generalize (attempt key result).run start = run at *
  obtain ⟨returned, final⟩ := run
  cases returned with
  | ok _ => exact safe.2.2.1.2.antisymm safe.2.2.1.1
  | error _ => exact safe.2.1.2.antisymm safe.2.1.1

/-- A late or duplicate publication cannot undo a cached completed result. -/
theorem completed_stable (expected : Journal) (key : String) (result : Result)
    (agrees : Agrees (records key result) expected) (start : State Journal)
    (bounded : Extends start.durable expected) (completedKey : String) (outcome : Exit)
    (cached : start.durable (resultKey completedKey) = some (toJson outcome)) :
    let final := ((attempt key result).run start).2
    JournalDb.get raw completedKey final.durable =
      (some (toJson (Result.completed outcome)), final.durable) := by
  have safe := put_spec expected start.durable key result agrees start ⟨.refl _, bounded⟩
  apply get_completed
  generalize (attempt key result).run start = run at *
  obtain ⟨returned, final⟩ := run
  cases returned with
  | ok _ => exact safe.2.2.1.1 _ _ cached
  | error _ => exact safe.2.1.1 _ _ cached

/-- A successful publication has a durable fork descriptor and every child slot
specified by that publication. Missing slots make no claim and erase nothing. -/
theorem published_fork {journal : Journal} {key : String} {children : Array (Option Exit)}
    (recorded : Published (records key (.suspended children)) journal) :
    journal (forkKey key) = some (toJson children.size) ∧
      ∀ i, i < children.size → ∀ outcome, children[i]! = some outcome →
        journal (childKey key i) = some (toJson outcome) := by
  constructor
  · exact recorded (forkKey key, toJson children.size) (by simp [records])
  · intro i inside outcome slot
    apply recorded (childKey key i, toJson outcome)
    simp only [records, List.mem_cons]
    right
    apply List.mem_filterMap.mpr
    exact ⟨i, List.mem_range.mpr inside, by simp [childRecord, slot]⟩

/-- Completing publication of all child outcomes yields a readable group result.
The result cache may be absent: reading the slots alone suffices. -/
theorem published_group_read (expected : Journal) (key : String) (outcomes : Array Exit)
    (journal : Journal) (bounded : Extends journal expected)
    (uncached : expected (resultKey key) = none)
    (recorded : Published (records key (.suspended (outcomes.map some))) journal) :
    JournalDb.get raw key journal =
      (some (toJson (Result.settle (outcomes.map some))), journal) := by
  have missing : journal (resultKey key) = none := by
    cases stored : journal (resultKey key) with
    | none => rfl
    | some value => have := bounded _ _ stored; simp [uncached] at this
  have stored := published_fork recorded
  apply get_fork journal key (outcomes.map some) missing stored.1
  intro i inside
  have bound : i < outcomes.size := by simpa using inside
  have slot : (outcomes.map some)[i]! = some outcomes[i] := by simp [getElem!_pos, bound]
  simpa [slot] using stored.2 i inside outcomes[i] slot

end LeanCloud.Proofs.JournalAdapter
