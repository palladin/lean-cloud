import LeanCloud.Proofs.JournalAdapter

/-! Immutable journal extension, compatible records, and reconstruction laws.
These properties are independent of the worker execution model. -/

namespace LeanCloud.Proofs.JournalAdapter
open Lean JournalDb

/-- Every previously recorded value is retained, including records outside the
current publication. -/
def Extends (before after : Journal) : Prop :=
  ∀ key value, before key = some value → after key = some value

theorem Extends.refl (journal : Journal) : Extends journal journal := fun _ _ h => h

theorem Extends.trans {a b c : Journal} (ab : Extends a b) (bc : Extends b c) : Extends a c :=
  fun k v h => bc k v (ab k v h)

theorem Extends.antisymm {left right : Journal} (forward : Extends left right)
    (backward : Extends right left) : left = right := by
  funext key
  cases a : left key with
  | some value => exact (forward key value a).symm
  | none =>
    cases b : right key with
    | none => rfl
    | some value => have := backward key value b; simp [a] at this

/-- A finite set of immutable fields cannot keep changing forever. A field
may remain absent forever; stabilization does not assume that all work finishes. -/
theorem finite_journal_stable (journals : Nat → Journal) (keys : List String)
    (grows : ∀ start stop, start ≤ stop → Extends (journals start) (journals stop))
    (supported : ∀ n key value, journals n key = some value → key ∈ keys) :
    ∃ cut, ∀ n, cut ≤ n → journals n = journals cut := by
  classical
  have absent (key : String) (missing : ¬ ∃ n value, journals n key = some value) (n : Nat) :
      journals n key = none := by
    cases recorded : journals n key with
    | none => rfl
    | some value => exact False.elim (missing ⟨n, value, recorded⟩)
  have fields (fields : List String) :
      ∃ cut, ∀ n, cut ≤ n → ∀ key ∈ fields, journals n key = journals cut key := by
    induction fields with
    | nil => exact ⟨0, by simp⟩
    | cons key rest ih =>
      obtain ⟨tailCut, tailFixed⟩ := ih
      by_cases present : ∃ n value, journals n key = some value
      · obtain ⟨headCut, value, recorded⟩ := present
        refine ⟨max headCut tailCut, ?_⟩
        intro n later field member
        rcases List.mem_cons.mp member with rfl | member
        · exact (grows headCut n (by omega) field value recorded).trans
            (grows headCut (max headCut tailCut) (by omega) field value recorded).symm
        · exact (tailFixed n (by omega) field member).trans
            (tailFixed (max headCut tailCut) (by omega) field member).symm
      · refine ⟨tailCut, ?_⟩
        intro n later field member
        rcases List.mem_cons.mp member with rfl | member
        · rw [absent field present n, absent field present tailCut]
        · exact tailFixed n later field member
  obtain ⟨cut, stable⟩ := fields keys
  refine ⟨cut, ?_⟩
  intro n later
  funext key
  by_cases member : key ∈ keys
  · exact stable n later key member
  · have missing : ¬ ∃ n value, journals n key = some value := by
      rintro ⟨n, value, recorded⟩
      exact member (supported n key value recorded)
    rw [absent key missing n, absent key missing cut]

def Published (entries : List Record) (journal : Journal) : Prop :=
  ∀ entry ∈ entries, journal entry.1 = some entry.2

/-- The intended records agree with a fixed journal. JSON comparison is partial
in Lean, so reflexivity on these encoded values is an explicit hypothesis. -/
def Agrees (entries : List Record) (expected : Journal) : Prop :=
  ∀ entry ∈ entries, expected entry.1 = some entry.2 ∧ (entry.2 == entry.2) = true

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

/-- Publishing an initially missing fork adds a record even for an empty
parallel group, whose initializer stores its completed result immediately. -/
theorem initialized_changes {initial journal : Journal} {current : Location} {count : Nat}
    (absent : initial (resultKey current.key) = none ∧ initial (forkKey current.key) = none)
    (published : Published (records current.key (Result.settle (Array.replicate count none))) journal) :
    journal ≠ initial := by
  intro same
  subst journal
  by_cases empty : count = 0
  · subst count
    have cached := published (resultKey current.key, toJson (Exit.success (.arr #[])))
      (by simp [Result.settle, records, pure, Except.pure, Functor.map, Except.map])
    simp [absent.1] at cached
  · have missing : none ∈ (Array.replicate count none : Array (Option Exit)) := by simp [empty]
    rw [Result.settle_missing _ missing] at published
    have descriptor := (published_fork published).1
    simp [absent.2] at descriptor

end LeanCloud.Proofs.JournalAdapter
