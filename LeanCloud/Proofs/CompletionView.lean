import LeanCloud.Proofs.JournalRecovery
import LeanCloud.Proofs.CompletionCode

/-! Physical records that justify retrying a completion. These are predicates
on the actual immutable layout, not assumptions about interpreter execution. -/

namespace LeanCloud.Proofs.ReplayRecovery
open Lean JournalDb JournalAdapter

def Between (initial expected journal : Journal) : Prop :=
  Extends initial journal ∧ Extends journal expected

theorem Between.grow {initial expected before after : Journal}
    (valid : Between initial expected before) (growth : Extends before after)
    (bound : Extends after expected) : Between initial expected after :=
  ⟨valid.1.trans growth, bound⟩

theorem Between.fixed {initial expected journal : Journal} (valid : Between initial expected journal)
    (key : String) (same : expected key = initial key) : journal key = initial key := by
  cases old : initial key with
  | some value => exact valid.1 _ _ old
  | none =>
    cases stored : journal key with
    | none => rfl
    | some value => have := valid.2 _ _ stored; simp [same, old] at this

theorem Extends.missing {journal expected : Journal} (bounded : Extends journal expected)
    (key : String) (missing : expected key = none) : journal key = none := by
  cases stored : journal key with
  | none => rfl
  | some value => have := bounded _ _ stored; simp [missing] at this

theorem get_missing (journal : Journal) (key : String)
    (cache : journal (resultKey key) = none) (fork : journal (forkKey key) = none) :
    JournalDb.get raw key journal = (none, journal) := by
  simp [JournalDb.get, raw, bind, pure, StateT.bind, StateT.pure, cache, fork]

/-- Durable evidence for a logical completion, with or without a result cache. -/
inductive CompletedAt (journal : Journal) (key : String) (outcome : Exit) : Prop where
  | cached (recorded : journal (resultKey key) = some (toJson outcome))
  | group (slots : Array (Option Exit))
      (fork : journal (forkKey key) = some (toJson slots.size))
      (filled : ∀ i, i < slots.size → ∃ value,
        slots[i]! = some value ∧ journal (childKey key i) = some (toJson value))
      (settled : Result.settle slots = .completed outcome)

theorem CompletedAt.grow {before after : Journal} {key : String} {outcome : Exit}
    (recorded : CompletedAt before key outcome) (growth : Extends before after) :
    CompletedAt after key outcome := by
  cases recorded with
  | cached stored => exact .cached (growth _ _ stored)
  | group slots fork filled settled =>
    refine .group slots (growth _ _ fork) ?_ settled
    intro i inside
    obtain ⟨value, same, stored⟩ := filled i inside
    exact ⟨value, same, growth _ _ stored⟩

/-- Without a result cache, completion requires every slot of the recorded
descriptor. This excludes a stranded join while a child is still missing. -/
theorem CompletedAt.no_missing {journal : Journal} {key : String} {outcome : Exit} {count : Nat}
    (completed : CompletedAt journal key outcome) (uncached : journal (resultKey key) = none)
    (descriptor : journal (forkKey key) = some (toJson count))
    (index : Fin count) : journal (childKey key index.val) ≠ none := by
  cases completed with
  | cached recorded => simp [uncached] at recorded
  | group slots fork filled settled =>
    have same : slots.size = count := toJson_injective (α := Nat) (fun _ => rfl)
      (Option.some.inj (fork.symm.trans descriptor))
    obtain ⟨value, _, recorded⟩ := filled index.val (by rw [same]; exact index.isLt)
    simp [recorded]

theorem CompletedAt.not_suspended {journal : Journal} {key : String} {outcome : Exit} {seen : Array (Option Exit)}
    (completed : CompletedAt journal key outcome) (uncached : journal (resultKey key) = none)
    (view : JournalDb.get raw key journal = (some (toJson (Result.suspended seen)), journal)) : False := by
  cases completed with
  | cached recorded => simp [uncached] at recorded
  | group slots fork filled settled =>
    have actual := get_fork journal key slots uncached fork (by
      intro index inside
      obtain ⟨value, same, recorded⟩ := filled index inside
      simpa only [same, Option.map_some] using recorded)
    rw [settled] at actual
    have same : Result.completed outcome = .suspended seen := toJson_injective result_roundtrip
      (Option.some.inj (congrArg Prod.fst (actual.symm.trans view)))
    cases same

/-- A durable completion remains readable when any optional cache is bounded
by the same prescribed result. Full child slots suffice without a cache. -/
theorem CompletedAt.view {journal expected : Journal} {key : String} {outcome : Exit}
    (completed : CompletedAt journal key outcome) (bounded : Extends journal expected)
    (intended : expected (resultKey key) = some (toJson outcome)) :
    JournalDb.get raw key journal = (some (toJson (Result.completed outcome)), journal) := by
  cases cached : journal (resultKey key) with
  | some value =>
    have same := (bounded _ _ cached).symm.trans intended
    cases same
    exact get_completed _ _ _ cached
  | none =>
    cases completed with
    | cached recorded => simp [cached] at recorded
    | group slots fork filled settled =>
      rw [get_fork journal key slots cached fork (by
        intro i inside
        obtain ⟨value, slot, stored⟩ := filled i inside
        simpa only [slot, Option.map_some] using stored), settled]

/-- A terminal command has no fork descriptor, or its completion is already
durable. A full group may be durable solely through its slots, without a cache. -/
inductive CompletionSource (initial expected : Journal) (key : String) (outcome : Exit) : Prop where
  | terminal (noFork : expected (forkKey key) = none)
  | completed (recorded : CompletedAt initial key outcome)

theorem CompletedAt.source {initial expected : Journal} {key : String} {outcome : Exit}
    (completed : CompletedAt initial key outcome) : CompletionSource initial expected key outcome :=
  .completed completed

theorem CompletionSource.grow {initial after expected : Journal} {key : String} {outcome : Exit}
    (source : CompletionSource initial expected key outcome) (growth : Extends initial after) :
    CompletionSource after expected key outcome := by
  cases source with
  | terminal absent => exact .terminal absent
  | completed recorded => exact .completed (recorded.grow growth)

theorem CompletionSource.view {initial expected : Journal} {key : String} {outcome : Exit}
    (source : CompletionSource initial expected key outcome)
    (intended : expected (resultKey key) = some (toJson outcome))
    (journal : Journal) (valid : Between initial expected journal) :
    ∃ record : Option Result, JournalDb.get raw key journal = (record.map toJson, journal) ∧
      (record = none ∨ record = some (.completed outcome) ∧ CompletedAt journal key outcome) := by
  cases source with
  | terminal noFork =>
    cases cached : journal (resultKey key) with
    | some value =>
      have same := (valid.2 _ _ cached).symm.trans intended
      cases same
      exact ⟨some (.completed outcome), get_completed _ _ _ cached, Or.inr ⟨rfl, .cached cached⟩⟩
    | none =>
      exact ⟨none, get_missing _ _ cached (Extends.missing valid.2 _ noFork), Or.inl rfl⟩
  | completed recorded =>
    have present := recorded.grow valid.1
    exact ⟨some (.completed outcome), present.view valid.2 intended, Or.inr ⟨rfl, present⟩⟩

/-- The local completion's fixed records. The parent descriptor and other slots
are already durable; only this child slot and a possible result cache can be
added. Values at unrelated locations are unrestricted. -/
structure ChildLayout (initial expected : Journal) (current parent : Location)
    (index : Nat) (outcome : Exit) (children : Array (Option Exit)) : Prop where
  own : expected (resultKey current.key) = some (toJson outcome)
  source : CompletionSource initial expected current.key outcome
  inside : index < children.size
  missing : children[index]! = none
  fork : initial (forkKey parent.key) = some (toJson children.size)
  descriptor : expected (forkKey parent.key) = some (toJson children.size)
  child : expected (childKey parent.key index) = some (toJson outcome)
  others : ∀ i, i < children.size → i ≠ index →
    initial (childKey parent.key i) = children[i]!.map toJson ∧
      expected (childKey parent.key i) = children[i]!.map toJson
  cache : expected (resultKey parent.key) =
    match Result.settle (children.set! index (some outcome)) with
    | .suspended _ => none
    | .completed result => some (toJson result)

/-- An intermediate completion state can serve as a new lower bound. Sibling
slots are fixed by the original interval; the selected slot may already exist. -/
theorem ChildLayout.rebase {initial expected journal : Journal} {current parent : Location}
    {index : Nat} {outcome : Exit} {children : Array (Option Exit)}
    (layout : ChildLayout initial expected current parent index outcome children)
    (valid : Between initial expected journal) :
    ChildLayout journal expected current parent index outcome children := by
  refine ⟨layout.own, layout.source.grow valid.1, layout.inside, layout.missing,
    valid.1 _ _ layout.fork, layout.descriptor, layout.child, ?_, layout.cache⟩
  intro i inside different
  have fixed := layout.others i inside different
  exact ⟨(valid.fixed _ (fixed.2.trans fixed.1.symm)).trans fixed.1, fixed.2⟩

abbrev completionResponse := ReplayInterpreter.Internal.joinResponse

/-- The parent's logical view is either the original partial group or exactly
the settled group after publishing this child. A cache can only contain that
same settled result. -/
theorem ChildLayout.parent_view {initial expected : Journal} {current parent : Location}
    {index : Nat} {outcome : Exit} {children : Array (Option Exit)}
    (layout : ChildLayout initial expected current parent index outcome children)
    (journal : Journal) (valid : Between initial expected journal) :
    ∃ group, JournalDb.get raw parent.key journal = (some (toJson group), journal) ∧
      (group = .suspended children ∧ journal (childKey parent.key index) = none ∨
        group = Result.settle (children.set! index (some outcome))) := by
  let updated := children.set! index (some outcome)
  have rest (i : Nat) (inside : i < children.size) (different : i ≠ index) :
      journal (childKey parent.key i) = children[i]!.map toJson := by
    have fixed := layout.others i inside different
    exact (valid.fixed _ (fixed.2.trans fixed.1.symm)).trans fixed.1
  cases cached : journal (resultKey parent.key) with
  | some value =>
    have bound := valid.2 _ _ cached
    rw [layout.cache] at bound
    change (match Result.settle updated with
      | .suspended _ => none | .completed result => some (toJson result)) = some value at bound
    cases settled : Result.settle updated with
    | suspended slots => simp only [settled] at bound; cases bound
    | completed result =>
      rw [settled] at bound
      cases bound
      exact ⟨.completed result, get_completed _ _ _ cached, Or.inr rfl⟩
  | none =>
    cases slot : journal (childKey parent.key index) with
    | none =>
      refine ⟨.suspended children, ?_, Or.inl ⟨rfl, rfl⟩⟩
      have missing : none ∈ children := by
        have stored := layout.missing
        rw [getElem!_pos children index layout.inside] at stored
        exact stored ▸ Array.getElem_mem layout.inside
      rw [get_fork journal parent.key children cached (valid.1 _ _ layout.fork),
        Result.settle_missing children missing]
      intro i inside
      by_cases same : i = index
      · subst i; simp [slot, layout.missing]
      · exact rest i inside same
    | some value =>
      have same := (valid.2 _ _ slot).symm.trans layout.child
      cases same
      refine ⟨Result.settle updated, ?_, Or.inr rfl⟩
      apply get_fork journal parent.key updated cached
      · simpa [updated] using valid.1 _ _ layout.fork
      · intro i inside
        have bound : i < children.size := by simpa [updated] using inside
        by_cases same : i = index
        · subst i
          simpa [updated, Array.getElem!_set!_self, layout.inside] using slot
        · rw [show updated[i]! = children[i]! by
            simp [updated, getElem!_pos, bound, Ne.symm same]]
          exact rest i bound same

theorem ChildLayout.parent_updated {initial expected : Journal} {current parent : Location}
    {index : Nat} {outcome : Exit} {children : Array (Option Exit)}
    (layout : ChildLayout initial expected current parent index outcome children)
    (journal : Journal) (valid : Between initial expected journal)
    (recorded : journal (childKey parent.key index) = some (toJson outcome)) :
    JournalDb.get raw parent.key journal =
      (some (toJson (Result.settle (children.set! index (some outcome)))), journal) := by
  obtain ⟨group, view, absent | complete⟩ := layout.parent_view journal valid
  · rw [recorded] at absent; cases absent.2
  · rw [complete] at view; exact view

/-- Equality is needed only for the records admitted by the storage invariant. -/
def Comparable (expected : Journal) : Prop :=
  ∀ key value, expected key = some value → (value == value) = true

theorem agrees_of_published {entries : List Record} {expected : Journal}
    (recorded : Published entries expected) (comparable : Comparable expected) : Agrees entries expected :=
  fun entry member => ⟨recorded entry member, comparable _ _ (recorded entry member)⟩

theorem published_suspended (key : String) (children : Array (Option Exit)) (journal : Journal)
    (fork : journal (forkKey key) = some (toJson children.size))
    (slots : ∀ i, i < children.size → ∀ outcome, children[i]! = some outcome →
      journal (childKey key i) = some (toJson outcome)) :
    Published (records key (.suspended children)) journal := by
  intro entry member
  rcases List.mem_cons.mp member with same | child
  · subst entry; exact fork
  · obtain ⟨i, member, selected⟩ := List.mem_filterMap.mp child
    have inside := List.mem_range.mp member
    unfold childRecord at selected
    cases stored : children[i]! with
    | none => simp [stored] at selected
    | some outcome =>
      simp only [stored, Option.map_some, Option.some.injEq] at selected
      subst entry
      exact slots i inside outcome stored

theorem ChildLayout.slots_agree {initial expected : Journal} {current parent : Location}
    {index : Nat} {outcome : Exit} {children : Array (Option Exit)}
    (layout : ChildLayout initial expected current parent index outcome children)
    (comparable : Comparable expected) :
    Agrees (records parent.key (.suspended (children.set! index (some outcome)))) expected := by
  apply agrees_of_published _ comparable
  apply published_suspended
  · simpa using layout.descriptor
  · intro i inside value slot
    have bound : i < children.size := by simpa using inside
    by_cases same : i = index
    · subst i
      rw [Array.getElem!_set!_self _ _ _ layout.inside] at slot
      cases slot
      exact layout.child
    · have kept : (children.set! index (some outcome))[i]! = children[i]! := by
        simp [getElem!_pos, bound, Ne.symm same]
      rw [kept] at slot
      simpa [slot] using (layout.others i bound same).2

theorem ChildLayout.cache_agrees {initial expected : Journal} {current parent : Location}
    {index : Nat} {outcome : Exit} {children : Array (Option Exit)}
    (layout : ChildLayout initial expected current parent index outcome children)
    (comparable : Comparable expected) (result : Exit)
    (complete : Result.settle (children.set! index (some outcome)) = .completed result) :
    Agrees (records parent.key (.completed result)) expected := by
  apply agrees_of_published _ comparable
  intro entry member
  simp only [records, List.mem_singleton] at member
  subst entry
  simpa only [complete] using layout.cache

end LeanCloud.Proofs.ReplayRecovery
