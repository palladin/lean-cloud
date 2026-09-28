import LeanCloud.Proofs.EvaluationContinuation
import LeanCloud.Proofs.BranchFreshness
import LeanCloud.Proofs.ParallelSlots

/-! A relational invariant for partially executed workflows. It relates the
original program to its journal, branch outcomes, and pending locations. It is not an executable interpreter or a queue policy. -/

namespace LeanCloud.Proofs
open Lean LeanEff

def commandLocation (parent : Location) (branch command : Nat) : Location :=
  parent.push (branch, command)

theorem Journal.FreshBetween.command_missing {journal : Journal} {parent : Location} {branch command : Nat}
    (fresh : journal.FreshBetween (commandLocation parent branch command) (parent.child (branch + 1))) :
    journal (commandLocation parent branch command).key = none :=
  fresh.missing (by simp [commandLocation])
    (Location.child_earlier_sibling parent branch command (branch + 1) (by omega))

/-- Partial outcomes occupy their original array positions. -/
def outcomeSlots (codec : Codec α) (outcomes : Array (Option (Except CloudError α))) :
    Array (Option Exit) := outcomes.map (Option.map (encodeOutcome codec))

/-- A group publishes its join only after every child has completed. -/
def groupPending (location : Location) (outcomes : Array (Option α))
    (children : List Location) : List Location :=
  match outcomes.mapM id with
  | none => children
  | some _ => [location]

mutual
  /-- A branch's replay snapshot. Completed prefixes retain their records;
  active parallel groups retain a snapshot for every child. Completed groups
  retain their evaluation and result while their continuation advances. -/
  inductive ReplaySnapshot (journal : Journal) :
      Cloud Id Json → Location → Nat → Nat →
        Option (Except CloudError Json) → List Location → Prop where
    | pending (program : Cloud Id Json)
        (parent : Location) (branch command : Nat)
        (fresh : journal.FreshBetween (commandLocation parent branch command) (parent.child (branch + 1))) :
        ReplaySnapshot journal program parent branch command none
          [commandLocation parent branch command]
    | returned {parent branch command} (value : Json)
        (recorded : journal (commandLocation parent branch command).key =
          some (toJson (Result.completed (.success value)))) :
        ReplaySnapshot journal (EffF.pure value) parent branch command (some (.ok value)) []
    | failed {parent branch command}
        (error : CloudError) (continuation : ArrsF (Control Id) β Json)
        (recorded : journal (commandLocation parent branch command).key =
          some (toJson (Result.completed (.failure error)))) :
        ReplaySnapshot journal (.impure (.fail error) continuation) parent branch command
          (some (.error error)) []
    | delay {parent branch command outcome pending}
        {continuation : ArrsF (Control Id) Unit Json}
        (rest : ReplaySnapshot journal (ArrsF.apply continuation ())
          parent branch command outcome pending) :
        ReplaySnapshot journal (.impure .delay continuation) parent branch command outcome pending
    | parallel {childCodec : Codec β} {count : Nat}
        {branches : Fin count → Cloud Id β}
        {continuation : ArrsF (Control Id) (Array β) Json}
        {parent branch command outcomes childrenPending}
        (children : ChildSnapshots journal childCodec branches
          (commandLocation parent branch command) 0 outcomes childrenPending)
        (recorded : journal (commandLocation parent branch command).key =
          some (toJson (Result.settle (outcomeSlots childCodec outcomes))))
        (fresh : journal.FreshBetween (commandLocation parent branch (command + 1))
          (parent.child (branch + 1))) :
        ReplaySnapshot journal (.impure (.parallel childCodec count branches) continuation)
          parent branch command none
          (groupPending (commandLocation parent branch command) outcomes childrenPending)
    | parallelSuccess {childCodec : Codec β} {count : Nat}
        {branches : Fin count → Cloud Id β}
        {continuation : ArrsF (Control Id) (Array β) Json}
        {parent branch command outcomes values outcome pending}
        (children : ChildrenEvaluation branches outcomes)
        (collected : outcomes.mapM id = .ok values)
        (recorded : journal (commandLocation parent branch command).key =
          some (toJson (Result.completed (.success (Json.arr (values.map childCodec.encode))))))
        (rest : ReplaySnapshot journal (ArrsF.apply continuation values)
          parent branch (command + 1) outcome pending) :
        ReplaySnapshot journal (.impure (.parallel childCodec count branches) continuation)
          parent branch command outcome pending
    | parallelFailure {childCodec : Codec β} {count : Nat}
        {branches : Fin count → Cloud Id β}
        (continuation : ArrsF (Control Id) (Array β) Json)
        {parent branch command outcomes error}
        (children : ChildrenEvaluation branches outcomes)
        (collected : outcomes.mapM id = .error error)
        (recorded : journal (commandLocation parent branch command).key =
          some (toJson (Result.completed (.failure error)))) :
        ReplaySnapshot journal (.impure (.parallel childCodec count branches) continuation)
          parent branch command (some (.error error)) []

  /-- Child snapshots share the journal and may advance in any order.
  Their pending lists are in structural order; a queue can select any member. -/
  inductive ChildSnapshots (journal : Journal) :
      {α : Type} → Codec α → {count : Nat} → (Fin count → Cloud Id α) →
        Location → Nat → Array (Option (Except CloudError α)) → List Location → Prop where
    | empty (codec : Codec α) (branches : Fin 0 → Cloud Id α) (parent : Location) (offset : Nat) :
        ChildSnapshots journal codec branches parent offset #[] []
    | cons {codec : Codec α} {count : Nat} {branches : Fin (count + 1) → Cloud Id α}
        {parent offset outcome outcomes headPending tailPending}
        (head : ReplaySnapshot journal (codec.encode <$> branches 0) parent offset 0
          (outcome.map (Except.map codec.encode)) headPending)
        (tail : ChildSnapshots journal codec (fun index => branches index.succ)
          parent (offset + 1) outcomes tailPending) :
        ChildSnapshots journal codec branches parent offset (#[outcome] ++ outcomes)
          (headPending ++ tailPending)
end

/-- The invariant holds before any work has executed. -/
theorem ReplaySnapshot.initial (program : Cloud Id Json) :
    ReplaySnapshot Journal.empty program #[] 0 0 none [Location.root] :=
  .pending program #[] 0 0 (.empty _ _)

theorem ChildSnapshots.size {journal : Journal} {codec : Codec α} {count : Nat}
    {branches : Fin count → Cloud Id α} {parent offset outcomes pending}
    (snapshot : ChildSnapshots journal codec branches parent offset outcomes pending) :
    outcomes.size = count := by
  match snapshot with
  | .empty .. => rfl
  | .cons _ tail => simp [tail.size, Nat.add_comm]
termination_by structural snapshot

theorem collect_optional_cons (head : Option α) (tail : Array (Option α)) :
    (#[head] ++ tail).mapM id =
      match head, tail.mapM id with
      | some value, some values => some (#[value] ++ values)
      | _, _ => none := by
  rw [Array.mapM_append]
  have singleton : (#[head].mapM id : Option (Array α)) = head.map (fun value => #[value]) := by
    cases head <;> simp [Array.mapM_eq_mapM_toList]
  rw [singleton]
  cases head <;> cases tail.mapM id <;> rfl

private theorem list_collect_optional_some {items : List (Option α)} {values : List α}
    (collected : items.mapM id = some values) : items = values.map some := by
  induction items generalizing values with
  | nil => simp at collected; subst values; rfl
  | cons head tail ih =>
    cases head with
    | none => simp [List.mapM_cons] at collected
    | some value =>
      cases result : tail.mapM id with
      | none => simp [List.mapM_cons, result] at collected
      | some rest =>
        simp [List.mapM_cons, result] at collected
        subst values
        simp [ih result]

/-- A fully collected group contains exactly the reported outcomes, with no
unfilled slots. This does not impose an order on when those slots were filled. -/
theorem collect_optional_some {items : Array (Option α)} {values : Array α}
    (collected : items.mapM id = some values) : items = values.map some := by
  cases result : items.toList.mapM id with
  | none => simp [Array.mapM_eq_mapM_toList, result] at collected
  | some rest =>
    simp [Array.mapM_eq_mapM_toList, result] at collected
    subst values
    apply Array.toList_inj.mp
    simpa using list_collect_optional_some result

theorem outcomeSlots_full (codec : Codec α) (statuses : Array (Option (Except CloudError α)))
    (outcomes : Array (Except CloudError α)) (collected : statuses.mapM id = some outcomes) :
    Result.settle (outcomeSlots codec statuses) =
      .completed (match outcomes.mapM id with
        | .ok values => .success (Json.arr (values.map codec.encode))
        | .error error => .failure error) := by
  rw [collect_optional_some collected]
  have slots : outcomeSlots codec (outcomes.map some) = (outcomes.map (encodeOutcome codec)).map some := by
    simp only [outcomeSlots, Array.map_map, Function.comp_def, Option.map_some]
  rw [slots]
  exact settle_encoded codec outcomes

private theorem list_collect_missing (values : List (Option α))
    (missing : values.mapM id = none) : none ∈ values := by
  induction values with
  | nil => simp at missing
  | cons head tail ih =>
    cases head with
    | none => simp
    | some value =>
      cases collected : tail.mapM id with
      | none => exact List.mem_cons_of_mem _ (ih collected)
      | some _ => simp [List.mapM_cons, collected] at missing

/-- The snapshot and runtime agree that a partial group must remain suspended. -/
theorem outcomeSlots_waits (codec : Codec α) (outcomes : Array (Option (Except CloudError α)))
    (missing : outcomes.mapM id = none) :
    Result.settle (outcomeSlots codec outcomes) = .suspended (outcomeSlots codec outcomes) := by
  have uncollected : outcomes.toList.mapM id = none := by
    cases collected : outcomes.toList.mapM id with
    | none => rfl
    | some _ => simp [Array.mapM_eq_mapM_toList, collected] at missing
  apply Result.settle_missing
  have member : none ∈ outcomes := by simpa using list_collect_missing outcomes.toList uncollected
  exact Array.mem_map.mpr ⟨none, member, rfl⟩

private theorem pending_append_empty (left right : List Location) :
    (left ++ right).isEmpty = (left.isEmpty && right.isEmpty) := by
  cases left <;> rfl

mutual
  /-- A snapshot has no pending work exactly when its branch has reported an
  outcome. In particular, a ready join is still pending work. -/
  theorem ReplaySnapshot.pending_empty {journal : Journal}
      {program : Cloud Id Json} {parent branch command status pending}
      (snapshot : ReplaySnapshot journal program parent branch command status pending) :
      pending.isEmpty = status.isSome := by
    match snapshot with
    | .pending .. | .returned .. | .failed .. | .parallelFailure .. => rfl
    | .delay rest | .parallelSuccess _ _ _ rest => exact rest.pending_empty
    | .parallel (outcomes := outcomes) children _ _ =>
      unfold groupPending
      cases collected : outcomes.mapM id with
      | none => simpa only [collected, Option.isSome_none] using children.pending_empty
      | some _ => rfl
  termination_by structural snapshot

  theorem ChildSnapshots.pending_empty {journal : Journal} {codec : Codec α} {count : Nat}
      {branches : Fin count → Cloud Id α} {parent offset outcomes pending}
      (snapshot : ChildSnapshots journal codec branches parent offset outcomes pending) :
      pending.isEmpty = (outcomes.mapM id).isSome := by
    match snapshot with
    | .empty .. => simp [Array.mapM_eq_mapM_toList]
    | .cons (outcome := headOutcome) (outcomes := tailOutcomes) head tail =>
      rw [pending_append_empty, head.pending_empty, tail.pending_empty, collect_optional_cons]
      simp only [Option.isSome_map]
      cases headOutcome <;> cases tailOutcomes.mapM id <;> rfl
  termination_by structural snapshot
end

theorem ReplaySnapshot.pending_exists {journal : Journal}
    {program : Cloud Id Json} {parent branch command status pending}
    (snapshot : ReplaySnapshot journal program parent branch command status pending)
    (unfinished : status = none) : ∃ location, location ∈ pending := by
  have nonempty := snapshot.pending_empty
  rw [unfinished] at nonempty
  cases pending with
  | nil => cases nonempty
  | cons location rest => exact ⟨location, by simp⟩

end LeanCloud.Proofs
