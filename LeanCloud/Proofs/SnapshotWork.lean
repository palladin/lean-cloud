import LeanCloud.Proofs.ReplaySnapshot
import LeanCloud.Proofs.EvaluationContinuation

/-! Work already processed in a replay snapshot. A fork and its eventual join
count separately; a pending command has not yet consumed a worker step. -/

namespace LeanCloud.Proofs
open Lean LeanEff

mutual
  inductive SnapshotWork {journal : Journal} :
      {program : Cloud Id Json} → {parent : Location} → {branch command : Nat} →
      {status : Option (Except CloudError Json)} → {pending : List Location} →
      ReplaySnapshot journal program parent branch command status pending → Nat → Prop where
    | pending (program : Cloud Id Json) (parent : Location) (branch command : Nat) (fresh) :
        SnapshotWork (.pending program parent branch command fresh) 0
    | returned {parent branch command} (value : Json) (recorded) :
        SnapshotWork (.returned (parent := parent) (branch := branch) (command := command) value recorded) 1
    | failed {parent branch command} (error : CloudError) (continuation : ArrsF (Control Id) β Json) (recorded) :
        SnapshotWork (.failed (parent := parent) (branch := branch) (command := command) error continuation recorded) 1
    | delay {parent branch command status pending work}
        {continuation : ArrsF (Control Id) Unit Json}
        {rest : ReplaySnapshot journal (ArrsF.apply continuation ()) parent branch command status pending}
        (cost : SnapshotWork rest work) : SnapshotWork (.delay rest) work
    | parallel {codec : Codec β} {count : Nat} {branches : Fin count → Cloud Id β}
        {continuation : ArrsF (Control Id) (Array β) Json}
        {parent branch command outcomes pending work}
        {children : ChildSnapshots journal codec branches (commandLocation parent branch command) 0 outcomes pending}
        (cost : ChildrenSnapshotWork children work) (recorded fresh) :
        SnapshotWork (.parallel (continuation := continuation) children recorded fresh) (1 + work)
    | parallelSuccess {codec : Codec β} {count : Nat} {branches : Fin count → Cloud Id β}
        {continuation : ArrsF (Control Id) (Array β) Json}
        {parent branch command outcomes values status pending childrenWork restWork}
        {children : ChildrenEvaluation branches outcomes}
        (firstCost : ChildrenWork 0 children childrenWork) (collected recorded)
        {rest : ReplaySnapshot journal (ArrsF.apply continuation values) parent branch (command + 1) status pending}
        (restCost : SnapshotWork rest restWork) :
        SnapshotWork (.parallelSuccess (childCodec := codec) children collected recorded rest) (childrenWork + 2 + restWork)
    | parallelFailure {codec : Codec β} {count : Nat} {branches : Fin count → Cloud Id β}
        (continuation : ArrsF (Control Id) (Array β) Json)
        {parent branch command outcomes error childrenWork}
        {children : ChildrenEvaluation branches outcomes}
        (cost : ChildrenWork 0 children childrenWork) (collected : outcomes.mapM id = .error error) (recorded) :
        SnapshotWork (.parallelFailure (childCodec := codec) (parent := parent) (branch := branch)
          (command := command) continuation children collected recorded) (childrenWork + 2)

  inductive ChildrenSnapshotWork {journal : Journal} :
      {α : Type} → {codec : Codec α} → {count : Nat} → {branches : Fin count → Cloud Id α} →
      {parent : Location} → {offset : Nat} → {statuses : Array (Option (Except CloudError α))} →
      {pending : List Location} →
      ChildSnapshots journal codec branches parent offset statuses pending → Nat → Prop where
    | empty (codec : Codec α) (branches : Fin 0 → Cloud Id α) (parent : Location) (offset : Nat) :
        ChildrenSnapshotWork (.empty codec branches parent offset) 0
    | cons {codec : Codec α} {count : Nat} {branches : Fin (count + 1) → Cloud Id α}
        {parent offset outcomes headPending tailPending firstWork restWork}
        {outcome : Option (Except CloudError α)}
        {head : ReplaySnapshot journal (codec.encode <$> branches 0) parent offset 0
          (outcome.map (Except.map codec.encode)) headPending}
        {tail : ChildSnapshots journal codec (fun index => branches index.succ)
          parent (offset + 1) outcomes tailPending}
        (headCost : SnapshotWork head firstWork) (tailCost : ChildrenSnapshotWork tail restWork) :
        ChildrenSnapshotWork (.cons head tail) (firstWork + restWork)
end

theorem SnapshotWork.source {journal : Journal} {program : Cloud Id Json}
    {parent branch command status pending spent}
    {snapshot : ReplaySnapshot journal program parent branch command status pending}
    (_cost : SnapshotWork snapshot spent) : ReplaySnapshot journal program parent branch command status pending := snapshot

theorem ChildrenSnapshotWork.source {journal : Journal} {codec : Codec α} {count : Nat}
    {branches : Fin count → Cloud Id α} {parent offset statuses pending spent}
    {snapshot : ChildSnapshots journal codec branches parent offset statuses pending}
    (_cost : ChildrenSnapshotWork snapshot spent) : ChildSnapshots journal codec branches parent offset statuses pending := snapshot

mutual
  theorem ReplaySnapshot.work_exists {journal : Journal} {program : Cloud Id Json}
      {parent branch command status pending}
      (snapshot : ReplaySnapshot journal program parent branch command status pending) :
      ∃ work, SnapshotWork snapshot work := by
    match snapshot with
    | .pending program parent branch command fresh => exact ⟨0, .pending program parent branch command fresh⟩
    | .returned value recorded => exact ⟨1, .returned value recorded⟩
    | .failed error continuation recorded => exact ⟨1, .failed error continuation recorded⟩
    | .delay rest =>
      obtain ⟨work, cost⟩ := rest.work_exists
      exact ⟨work, .delay cost⟩
    | .parallel children recorded fresh =>
      obtain ⟨work, cost⟩ := children.work_exists
      exact ⟨1 + work, .parallel cost recorded fresh⟩
    | .parallelSuccess children collected recorded rest =>
      obtain ⟨first, headCost⟩ := children.work_exists
      obtain ⟨last, tailCost⟩ := rest.work_exists
      exact ⟨first + 2 + last, .parallelSuccess headCost collected recorded tailCost⟩
    | .parallelFailure continuation children collected recorded =>
      obtain ⟨work, cost⟩ := children.work_exists
      exact ⟨work + 2, .parallelFailure continuation cost collected recorded⟩
  termination_by structural snapshot

  theorem ChildSnapshots.work_exists {journal : Journal} {codec : Codec α} {count : Nat}
      {branches : Fin count → Cloud Id α} {parent offset statuses pending}
      (snapshot : ChildSnapshots journal codec branches parent offset statuses pending) :
      ∃ work, ChildrenSnapshotWork snapshot work := by
    match snapshot with
    | .empty codec branches parent offset => exact ⟨0, .empty codec branches parent offset⟩
    | .cons head tail =>
      obtain ⟨first, headCost⟩ := head.work_exists
      obtain ⟨rest, tailCost⟩ := tail.work_exists
      exact ⟨first + rest, .cons headCost tailCost⟩
  termination_by structural snapshot
end

theorem SnapshotWork.completed {journal : Journal} {program : Cloud Id Json}
    {parent branch command status outcome pending spent}
    {snapshot : ReplaySnapshot journal program parent branch command status pending}
    (cost : SnapshotWork snapshot spent) (completed : status = some outcome) :
    ∃ work, ∃ evaluation : Evaluation program outcome,
      ProgramWork 0 evaluation work ∧ spent = work + returnWork outcome := by
  match cost with
  | .pending .. => cases completed
  | .returned value recorded =>
    cases completed
    exact ⟨0, _, .pure value, rfl⟩
  | .failed error continuation recorded =>
    cases completed
    exact ⟨1, _, .failure continuation (.fail error), rfl⟩
  | .delay rest =>
    obtain ⟨work, _, cost, bound⟩ := rest.completed completed
    obtain ⟨_, restCost⟩ := ContinuationWork.of_apply _ _ cost
    exact ⟨0 + work, _, .success .delay restCost, by omega⟩
  | .parallel .. => cases completed
  | .parallelSuccess first collected recorded rest =>
    obtain ⟨work, _, cost, bound⟩ := rest.completed completed
    obtain ⟨_, controlCost⟩ := first.control _ collected
    obtain ⟨_, restCost⟩ := ContinuationWork.of_apply _ _ cost
    exact ⟨_, _, .success controlCost restCost, by omega⟩
  | .parallelFailure continuation first collected recorded =>
    cases completed
    obtain ⟨_, controlCost⟩ := first.control _ collected
    exact ⟨_, _, .failure continuation controlCost, by simp [returnWork]⟩
termination_by structural cost

/-- Completion supplies the original program's evaluation; the work theorem
also accounts for every processed command. -/
theorem ReplaySnapshot.evaluation {journal : Journal} {program : Cloud Id Json}
    {parent branch command status outcome pending}
    (snapshot : ReplaySnapshot journal program parent branch command status pending)
    (completed : status = some outcome) : Evaluation program outcome := by
  obtain ⟨_, cost⟩ := snapshot.work_exists
  obtain ⟨_, evaluation, _, _⟩ := cost.completed completed
  exact evaluation

theorem ChildrenSnapshotWork.completed {α : Type} {journal : Journal} {codec : Codec α} {count : Nat}
    {branches : Fin count → Cloud Id α} {parent offset statuses pending outcomes spent}
    {snapshot : ChildSnapshots journal codec branches parent offset statuses pending}
    (cost : ChildrenSnapshotWork snapshot spent) (law : CodecLaw codec)
    (completed : statuses.mapM id = some outcomes) :
    ∃ evaluation : ChildrenEvaluation branches outcomes, ChildrenWork 0 evaluation spent := by
  match cost with
  | .empty codec branches parent offset =>
    simp only [Array.mapM_empty, pure, Option.some.injEq] at completed
    subst outcomes
    exact ⟨_, .empty branches⟩
  | .cons (outcome := headOutcome) (outcomes := tailOutcomes) head tail =>
    rw [collect_optional_cons] at completed
    cases headEq : headOutcome with
    | none => simp only [headEq] at completed; cases completed
    | some value =>
      cases tailEq : tailOutcomes.mapM id with
      | none => simp only [headEq, tailEq] at completed; cases completed
      | some values =>
        simp only [headEq, tailEq, Option.some.injEq] at completed
        subst outcomes
        obtain ⟨work, _, headCost, bound⟩ := head.completed (by rw [headEq]; rfl)
        obtain ⟨_, original⟩ := headCost.of_encoded codec law _
        obtain ⟨_, remaining⟩ := tail.completed law tailEq
        have combined := ChildrenWork.cons original remaining
        simp only [returnWork_map] at bound
        exact ⟨_, by simpa only [bound] using combined⟩
termination_by structural cost

end LeanCloud.Proofs
