import LeanCloud.Proofs.EvaluationContinuation

/-! A finite description of the control path justified by a pure evaluation.
This is proof data, not an interpreter or a runtime scheduling policy. Children
retain their original array order; completed successful forks have a continuation. -/

universe u

namespace LeanCloud.Proofs
open Lean LeanEff

inductive ExecutionTree where
  | terminal (result : Except CloudError Json)
  | delay (rest : ExecutionTree)
  | fork (children : List ExecutionTree) (result : Except CloudError Json)
      (next : Option ExecutionTree)

def ExecutionTree.outcome : ExecutionTree → Except CloudError Json
  | .terminal result => result
  | .delay rest => rest.outcome
  | .fork _ result none => result
  | .fork _ _ (some next) => next.outcome

mutual
  inductive Expansion {m : Type → Type u} : Cloud m Json → ExecutionTree → Prop where
    | pure (value : Json) : Expansion (EffF.pure value) (.terminal (.ok value))
    | fail (error : CloudError) (continuation : ArrsF (Control m) α Json) :
        Expansion (.impure (.fail error) continuation) (.terminal (.error error))
    | delay {continuation : ArrsF (Control m) Unit Json} {tree}
        (rest : Expansion (ArrsF.apply continuation ()) tree) :
        Expansion (.impure .delay continuation) (.delay tree)
    | success {codec : Codec α} {count : Nat} {branches : Fin count → Cloud m α}
        {continuation : ArrsF (Control m) (Array α) Json} {outcomes values trees next}
        (evaluated : ChildrenEvaluation branches outcomes)
        (collected : outcomes.mapM id = .ok values)
        (children : ChildrenExpansion codec branches trees)
        (rest : Expansion (ArrsF.apply continuation values) next) :
        Expansion (.impure (.parallel codec count branches) continuation)
          (.fork trees (.ok (.arr (values.map codec.encode))) (some next))
    | failure {codec : Codec α} {count : Nat} {branches : Fin count → Cloud m α}
        (continuation : ArrsF (Control m) (Array α) Json) {outcomes error trees}
        (evaluated : ChildrenEvaluation branches outcomes)
        (collected : outcomes.mapM id = .error error)
        (children : ChildrenExpansion codec branches trees) :
        Expansion (.impure (.parallel codec count branches) continuation)
          (.fork trees (.error error) none)

  inductive ChildrenExpansion {m : Type → Type u} : {α : Type} → Codec α → {count : Nat} →
      (Fin count → Cloud m α) → List ExecutionTree → Prop where
    | empty (codec : Codec α) (branches : Fin 0 → Cloud m α) : ChildrenExpansion codec branches []
    | cons {codec : Codec α} {count : Nat} {branches : Fin (count + 1) → Cloud m α} {tree trees}
        (head : Expansion (codec.encode <$> branches 0) tree)
        (tail : ChildrenExpansion codec (fun index => branches index.succ) trees) :
        ChildrenExpansion codec branches (tree :: trees)
end

variable {m : Type → Type u}

/-- The tree records the existing pure semantics, including array-order failure
selection. It cannot invent an outcome for a program. -/
theorem Expansion.evaluation {program : Cloud m Json} {tree}
    (expansion : Expansion program tree) : Evaluation program tree.outcome := by
  match expansion with
  | .pure value => exact .pure value
  | .fail error continuation => exact .failure continuation (.fail error)
  | .delay rest => exact .success .delay (ContinuationEvaluation.of_apply rest.evaluation)
  | .success (codec := codec) evaluated collected _ rest =>
    have head := ControlEvaluation.parallel (codec := codec) evaluated
    rw [collected] at head
    exact .success head (ContinuationEvaluation.of_apply rest.evaluation)
  | .failure (codec := codec) continuation evaluated collected _ =>
    have head := ControlEvaluation.parallel (codec := codec) evaluated
    rw [collected] at head
    exact .failure continuation head
termination_by structural expansion

theorem ChildrenExpansion.size {codec : Codec α} {count : Nat} {branches : Fin count → Cloud m α} {trees}
    (expansion : ChildrenExpansion codec branches trees) : trees.length = count := by
  match expansion with
  | .empty .. => rfl
  | .cons _ tail => simpa using congrArg Nat.succ tail.size
termination_by structural expansion

/-- Indexed reconstruction selects the original branch, with its original codec. -/
theorem ChildrenExpansion.at {codec : Codec α} {count : Nat} {branches : Fin count → Cloud m α} {trees}
    (expansion : ChildrenExpansion codec branches trees) (index : Fin count) (inside : index.val < trees.length) :
    Expansion (codec.encode <$> branches index) (trees[index.val]) := by
  cases expansion with
  | empty => exact Fin.elim0 index
  | cons head tail =>
    cases index using Fin.cases with
    | zero => exact head
    | succ i => exact tail.at i (by rw [tail.size]; exact i.isLt)
termination_by count

/-- Every child tree has precisely its original branch's encoded result. -/
theorem ChildrenExpansion.outcomes {codec : Codec α} {count : Nat} {branches : Fin count → Cloud m α}
    {trees outcomes} (expansion : ChildrenExpansion codec branches trees)
    (evaluated : ChildrenEvaluation branches outcomes) :
    trees.map ExecutionTree.outcome = (outcomes.map (Except.map codec.encode)).toList := by
  match expansion with
  | .empty .. => cases evaluated; simp
  | .cons head tail =>
    cases evaluated with
    | cons first rest =>
      obtain ⟨outcome, original, encoded⟩ := head.evaluation.map_cases _ _
      have same := original.unique first
      simp [encoded, same, tail.outcomes rest]
termination_by structural expansion

private theorem expand_control {request : Control m α} {outcome work}
    {evaluation : ControlEvaluation request outcome} (cost : ControlWork 1 evaluation work)
    (supported : PureControl request) (continuation : ArrsF (Control m) α Json)
    (children : ∀ {β count} (codec : Codec β) (branches : Fin count → Cloud m β) {outcomes spent}
      {evaluation : ChildrenEvaluation branches outcomes}, ChildrenWork 1 evaluation spent →
      spent < work → (∀ index, PureProgram (branches index)) →
      ∃ trees, ChildrenExpansion codec branches trees)
    (rest : ∀ value, outcome = .ok value → ∃ tree, Expansion (ArrsF.apply continuation value) tree) :
    ∃ tree, Expansion (.impure request continuation) tree := by
  cases cost with
  | delay =>
    obtain ⟨tree, expanded⟩ := rest () rfl
    exact ⟨.delay tree, .delay expanded⟩
  | fail error => exact ⟨.terminal (.error error), .fail error continuation⟩
  | @parallel α codec count branches outcomes spent evaluated cost =>
    obtain ⟨trees, expanded⟩ := children codec branches cost (by omega) supported.2
    cases collected : outcomes.mapM id with
    | ok values =>
      obtain ⟨tree, next⟩ := rest values collected
      exact ⟨_, .success evaluated collected expanded next⟩
    | error error => exact ⟨_, .failure continuation evaluated collected expanded⟩

mutual
  /-- The completed evaluation bounds expansion, including transparent delays.
  No existing journal, successful replay, or scheduling policy is assumed. -/
  theorem ProgramWork.expand {program : Cloud m Json} {outcome work}
      {evaluation : Evaluation program outcome} (cost : ProgramWork 1 evaluation work)
      (supported : PureProgram program) : ∃ tree, Expansion program tree := by
    match cost with
    | .pure value => exact ⟨_, .pure value⟩
    | .success control remaining =>
      have positive := control.positive
      apply expand_control control supported.1
      · intro β count codec branches outcomes spent evaluation children smaller supported
        exact children.expand codec supported
      · intro value same
        cases same
        obtain ⟨_, rest⟩ := remaining.apply supported.2
        exact rest.expand (supported.2.apply _)
    | .failure continuation control =>
      apply expand_control control supported.1
      · intro β count codec branches outcomes spent evaluation children smaller supported
        exact children.expand codec supported
      · intro value same
        cases same
  termination_by 2 * (work + returnWork outcome)
  decreasing_by
    all_goals simp_wf
    all_goals try simp only [Nat.mul_add]
    all_goals omega

  theorem ChildrenWork.expand {count : Nat} {branches : Fin count → Cloud m α} {outcomes work}
      {evaluation : ChildrenEvaluation branches outcomes} (cost : ChildrenWork 1 evaluation work)
      (codec : Codec α) (supported : ∀ index, PureProgram (branches index)) :
      ∃ trees, ChildrenExpansion codec branches trees := by
    match cost with
    | .empty branches => exact ⟨[], .empty codec branches⟩
    | .cons first remaining =>
      have positive := first.total_positive
      obtain ⟨_, encoded⟩ := first.map (supported 0) codec.encode
      obtain ⟨tree, head⟩ := encoded.expand ((supported 0).map codec.encode)
      obtain ⟨trees, tail⟩ := remaining.expand codec (fun index => supported index.succ)
      exact ⟨tree :: trees, .cons head tail⟩
  termination_by 2 * work + 1
  decreasing_by
    all_goals simp_wf
    all_goals try simp only [returnWork_map]
    all_goals try simp only [Nat.mul_add]
    all_goals omega
end

/-- Every pure workflow has a finite tree whose output is the direct semantics.
The tree can be used to specify immutable records independently of delivery order. -/
theorem PureProgram.expansion {program : Cloud m Json} (supported : PureProgram program) :
    ∃ tree, Expansion program tree := by
  obtain ⟨_, evaluated⟩ := Evaluation.exists program supported
  obtain ⟨_, cost⟩ := evaluated.work_exists 1
  exact cost.expand supported

end LeanCloud.Proofs
