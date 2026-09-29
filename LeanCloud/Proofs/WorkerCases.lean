import LeanCloud.Proofs.Reconstruction
import LeanCloud.Proofs.TreeActivation

/-! Shared verification of the actual replay worker. Safety, coverage, and
progress supply command-specific properties to the same control-flow proof. -/

namespace LeanCloud.Proofs
open Lean LeanEff CrashModel JournalAdapter ReplayRecovery ReplayInterpreter.Internal

/-- The four proof obligations of a live command. They describe the actual
worker operations and carry no evaluator or execution assumptions. -/
structure CommandSpec (initial : Journal) (current : Location) (node : ExecutionTree)
    (post : StepResult → Journal → Prop) (stopped : Journal → Prop) : Prop where
  finished : node.FinishReady current initial → Spec (· = initial) (finish db current node.exit) post stopped
  fresh : ∀ children result next, node = .fork children result next →
      JournalDb.get raw current.key initial = (none, initial) →
      Spec (· = initial) (do
        save db current (Result.settle (Array.replicate children.length none))
        pure (.runnable (if children.length == 0 then #[current] else
          Array.ofFn fun i : Fin children.length => current.child i.val))) post stopped
  joined : ∀ children value next, node = .fork children (.ok value) (some next) →
      CompletedAt initial current.key (.success value) →
      Spec (· = initial) (pure (.runnable #[current.next])) post stopped
  waiting : ∀ children result next, node = .fork children result next →
      ∀ slots : Array (Option Exit), JournalDb.get raw current.key initial =
        (some (toJson (Result.suspended slots)), initial) →
      Spec (· = initial) (pure (.runnable ((Array.ofFn fun i : Fin children.length => i.val).filterMap fun i =>
        if slots[i]!.isNone then some (current.child i) else none))) post stopped

/-- Verify a selected command once, independently of the property being proved.
Clients handle completion, initialization, a successful join, and missing-child
publication. Typed decoding and the program's control cases are discharged here. -/
theorem TreeRoute.target_cases {m : Type → Type} {rootProgram : Cloud m Json} {tree current node}
    (rootExpansion : Expansion rootProgram tree) (route : TreeRoute tree Location.root current node)
    (initial : Journal) (bounded : Extends initial (tree.journal Location.root))
    (blobs : BlobStorage Unit (M Journal))
    {program : Cloud (M Journal) Json} (expansion : Expansion program node) (supported : PureProgram program)
    (fuel : Nat) {post : StepResult → Journal → Prop} {stopped : Journal → Prop} (safe : stopped initial)
    (rules : CommandSpec initial current node post stopped) :
    Spec (· = initial) (walk db blobs (fuel + 1) program current current) post stopped := by
  obtain ⟨finished, fresh, joined, waiting⟩ := rules
  cases expansion with
  | pure value =>
    simpa only [walk, beq_self_eq_true, ↓reduceIte, ExecutionTree.exit, ExecutionTree.outcome,
      encodeOutcome, Codec.encode, id_eq] using finished trivial
  | fail error continuation =>
    simpa only [walk, beq_self_eq_true, ↓reduceIte, ExecutionTree.exit, ExecutionTree.outcome,
      encodeOutcome] using finished trivial
  | delay expanded => exact False.elim (route.not_delay _ rfl)
  | @success α codec count branches continuation outcomes values children next evaluated collected childrenExpansion expanded =>
    have countEq := childrenExpansion.size
    subst count
    apply fork_cases rootExpansion route.member initial bounded blobs fuel codec children.length branches continuation rfl safe
    · exact fresh _ _ _ rfl
    · intro view
      have size : values.size = children.length := (collect_outcomes_size _ _ collected).trans evaluated.size
      simp only [encodeOutcome, Codec.encode, id_eq, ← size,
        ReplayModel.decode_group_encoded codec supported.1.1 values, pure_bind]
      exact joined _ _ _ rfl (tree.fork_completed_at (by simp [Location.root]) route.member initial bounded view)
    · exact waiting _ _ _ rfl
  | @failure α codec count branches continuation outcomes error children evaluated collected childrenExpansion =>
    have countEq := childrenExpansion.size
    subst count
    apply fork_cases rootExpansion route.member initial bounded blobs fuel codec children.length branches continuation rfl safe
    · exact fresh _ _ _ rfl
    · exact finished
    · exact waiting _ _ _ rfl

/-- Activation decides whether to reconstruct a live command or wake an
already completed parent. All clients share the same traversal and fuel bound. -/
theorem TreeRoute.worker_cases {program : Cloud (M Journal) Json} {tree current node}
    (expansion : Expansion program tree) (supported : PureProgram program)
    (route : TreeRoute tree Location.root current node)
    (initial : Journal) (bounded : Extends initial (tree.journal Location.root))
    (causal : tree.Causal Location.root initial) (activated : route.Activated initial)
    (blobs : BlobStorage Unit (M Journal))
    {post : StepResult → Journal → Prop} {stopped : Journal → Prop} (safe : stopped initial)
    (live : OpenParent initial current → CommandSpec initial current node post stopped)
    (obsolete : ∀ parent index outcome, current.parent? = some (parent, index) →
      JournalDb.get raw parent.key initial = (some (toJson (Result.completed outcome)), initial) →
      post (.runnable #[parent]) initial) :
    ∀ fuel, route.prefixSteps + 1 ≤ fuel → Spec (· = initial) (step db blobs fuel program current) post stopped := by
  intro fuel enough
  rcases route.delivery_ready expansion bounded causal activated with ⟨ready, parentOpen⟩ |
    ⟨parent, index, outcome, linked, recorded⟩
  · apply route.step_reconstruct initial blobs post stopped safe 1 _ expansion supported ready parentOpen fuel enough
    intro leaf pureLeaf expanded budget sufficient
    cases budget with
    | zero => omega
    | succ budget => exact route.target_cases expansion initial bounded blobs expanded pureLeaf budget safe (live parentOpen)
  · exact (step_completed_parent_reads initial current parent index outcome route.root_guard linked recorded blobs fuel program).weaken
      (fun _ h => h)
      (fun _ _ ⟨same, unchanged⟩ => ⟨.runnable #[parent], same, unchanged ▸ obsolete parent index outcome linked recorded⟩)
      (fun _ h => h ▸ safe)

end LeanCloud.Proofs
