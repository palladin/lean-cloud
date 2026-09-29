import LeanCloud.Proofs.StableProgress
import LeanCloud.Proofs.CoverageResponses
import LeanCloud.Proofs.WorkerCases

/-! The actual worker produces structural progress when its before and after
journals agree. Fork initialization must grow the journal; the other responses
report a branch or expose children or a continuation. -/

namespace LeanCloud.Proofs
open Lean LeanEff JournalDb JournalAdapter ReplayRecovery ReplayInterpreter.Internal

/-- The queue has published a response: a final outcome is durable, or each
successor is available. Later fair delivery will instantiate `available`. -/
def ResponseAvailable (rootDone : Prop) (available : Location → Prop) : StepResult → Prop
  | .done _ => rootDone
  | .runnable locations => ∀ location ∈ locations, available location

def StableResponse (initial : Journal) (node : ExecutionTree) (current : Location)
    (response : StepResult) (journal : Journal) : Prop :=
  journal = initial → ∀ rootDone available, ResponseAvailable rootDone available response →
    StableAdvance journal available node current (BranchReported journal rootDone node current)

/-- The shortcut's response is observable work for the original parent. -/
def ParentResponse (initial : Journal) (current : Location) (response : StepResult) : Prop :=
  ∀ parent index outcome, current.parent? = some (parent, index) →
    JournalDb.get raw parent.key initial = (some (toJson (Result.completed outcome)), initial) →
      response = .runnable #[parent]

/-- An absent logical fork has neither a completed cache nor a descriptor. -/
private theorem fork_missing {tree : ExecutionTree} {root current : Location} {children result next journal}
    (nonempty : 0 < root.size) (member : (current, ExecutionTree.fork children result next) ∈ tree.nodes root)
    (bounded : Extends journal (tree.journal root))
    (view : JournalDb.get raw current.key journal = (none, journal)) :
    journal (resultKey current.key) = none ∧ journal (forkKey current.key) = none := by
  obtain ⟨descriptor, expected, _⟩ := tree.fork_fields nonempty member
  cases cached : journal (resultKey current.key) with
  | some value =>
    have same := (bounded _ _ cached).symm.trans expected
    cases same
    have impossible := (get_completed _ _ _ cached).symm.trans view
    cases impossible
  | none =>
    cases recorded : journal (forkKey current.key) with
    | none => exact ⟨rfl, rfl⟩
    | some value =>
      have same := (bounded _ _ recorded).symm.trans descriptor
      cases same
      obtain ⟨_, physical⟩ := tree.observedSlots_spec nonempty member journal bounded
      have observed := get_fork journal current.key (ExecutionTree.observedSlots children journal current) cached
        (by simpa [ExecutionTree.observedSlots] using recorded) (by
          intro i inside
          exact physical i (by simpa [ExecutionTree.observedSlots] using inside))
      have impossible := observed.symm.trans view
      cases impossible

/-- Publishing an initially missing fork adds a record even for an empty
parallel group, whose initializer stores its completed result immediately. -/
private theorem initialized_changes {initial journal : Journal} {current : Location} {count : Nat}
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

/-- A successful finish discharges its original branch, either by publishing
the root outcome or by recording its child slot/completed parent. -/
theorem TreeRoute.finish_stable {m : Type → Type} {program : Cloud m Json} {tree current node}
    (expansion : Expansion program tree) (route : TreeRoute tree Location.root current node)
    (initial : Journal) (bounded : Extends initial (tree.journal Location.root))
    (parentOpen : OpenParent initial current) (ready : node.FinishReady current initial)
    (comparable : Comparable (tree.journal Location.root)) (sameExit : (node.exit == node.exit) = true) :
    Spec (· = initial) (finish db current node.exit)
      (fun response journal => Between initial (tree.journal Location.root) journal ∧
        StableResponse initial node current response journal)
      (Between initial (tree.journal Location.root)) := by
  cases linked : current.parent? with
  | none =>
    apply (route.finish_root linked comparable sameExit initial bounded ready).weaken
      (by intro journal same; subst journal; exact ⟨Extends.refl _, bounded⟩) _ (fun _ h => h)
    intro response journal h
    obtain ⟨rfl, progress⟩ := h
    refine ⟨progress, ?_⟩
    intro _ rootDone available published
    exact .reported (by simpa only [BranchReported, linked, ResponseAvailable] using published)
  | some pair =>
    obtain ⟨parent, index⟩ := pair
    obtain ⟨slots, view⟩ := parentOpen parent index linked
    obtain ⟨children, result, next, inside, member, _⟩ := route.child_outcome linked
    have rootSize : 0 < Location.root.size := by simp [Location.root]
    have before := tree.suspended_snapshot rootSize member initial bounded view
    have slotBound : index < slots.size := by rw [before.2.2.1.1]; exact inside
    apply (route.finish_child expansion linked initial bounded view comparable ready sameExit).weaken
      (fun _ h => h) _ (fun _ h => h)
    intro response journal h
    obtain ⟨progress, _, parentView, _⟩ := h
    refine ⟨progress, ?_⟩
    intro _ rootDone available _
    apply StableAdvance.reported
    simp only [BranchReported, linked]
    cases settled : Result.settle (slots.set! index (some node.exit)) with
    | completed outcome =>
      rw [settled] at parentView
      exact .inr ⟨_, tree.fork_completed_at rootSize member journal progress.2 parentView⟩
    | suspended remaining =>
      rw [settled] at parentView
      have after := tree.suspended_snapshot rootSize member journal progress.2 parentView
      have physical := after.2.2.2 index (by rw [after.2.2.1.1]; exact inside)
      rw [← Result.settle_suspended settled, Array.getElem!_set!_self _ _ _ slotBound] at physical
      exact .inl physical

/-- An activated delivery is live or wakes an already completed parent. In
both cases the actual stable response satisfies the structural progress rule. -/
theorem TreeRoute.activated_stable {program : Cloud (CrashModel.M Journal) Json} {tree target node}
    (expansion : Expansion program tree) (supported : PureProgram program)
    (route : TreeRoute tree Location.root target node)
    (initial : Journal) (bounded : Extends initial (tree.journal Location.root))
    (causal : tree.Causal Location.root initial) (activated : route.Activated initial)
    (comparable : Comparable (tree.journal Location.root)) (sameExit : (node.exit == node.exit) = true)
    (blobs : BlobStorage Unit (CrashModel.M Journal)) (fuel : Nat) (enough : route.prefixSteps + 1 ≤ fuel) :
    Spec (· = initial) (step db blobs fuel program target)
      (fun response journal => Between initial (tree.journal Location.root) journal ∧
        StableResponse initial node target response journal ∧ ParentResponse initial target response)
      (Between initial (tree.journal Location.root)) := by
  have rootSize : 0 < Location.root.size := by simp [Location.root]
  apply route.worker_cases expansion supported initial bounded causal activated blobs
    ⟨Extends.refl _, bounded⟩ ?_ ?_ fuel enough
  · intro parentOpen
    obtain ⟨leaf, expanded⟩ := expansion.node route.member
    have rules : CommandSpec initial target node
        (fun response journal => Between initial (tree.journal Location.root) journal ∧
          StableResponse initial node target response journal) (Between initial (tree.journal Location.root)) := by
      constructor
      · exact fun ready => route.finish_stable expansion initial bounded parentOpen ready comparable sameExit
      · intro children result next shape view
        subst node
        have absent := fork_missing rootSize route.member bounded view
        have saved := tree.save_admitted rootSize route.member
          (expanded.settle_admitted (ExecutionTree.PartialSlots.empty children)) comparable initial
        apply Spec.bind (saved.weaken (pre' := (· = initial))
          (by intro journal same; subst journal; exact ⟨Extends.refl _, bounded⟩)
          (fun _ _ h => h) (fun _ h => h))
        intro _
        exact (Spec.pure _ _).weaken (fun _ h => h)
          (fun _ _ ⟨_, progress, published⟩ => ⟨progress, fun same => False.elim (initialized_changes absent published same)⟩)
          (fun _ h => h)
      · intro children value next shape completed
        subst node
        apply Spec.return_at
        refine ⟨⟨Extends.refl _, bounded⟩, ?_⟩
        intro _ rootDone available published
        exact .continued completed (published target.next (by simp))
      · intro children result next shape slots view
        subst node
        apply Spec.return_at
        refine ⟨⟨Extends.refl _, bounded⟩, ?_⟩
        intro _ rootDone available published
        have snapshot := tree.suspended_snapshot rootSize route.member initial bounded view
        refine .waiting (by simpa only [snapshot.2.2.1.1] using snapshot.2.1) snapshot.1
          (expansion.suspended_missing rootSize route.member bounded view) ?_
        intro index
        cases stored : initial (childKey target.key index.val) with
        | some value =>
          have same := (bounded _ _ stored).symm.trans ((tree.fork_fields rootSize route.member).2.2 index)
          cases same
          exact .inl (.inl stored)
        | none =>
          apply Or.inr
          apply published
          have physical := snapshot.2.2.2 index.val (by rw [snapshot.2.2.1.1]; exact index.isLt)
          have empty : slots[index.val]! = none := by
            cases slot : slots[index.val]! with
            | none => rfl
            | some value => simp [slot, stored] at physical
          apply Array.mem_filterMap.mpr
          exact ⟨index.val, Array.mem_ofFn.mpr ⟨index, rfl⟩, by simp [empty]⟩

    have augment {action : Worker StepResult} (spec : Spec (· = initial) action
        (fun response journal => Between initial (tree.journal Location.root) journal ∧
          StableResponse initial node target response journal) (Between initial (tree.journal Location.root))) :=
      spec.weaken (fun _ h => h)
        (post' := fun response journal => Between initial (tree.journal Location.root) journal ∧
          StableResponse initial node target response journal ∧ ParentResponse initial target response)
        (fun response journal h => ⟨h.1, h.2, fun parent index outcome linked completed => by
          obtain ⟨slots, suspended⟩ := parentOpen parent index linked
          have impossible : Result.suspended slots = .completed outcome := toJson_injective result_roundtrip
            (Option.some.inj (congrArg Prod.fst (suspended.symm.trans completed)))
          cases impossible⟩) (fun _ h => h)
    exact ⟨fun ready => augment (rules.finished ready),
      fun children result next shape view => augment (rules.fresh children result next shape view),
      fun children value next shape completed => augment (rules.joined children value next shape completed),
      fun children result next shape slots view => augment (rules.waiting children result next shape slots view)⟩
  · intro parent index outcome linked view
    obtain ⟨children, result, next, _, member, _⟩ := route.child_outcome linked
    have completed := tree.fork_completed_at rootSize member initial bounded view
    refine ⟨⟨Extends.refl _, bounded⟩, ?_, ?_⟩
    · intro _ rootDone available _
      apply StableAdvance.reported
      simp only [BranchReported, linked]
      exact .inr ⟨_, completed⟩
    · intro other child _ actual _
      rw [linked] at actual
      cases actual
      rfl

end LeanCloud.Proofs
