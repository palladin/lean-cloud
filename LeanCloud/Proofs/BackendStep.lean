import LeanCloud.Proofs.BackendProgress

/-! The actual public replay step over contract-based Db operations. Its
response retains the program-derived value and routing evidence, including the
earlier observation behind a partial join or an empty child notification. -/

namespace LeanCloud.Backend.Proofs.Journal
open Lean LeanEff LeanCloud.Proofs JournalAdapter JournalDb ReplayRecovery ReplayInterpreter.Internal

def Emits (tree : ExecutionTree) (response : StepResult) (state : Backend.State) : Prop :=
  tree.EmitsActivated (view state) response

theorem Finished.emits {tree current node before after response}
    (route : TreeRoute tree Location.root current node)
    (active : route.Activated (view before)) (growth : Grows before after)
    (finished : Finished current node.exit before response after) : Emits tree response after := by
  have ready := active.grow growth.reads
  cases linked : current.parent? with
  | none =>
    have same : response = .done node.exit := by simpa only [Finished, linked] using finished.2
    rw [same]
    exact route.root_outcome linked
  | some pair =>
    obtain ⟨parent, index⟩ := pair
    have notified : Notification parent index node.exit before after response := by
      simpa only [Finished, linked] using finished.2
    cases notified with
    | wake result completed => exact ExecutionTree.EmitsActivated.singleton (ready.parent linked)
    | waiting => intro _ member; simp at member

private theorem finish_progress {root : Cloud Replay.M Json} {tree current node}
    (whole : Expansion root tree) (route : TreeRoute tree Location.root current node)
    (comparable : Comparable (tree.journal Location.root)) (sameExit : (node.exit == node.exit) = true)
    (state : Backend.State) (valid : Valid (tree.journal Location.root) state)
    (active : route.Activated (view state)) (ready : node.FinishReady current (view state))
    (descriptors : ∀ parent index, current.parent? = some (parent, index) →
      ∃ count : Nat, view state (forkKey parent.key) = some (toJson count)) :
    ActionChecked (tree.journal Location.root) (finish workerDb current node.exit)
      (fun response final => Emits tree response final ∧ CommandProgress current state node response final) state := by
  exact (finish_tree_checked whole route comparable sameExit state valid ready descriptors).remember.weaken
    (fun _ _ h => ⟨h.2.emits route active h.1, .finished h.2⟩)

/-- At a selected command, the original program determines all branch writes,
joins, and completion values. Retain the actual command's progress evidence,
including the checkpoint behind a stale read or empty child notification. -/
theorem target_progress {root : Cloud Replay.M Json} {tree current node}
    (whole : Expansion root tree) (route : TreeRoute tree Location.root current node)
    (comparable : Comparable (tree.journal Location.root)) (sameExit : (node.exit == node.exit) = true)
    (blobs : BlobStorage Unit Replay.M) {program : Cloud Replay.M Json}
    (expanded : Expansion program node) (supported : PureProgram program)
    (state : Backend.State) (valid : Valid (tree.journal Location.root) state)
    (active : route.Activated (view state))
    (descriptors : ∀ parent index, current.parent? = some (parent, index) →
      ∃ count : Nat, view state (forkKey parent.key) = some (toJson count))
    (fuel : Nat) :
    ActionChecked (tree.journal Location.root) (walk workerDb blobs (fuel + 1) program current current)
      (fun response final => Emits tree response final ∧ CommandProgress current state node response final) state := by
  have rootSize : 0 < Location.root.size := by simp [Location.root]
  have member := route.member
  cases expanded with
  | pure value =>
    simp only [walk, beq_self_eq_true, ↓reduceIte]
    exact finish_progress whole route comparable sameExit state valid active trivial descriptors
  | fail error continuation =>
    simp only [walk, beq_self_eq_true, ↓reduceIte]
    exact finish_progress whole route comparable sameExit state valid active trivial descriptors
  | delay expanded => exact False.elim (route.not_delay _ rfl)
  | @success α codec count branches continuation outcomes values children next evaluated collected childrenExpansion expanded =>
    rw [walk]
    apply ActionChecked.bind (load_checked _ current (tree.readable _ rootSize _) (whole.coherent rootSize member) state valid) valid
    intro answer observed bounded growth seen
    have admitted := seen.admitted whole rootSize member bounded
    have activated := active.grow growth.reads
    cases seen with
    | missing absent noFork =>
      simp only [beq_self_eq_true, Option.isNone_none, Bool.and_self, ↓reduceIte]
      have fork : Expansion (.impure (.parallel codec count branches) continuation)
          (.fork children (.ok (.arr (values.map codec.encode))) (some next)) :=
        .success evaluated collected childrenExpansion expanded
      have allowed := fork.settle_admitted (ExecutionTree.PartialSlots.empty children)
      rw [childrenExpansion.size] at allowed
      apply ActionChecked.bind (save_checked _ current _
        (tree.admitted_agrees rootSize member allowed comparable) observed bounded) bounded
      intro ignored published valid later records
      apply action_pure
      intro final finalValid last
      have published := fun entry included => last _ _ (records entry included)
      exact ⟨route.emits_initial_activated (activated.grow (later.trans last)) count childrenExpansion.size published,
        .initialized childrenExpansion.size state (.refl _) (growth.trans (later.trans last)) absent noFork published⟩
    | completed outcome completed =>
      have same := admitted (.completed outcome) rfl
      change outcome = .success (.arr (values.map codec.encode)) at same
      subst outcome
      have size : values.size = count := (collect_outcomes_size _ _ collected).trans evaluated.size
      simp only [beq_self_eq_true, Option.isNone_some, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
        ← size, decode_group codec supported.1.1, action_pure_bind]
      apply action_pure
      intro final finalValid later
      exact ⟨ExecutionTree.EmitsActivated.singleton ((activated.grow later).next (completed.grow later)),
        .joined (completed.grow later)⟩
    | suspended slots published incomplete settled =>
      have allowed := admitted (.suspended slots) rfl
      have size : slots.size = count := allowed.1.trans childrenExpansion.size
      simp only [beq_self_eq_true, Option.isNone_some, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
        size, bne_self_eq_false]
      apply action_pure
      intro final finalValid later
      exact ⟨route.emits_missing_activated (activated.grow later) count childrenExpansion.size slots
        (by simpa only [allowed.1] using later _ _ (published_fork published).1),
        .waiting childrenExpansion.size slots size state (.refl _) (growth.trans later) incomplete settled
          (fun entry included => later _ _ (published entry included))⟩
  | @failure α codec count branches continuation outcomes error children evaluated collected childrenExpansion =>
    rw [walk]
    apply ActionChecked.bind (load_checked _ current (tree.readable _ rootSize _) (whole.coherent rootSize member) state valid) valid
    intro answer observed bounded growth seen
    have admitted := seen.admitted whole rootSize member bounded
    have activated := active.grow growth.reads
    cases seen with
    | missing absent noFork =>
      simp only [beq_self_eq_true, Option.isNone_none, Bool.and_self, ↓reduceIte]
      have fork : Expansion (.impure (.parallel codec count branches) continuation) (.fork children (.error error) none) :=
        .failure continuation evaluated collected childrenExpansion
      have allowed := fork.settle_admitted (ExecutionTree.PartialSlots.empty children)
      rw [childrenExpansion.size] at allowed
      apply ActionChecked.bind (save_checked _ current _
        (tree.admitted_agrees rootSize member allowed comparable) observed bounded) bounded
      intro ignored published valid later records
      apply action_pure
      intro final finalValid last
      have published := fun entry included => last _ _ (records entry included)
      exact ⟨route.emits_initial_activated (activated.grow (later.trans last)) count childrenExpansion.size published,
        .initialized childrenExpansion.size state (.refl _) (growth.trans (later.trans last)) absent noFork published⟩
    | completed outcome completed =>
      have same := admitted (.completed outcome) rfl
      change outcome = .failure error at same
      subst outcome
      simp only [beq_self_eq_true, Option.isNone_some, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
      have finished := finish_progress whole route comparable sameExit observed bounded activated
        (completed.view bounded (tree.fork_fields rootSize member).2.1) (by
          intro parent index linked
          obtain ⟨count, stored⟩ := descriptors parent index linked
          exact ⟨count, growth _ _ stored⟩)
      exact finished.weaken fun _ _ h => ⟨h.1, h.2.grow growth (.refl _)⟩
    | suspended slots published incomplete settled =>
      have allowed := admitted (.suspended slots) rfl
      have size : slots.size = count := allowed.1.trans childrenExpansion.size
      simp only [beq_self_eq_true, Option.isNone_some, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
        size, bne_self_eq_false]
      apply action_pure
      intro final finalValid later
      exact ⟨route.emits_missing_activated (activated.grow later) count childrenExpansion.size slots
        (by simpa only [allowed.1] using later _ _ (published_fork published).1),
        .waiting childrenExpansion.size slots size state (.refl _) (growth.trans later) incomplete settled
          (fun entry included => later _ _ (published entry included))⟩

/-- Reconstruct and execute an activated command while other workers extend the
journal. The target and any concurrent ancestor redirect satisfy the same
program-derived response contract. -/
theorem walk_progress {program : Cloud Replay.M Json} {tree current node}
    (whole : Expansion program tree) (supported : PureProgram program)
    (route : TreeRoute tree Location.root current node)
    (comparable : Comparable (tree.journal Location.root)) (sameExit : (node.exit == node.exit) = true)
    (blobs : BlobStorage Unit Replay.M) (state : Backend.State) (valid : Valid (tree.journal Location.root) state)
    (active : route.Activated (view state))
    (descriptors : ∀ parent index, current.parent? = some (parent, index) →
      ∃ count : Nat, view state (forkKey parent.key) = some (toJson count))
    (fuel : Nat) (enough : route.prefixSteps + 1 ≤ fuel) :
    ActionChecked (tree.journal Location.root) (walk workerDb blobs fuel program Location.root current)
      (fun response final => Emits tree response final ∧ StepProgress tree current node state response final) state := by
  have handle (source : Cloud Replay.M Json) (pureSource : PureProgram source) (expanded : Expansion source node)
      (currentState : Backend.State) (kept : Valid (tree.journal Location.root) currentState)
      (growth : Grows state currentState) (budget : Nat) (positive : 1 ≤ budget) :
      ActionChecked (tree.journal Location.root) (walk workerDb blobs budget source current current)
        (fun response final => Emits tree response final ∧ StepProgress tree current node state response final) currentState := by
    cases budget with
    | zero => omega
    | succ budget =>
      have target := target_progress whole route comparable sameExit blobs expanded pureSource currentState kept
        (active.grow growth) (by
          intro parent index linked
          obtain ⟨count, stored⟩ := descriptors parent index linked
          exact ⟨count, growth _ _ stored⟩) budget
      exact target.weaken fun _ _ h => ⟨h.1, .command (h.2.grow growth (.refl _))⟩
  exact (reconstruct_checked whole route (fun _ h => h) blobs _ state 1 handle whole supported
    (by simp [Location.root]) state valid (.refl _) active fuel enough).weaken
      (fun _ _ result => result.elim id (fun redirect => ⟨redirect.emits, .redirect redirect⟩))

private def ParentAvailable (journal : View) (current : Location) : Prop :=
  ∀ parent index, current.parent? = some (parent, index) →
    (∃ count : Nat, journal (forkKey parent.key) = some (toJson count)) ∨
      ∃ outcome, CompletedAt journal parent.key outcome

private theorem parent_available {tree current target node journal}
    {route : TreeRoute tree current target node} (active : route.Activated journal)
    (nonempty : 0 < current.size) (outer : ParentAvailable journal current) :
    ParentAvailable journal target := by
  induction route with
  | terminal | fork => exact outer
  | delay rest ih => exact ih active nonempty outer
  | next rest ih =>
    apply ih active.2 (by simpa using nonempty)
    intro parent index linked
    exact outer parent index ((Location.next_parent_eq _).symm.trans linked)
  | @child children result next current target node index rest ih =>
    apply ih active.2 (by simp)
    intro parent child linked
    rw [Location.parent_child current nonempty index.val] at linked
    cases linked
    exact active.1.imp (fun descriptor => ⟨_, descriptor⟩) (fun completed => ⟨_, completed⟩)

/-- The actual public step, including its parent check, preserves compatible
records and records why it emitted its response. All routing and parent
prerequisites follow from the delivered activation. -/
theorem step_progress {program : Cloud Replay.M Json} {tree current node}
    (whole : Expansion program tree) (supported : PureProgram program)
    (route : TreeRoute tree Location.root current node)
    (comparable : Comparable (tree.journal Location.root)) (sameExit : (node.exit == node.exit) = true)
    (blobs : BlobStorage Unit Replay.M) (state : Backend.State) (valid : Valid (tree.journal Location.root) state)
    (active : route.Activated (view state)) (fuel : Nat) (enough : route.prefixSteps + 1 ≤ fuel) :
    ActionChecked (tree.journal Location.root) (ReplayInterpreter.Internal.step workerDb blobs fuel program current)
      (fun response final => Emits tree response final ∧ StepProgress tree current node state response final) state := by
  have rootSize : 0 < Location.root.size := by simp [Location.root]
  rw [ReplayInterpreter.Internal.step]
  simp only [route.root_guard, Bool.false_eq_true, ↓reduceIte]
  cases linked : current.parent? with
  | none =>
    apply walk_progress whole supported route comparable sameExit blobs state valid active _ fuel enough
    intro parent index impossible
    simp [linked] at impossible
  | some pair =>
    obtain ⟨parent, index⟩ := pair
    obtain ⟨children, result, next, inside, member, outcome⟩ := route.child_outcome linked
    have available := parent_available active rootSize (by simp [ParentAvailable, Location.root, Location.parent?])
    apply ActionChecked.bind (load_checked _ parent (tree.readable _ rootSize _) (whole.coherent rootSize member) state valid) valid
    intro answer observed bounded growth seen
    have present := seen.not_missing (available parent index linked)
    cases seen with
    | missing absent noFork => exact False.elim (present rfl)
    | completed outcome recorded =>
      apply action_pure
      intro final finalValid later
      exact ⟨ExecutionTree.EmitsActivated.singleton ((active.grow (growth.trans later)).parent linked),
        .parent parent index outcome linked (recorded.grow later) rfl⟩
    | suspended slots published incomplete settled =>
      have walked := walk_progress whole supported route comparable sameExit blobs observed bounded (active.grow growth)
        (by
          intro actual child relation
          rw [linked] at relation
          cases relation
          exact ⟨slots.size, (published_fork published).1⟩) fuel enough
      exact walked.weaken fun _ _ h => ⟨h.1, h.2.grow growth (.refl _)⟩

/-- Output safety follows by forgetting the richer progress evidence. -/
theorem step_checked {program : Cloud Replay.M Json} {tree current node}
    (whole : Expansion program tree) (supported : PureProgram program)
    (route : TreeRoute tree Location.root current node)
    (comparable : Comparable (tree.journal Location.root)) (sameExit : (node.exit == node.exit) = true)
    (blobs : BlobStorage Unit Replay.M) (state : Backend.State) (valid : Valid (tree.journal Location.root) state)
    (active : route.Activated (view state)) (fuel : Nat) (enough : route.prefixSteps + 1 ≤ fuel) :
    ActionChecked (tree.journal Location.root) (ReplayInterpreter.Internal.step workerDb blobs fuel program current) (Emits tree) state :=
  (step_progress whole supported route comparable sameExit blobs state valid active fuel enough).weaken
    (fun _ _ h => h.1)

end LeanCloud.Backend.Proofs.Journal

