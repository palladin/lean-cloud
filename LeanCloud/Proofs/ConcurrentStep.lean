import LeanCloud.Proofs.ConcurrentProgress

/-! The actual replay step over the concurrent journal. Its response retains
both output safety and the publication/observation evidence needed for coverage.
Reconstruction can instead redirect a stale delivery to its completed ancestor. -/

namespace LeanCloud.Proofs.ConcurrentJournal
open Lean LeanEff Simulation SimulationBackend JournalAdapter JournalDb ReplayRecovery
open ReplayInterpreter.Internal

private abbrev workerDb := JournalDb.ofDb rawDb

def Emits (tree : ExecutionTree) (response : StepResult) (state : Durable) : Prop :=
  tree.EmitsActivated (view state) response

theorem Finished.emits {tree current node before after response}
    (route : TreeRoute tree Location.root current node)
    (active : route.Activated (view before)) (growth : Grows before after)
    (finished : Finished current node.exit before response after) : Emits tree response after := by
  have ready := active.grow growth.1
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

private theorem finish_progress {root : Cloud M Json} {tree current node}
    (whole : Expansion root tree) (route : TreeRoute tree Location.root current node)
    (comparable : Comparable (tree.journal Location.root)) (sameExit : (node.exit == node.exit) = true)
    (state : Durable) (valid : Valid (tree.journal Location.root) state)
    (active : route.Activated (view state)) (ready : node.FinishReady current (view state))
    (descriptors : ∀ parent index, current.parent? = some (parent, index) →
      ∃ count : Nat, view state (forkKey parent.key) = some (toJson count)) :
    Checked (tree.journal Location.root) (finish workerDb current node.exit)
      (fun response final => Emits tree response final ∧ CommandProgress current state node response final) state := by
  exact (route.finish_tree_checked whole comparable sameExit state valid ready descriptors).remember.weaken
    (fun _ _ h => ⟨h.2.emits route active h.1, .finished h.2⟩)

/-- At a selected command, the original program determines all branch writes,
joins, and completion values. Retain the actual command's progress evidence,
including the checkpoint behind a stale read or empty child notification. -/
theorem target_progress {root : Cloud M Json} {tree current node}
    (whole : Expansion root tree) (route : TreeRoute tree Location.root current node)
    (comparable : Comparable (tree.journal Location.root)) (sameExit : (node.exit == node.exit) = true)
    (blobs : BlobStorage Unit M) {program : Cloud M Json}
    (expanded : Expansion program node) (supported : PureProgram program)
    (state : Durable) (valid : Valid (tree.journal Location.root) state)
    (active : route.Activated (view state))
    (descriptors : ∀ parent index, current.parent? = some (parent, index) →
      ∃ count : Nat, view state (forkKey parent.key) = some (toJson count))
    (fuel : Nat) :
    Checked (tree.journal Location.root) (walk workerDb blobs (fuel + 1) program current current)
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
    apply checked_bind (load_checked _ current (tree.readable _ rootSize _) (whole.coherent rootSize member) state valid) valid
    intro answer observed bounded growth seen
    have admitted := seen.admitted whole rootSize member bounded
    have activated := active.grow growth.1
    cases seen with
    | missing absent noFork =>
      simp only [beq_self_eq_true, Option.isNone_none, Bool.and_self, ↓reduceIte]
      have fork : Expansion (.impure (.parallel codec count branches) continuation)
          (.fork children (.ok (.arr (values.map codec.encode))) (some next)) :=
        .success evaluated collected childrenExpansion expanded
      have allowed := fork.settle_admitted (ExecutionTree.PartialSlots.empty children)
      rw [childrenExpansion.size] at allowed
      apply checked_bind (save_checked _ current _
        (tree.admitted_agrees rootSize member allowed comparable) observed bounded) bounded
      intro ignored published valid later records
      apply checked_pure
      intro final finalValid last
      have published := fun entry included => last _ _ (records entry included)
      exact ⟨route.emits_initial_activated (activated.grow (later.trans last).1) count childrenExpansion.size published,
        .initialized childrenExpansion.size state (.refl _) (growth.trans (later.trans last)) absent noFork published⟩
    | completed outcome completed =>
      have same := admitted (.completed outcome) rfl
      change outcome = .success (.arr (values.map codec.encode)) at same
      subst outcome
      have size : values.size = count := (collect_outcomes_size _ _ collected).trans evaluated.size
      simp only [beq_self_eq_true, Option.isNone_some, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
        ← size, decode_group codec supported.1.1, pure_bind_action]
      apply checked_pure
      intro final finalValid later
      exact ⟨ExecutionTree.EmitsActivated.singleton ((activated.grow later.1).next (completed.grow later.1)),
        .joined (completed.grow later.1)⟩
    | suspended slots published incomplete settled =>
      have allowed := admitted (.suspended slots) rfl
      have size : slots.size = count := allowed.1.trans childrenExpansion.size
      simp only [beq_self_eq_true, Option.isNone_some, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
        size, bne_self_eq_false]
      apply checked_pure
      intro final finalValid later
      exact ⟨route.emits_missing_activated (activated.grow later.1) count childrenExpansion.size slots
        (by simpa only [allowed.1] using later _ _ (published_fork published).1),
        .waiting childrenExpansion.size slots size state (.refl _) (growth.trans later) incomplete settled
          (fun entry included => later _ _ (published entry included))⟩
  | @failure α codec count branches continuation outcomes error children evaluated collected childrenExpansion =>
    rw [walk]
    apply checked_bind (load_checked _ current (tree.readable _ rootSize _) (whole.coherent rootSize member) state valid) valid
    intro answer observed bounded growth seen
    have admitted := seen.admitted whole rootSize member bounded
    have activated := active.grow growth.1
    cases seen with
    | missing absent noFork =>
      simp only [beq_self_eq_true, Option.isNone_none, Bool.and_self, ↓reduceIte]
      have fork : Expansion (.impure (.parallel codec count branches) continuation) (.fork children (.error error) none) :=
        .failure continuation evaluated collected childrenExpansion
      have allowed := fork.settle_admitted (ExecutionTree.PartialSlots.empty children)
      rw [childrenExpansion.size] at allowed
      apply checked_bind (save_checked _ current _
        (tree.admitted_agrees rootSize member allowed comparable) observed bounded) bounded
      intro ignored published valid later records
      apply checked_pure
      intro final finalValid last
      have published := fun entry included => last _ _ (records entry included)
      exact ⟨route.emits_initial_activated (activated.grow (later.trans last).1) count childrenExpansion.size published,
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
      apply checked_pure
      intro final finalValid later
      exact ⟨route.emits_missing_activated (activated.grow later.1) count childrenExpansion.size slots
        (by simpa only [allowed.1] using later _ _ (published_fork published).1),
        .waiting childrenExpansion.size slots size state (.refl _) (growth.trans later) incomplete settled
          (fun entry included => later _ _ (published entry included))⟩

/-- Reconstruct and execute an activated command while other workers extend the
journal. The target and any concurrent ancestor redirect satisfy the same
program-derived response contract. -/
theorem walk_progress {program : Cloud M Json} {tree current node}
    (whole : Expansion program tree) (supported : PureProgram program)
    (route : TreeRoute tree Location.root current node)
    (comparable : Comparable (tree.journal Location.root)) (sameExit : (node.exit == node.exit) = true)
    (blobs : BlobStorage Unit M) (state : Durable) (valid : Valid (tree.journal Location.root) state)
    (active : route.Activated (view state))
    (descriptors : ∀ parent index, current.parent? = some (parent, index) →
      ∃ count : Nat, view state (forkKey parent.key) = some (toJson count))
    (fuel : Nat) (enough : route.prefixSteps + 1 ≤ fuel) :
    Checked (tree.journal Location.root) (walk workerDb blobs fuel program Location.root current)
      (fun response final => Emits tree response final ∧ StepProgress tree current node state response final) state := by
  have handle (source : Cloud M Json) (pureSource : PureProgram source) (expanded : Expansion source node)
      (currentState : Durable) (kept : Valid (tree.journal Location.root) currentState)
      (growth : Grows state currentState) (budget : Nat) (positive : 1 ≤ budget) :
      Checked (tree.journal Location.root) (walk workerDb blobs budget source current current)
        (fun response final => Emits tree response final ∧ StepProgress tree current node state response final) currentState := by
    cases budget with
    | zero => omega
    | succ budget =>
      have target := target_progress whole route comparable sameExit blobs expanded pureSource currentState kept
        (active.grow growth.1) (by
          intro parent index linked
          obtain ⟨count, stored⟩ := descriptors parent index linked
          exact ⟨count, growth _ _ stored⟩) budget
      exact target.weaken fun _ _ h => ⟨h.1, .command (h.2.grow growth (.refl _))⟩
  exact (reconstruct_checked whole route (fun _ h => h) blobs _ state 1 handle whole supported
    (by simp [Location.root]) state valid (.refl _) active fuel enough).weaken
      (fun _ _ result => result.elim id (fun redirect => ⟨redirect.emits, .redirect redirect⟩))

private def ParentAvailable (journal : Journal) (current : Location) : Prop :=
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
theorem step_progress {program : Cloud M Json} {tree current node}
    (whole : Expansion program tree) (supported : PureProgram program)
    (route : TreeRoute tree Location.root current node)
    (comparable : Comparable (tree.journal Location.root)) (sameExit : (node.exit == node.exit) = true)
    (blobs : BlobStorage Unit M) (state : Durable) (valid : Valid (tree.journal Location.root) state)
    (active : route.Activated (view state)) (fuel : Nat) (enough : route.prefixSteps + 1 ≤ fuel) :
    Checked (tree.journal Location.root) (ReplayInterpreter.Internal.step workerDb blobs fuel program current)
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
    apply checked_bind (load_checked _ parent (tree.readable _ rootSize _) (whole.coherent rootSize member) state valid) valid
    intro answer observed bounded growth seen
    have present := seen.not_missing (available parent index linked)
    cases seen with
    | missing absent noFork => exact False.elim (present rfl)
    | completed outcome recorded =>
      apply checked_pure
      intro final finalValid later
      exact ⟨ExecutionTree.EmitsActivated.singleton ((active.grow (growth.trans later).1).parent linked),
        .parent parent index outcome linked (recorded.grow later.1) rfl⟩
    | suspended slots published incomplete settled =>
      have walked := walk_progress whole supported route comparable sameExit blobs observed bounded (active.grow growth.1)
        (by
          intro actual child relation
          rw [linked] at relation
          cases relation
          exact ⟨slots.size, (published_fork published).1⟩) fuel enough
      exact walked.weaken fun _ _ h => ⟨h.1, h.2.grow growth (.refl _)⟩

/-- Output safety follows by forgetting the richer progress evidence. -/
theorem step_checked {program : Cloud M Json} {tree current node}
    (whole : Expansion program tree) (supported : PureProgram program)
    (route : TreeRoute tree Location.root current node)
    (comparable : Comparable (tree.journal Location.root)) (sameExit : (node.exit == node.exit) = true)
    (blobs : BlobStorage Unit M) (state : Durable) (valid : Valid (tree.journal Location.root) state)
    (active : route.Activated (view state)) (fuel : Nat) (enough : route.prefixSteps + 1 ≤ fuel) :
    Checked (tree.journal Location.root) (ReplayInterpreter.Internal.step workerDb blobs fuel program current) (Emits tree) state :=
  (step_progress whole supported route comparable sameExit blobs state valid active fuel enough).weaken
    (fun _ _ h => h.1)

/-- Any finite legal schedule of actual replay steps, including independent
crashes and retries. Every returned step succeeds; runnable locations retain
their original reconstruction prerequisites, and `done` has the direct meaning
of the pure program. Queue polling and publication are composed separately. -/
theorem step_concurrent {program : Cloud M Json} {tree : ExecutionTree}
    (whole : Expansion program tree) (supported : PureProgram program)
    (comparable : Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (locations : Fin count → Location) (blobs : BlobStorage Unit M) (fuel : Nat) (enough : sizeOf tree ≤ fuel)
    (initial : Durable) (bounded : Valid (tree.journal Location.root) initial)
    (active : ∀ worker, tree.Activated (view initial) (locations worker))
    (events : List (Event count))
    (final : Simulation.State Durable (Except CloudError StepResult × Unit) count)
    (executed :
      let start := fun worker => (ReplayInterpreter.Internal.step workerDb blobs fuel program (locations worker)).run ()
      Simulation.run start advance events (Simulation.State.initial initial start) = .ok final) :
    Grows initial final.durable ∧ Valid (tree.journal Location.root) final.durable ∧
      ∀ worker returned, (final.workers worker).outcome? = some returned →
        ∃ response, returned = (.ok response, ()) ∧ Emits tree response final.durable := by
  let start := fun worker => (ReplayInterpreter.Internal.step workerDb blobs fuel program (locations worker)).run ()
  let invariant := fun state => Valid (tree.journal Location.root) state ∧ Grows initial state
  let post := fun (_ : Fin count) (returned : Except CloudError StepResult × Unit) final =>
    ∃ response, returned = (.ok response, ()) ∧ Emits tree response final
  have preserved before after (kept : invariant before) (valid : Valid (tree.journal Location.root) after)
      (growth : Grows before after) : invariant after := ⟨valid, kept.2.trans growth⟩
  have fresh worker state (kept : invariant state) :
      Safe invariant Grows (post worker) (.ofProgram (start worker)) state := by
    obtain ⟨node, route, ready⟩ := active worker
    exact (step_checked whole supported route comparable (sameExit _ _ route.member) blobs state kept.1
      (ready.grow kept.2.1) fuel (Nat.le_trans route.fuel_bound enough)).strengthen invariant
        (fun _ h => h.1) preserved
  have clock elapsed state (kept : invariant state) :
      invariant (advance elapsed state) ∧ Grows state (advance elapsed state) := ⟨kept, .refl _⟩
  have safe : AllSafe invariant Grows post (Simulation.State.initial initial start) :=
    ⟨⟨bounded, .refl _⟩, fun worker => fresh worker initial ⟨bounded, .refl _⟩⟩
  obtain ⟨growth, kept, workers⟩ := Simulation.run_safe (valid := invariant) (grows := Grows)
    Grows.refl (fun first second => first.trans second) start advance post fresh clock events safe executed
  exact ⟨growth, kept.1, fun worker returned done => (workers worker).returned Grows.refl kept done⟩

end LeanCloud.Proofs.ConcurrentJournal
