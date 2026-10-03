import LeanCloud.Proofs.BackendTree
import LeanCloud.Proofs.Reconstruction
import LeanCloud.Proofs.TreeSuccessors

/-! Location reconstruction with arbitrary concurrent service operations.
Pure-prefix replay either reaches the original command or returns a justified
wakeup of a completed ancestor. -/

namespace LeanCloud.Backend.Proofs.Journal
open Lean LeanEff LeanCloud.Proofs JournalAdapter JournalDb ReplayRecovery ReplayInterpreter.Internal

theorem decode_group (codec : Codec α) (law : CodecLaw codec) (values : Array α) :
    decodeGroup (m := StateT Unit Replay.M) codec values.size (.arr (values.map codec.encode)) = pure values := by
  letI : Codec α := codec
  have decoded : (inferInstance : Codec (Array α)).decode (.arr (values.map codec.encode)) = .ok values :=
    codec_array law values
  simp only [decodeGroup, decode, decoded]
  funext handle
  simp [bind, pure, ExceptT.bind, ExceptT.mk, ExceptT.pure, ExceptT.bindCont, StateT.bind, StateT.pure, EffF.bind]

/-- A stale child can wake a completed fork on its original reconstruction path.
This records both the original path and durable completion evidence. -/
def Redirect (tree : ExecutionTree) (current target : Location) (response : StepResult) (state : Backend.State) : Prop :=
  ∃ location children result next, ∃ route : TreeRoute tree current location (.fork children result next),
    route.Activated (view state) ∧
    CompletedAt (view state) location.key (encodeOutcome (inferInstance : Codec Json) result) ∧
    location.entersChild target = true ∧ response = .runnable #[location]


theorem Redirect.grow {tree current target response before after}
    (redirect : Redirect tree current target response before) (growth : Grows before after) :
    Redirect tree current target response after := by
  obtain ⟨location, children, result, next, route, active, complete, enters, response⟩ := redirect
  exact ⟨location, children, result, next, route, active.grow growth, complete.grow growth, enters, response⟩

private theorem Redirect.delay {tree current target response state}
    (redirect : Redirect tree current target response state) : Redirect (.delay tree) current target response state := by
  obtain ⟨location, children, result, next, route, active, complete, response⟩ := redirect
  exact ⟨location, children, result, next, .delay route, active, complete, response⟩

private theorem Redirect.next {children result tree current target response state}
    (redirect : Redirect tree current.next target response state)
    (completed : CompletedAt (view state) current.key (encodeOutcome (inferInstance : Codec Json) result)) :
    Redirect (.fork children result (some tree)) current target response state := by
  obtain ⟨location, descendants, outcome, next, route, active, complete, response⟩ := redirect
  exact ⟨location, descendants, outcome, next, .next route, ⟨completed, active⟩, complete, response⟩

private theorem Redirect.child {children result next current target response state} (index : Fin children.length)
    (redirect : Redirect children[index.val] (current.child index.val) target response state)
    (opened : view state (forkKey current.key) = some (toJson children.length) ∨
      CompletedAt (view state) current.key (encodeOutcome (inferInstance : Codec Json) result)) :
    Redirect (.fork children result next) current target response state := by
  obtain ⟨location, descendants, outcome, later, route, active, complete, response⟩ := redirect
  exact ⟨location, descendants, outcome, later, .child index route, ⟨opened, active⟩, complete, response⟩

theorem ReadResult.not_missing {key before after result}
    (seen : ReadResult key before after result)
    (opened : (∃ count : Nat, view before (forkKey key) = some (toJson count)) ∨
      ∃ outcome, CompletedAt (view before) key outcome) : result ≠ none := by
  cases seen with
  | completed | suspended => simp
  | missing absent noFork =>
    rcases opened with ⟨count, stored⟩ | ⟨outcome, completed⟩
    · simp [noFork] at stored
    · cases completed with
      | cached stored => simp [absent] at stored
      | group slots fork _ _ => simp [noFork] at fork

private def redirected (program : Cloud Replay.M Json) (current : Location)
    (result : Except CloudError Json) : Action StepResult :=
  match program with
  | .impure (.parallel codec count _) _ =>
    match encodeOutcome (inferInstance : Codec Json) result with
    | .success value => do
        let _ ← decodeGroup codec count value
        pure (.runnable #[current])
    | _ => pure (.runnable #[current])
  | _ => pure (.runnable #[current])

/-- A completed ancestor decodes using its original branch codec before the
worker redirects an obsolete child delivery back to that ancestor. -/
private theorem redirect_code {program : Cloud Replay.M Json} {children result next} (current : Location)
    (expanded : Expansion program (.fork children result next)) (supported : PureProgram program) :
    redirected program current result = pure (.runnable #[current]) := by
  cases expanded with
  | @success α codec count branches continuation outcomes values trees next evaluated collected children rest =>
    have size := (collect_outcomes_size _ _ collected).trans evaluated.size
    change (do
      let _ ← decodeGroup (m := StateT Unit Replay.M) codec count (.arr (values.map codec.encode))
      pure (StepResult.runnable #[current])) = _
    rw [← size, decode_group codec supported.1.1, action_pure_bind]
  | failure => rfl

/-- The target handler is called with the original computation and continuation.
If another worker completes an ancestor meanwhile, the only alternative is a
durably justified redirect along the same original path. -/
theorem reconstruct_checked {top : ExecutionTree} {root : Cloud Replay.M Json}
    (whole : Expansion root top) {tree current target node}
    (route : TreeRoute tree current target node)
    (embedded : tree.nodes current ⊆ top.nodes Location.root)
    (blobs : BlobStorage Unit Replay.M) (post : StepResult → Backend.State → Prop)
    (before : Backend.State) (bound : Nat)
    (handle : ∀ program : Cloud Replay.M Json, PureProgram program → Expansion program node →
      ∀ state, Valid (top.journal Location.root) state → Grows before state →
      ∀ fuel, bound ≤ fuel → ActionChecked (top.journal Location.root)
        (walk workerDb blobs fuel program target target) post state)
    {program : Cloud Replay.M Json} (expanded : Expansion program tree) (supported : PureProgram program)
    (nonempty : 0 < current.size) (state : Backend.State) (bounded : Valid (top.journal Location.root) state)
    (prior : Grows before state) (active : route.Activated (view state)) :
    ∀ fuel, route.prefixSteps + bound ≤ fuel → ActionChecked (top.journal Location.root)
      (walk workerDb blobs fuel program current target)
      (fun response final => post response final ∨ Redirect tree current target response final) state := by
  have rootSize : 0 < Location.root.size := by simp [Location.root]
  induction route generalizing program state with
  | terminal | fork =>
    intro fuel enough
    exact (handle program supported expanded state bounded prior fuel (by simpa [TreeRoute.prefixSteps] using enough)).weaken
      (fun _ _ done => .inl done)
  | delay rest ih =>
    cases expanded with
    | delay expanded =>
      intro fuel enough
      cases fuel with
      | zero => simp [TreeRoute.prefixSteps] at enough
      | succ fuel =>
        exact (ih (by simpa only [ExecutionTree.nodes] using embedded) handle expanded (supported.2.apply ())
          nonempty state bounded prior active fuel (by simp only [TreeRoute.prefixSteps] at enough; omega)).weaken
          (fun _ _ result => result.imp_right Redirect.delay)
  | @next children result tree current target node rest ih =>
    cases expanded with
    | @success α codec count branches continuation outcomes values trees next evaluated collected childrenExpansion expanded =>
      have member : (current, ExecutionTree.fork children (.ok (.arr (values.map codec.encode))) (some tree)) ∈
          top.nodes Location.root := embedded (by simp [ExecutionTree.nodes])
      have included : tree.nodes current.next ⊆ top.nodes Location.root :=
        fun _ h => embedded (by simp [ExecutionTree.nodes, h])
      have different := rest.next_ne nonempty
      have size : values.size = count := (collect_outcomes_size _ _ collected).trans evaluated.size
      intro fuel enough
      cases fuel with
      | zero => simp [TreeRoute.prefixSteps] at enough
      | succ fuel =>
        rw [walk]
        apply ActionChecked.bind (load_checked _ current (top.readable _ rootSize _) (whole.coherent rootSize member) state bounded) bounded
        intro answer observed valid growth seen
        have admitted := seen.admitted whole rootSize member valid
        have ready := active.1
        simp only [beq_eq_false_iff_ne.mpr different, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        cases seen with
        | missing absent noFork =>
          cases ready with
          | cached stored => simp [absent] at stored
          | group slots fork _ _ => simp [noFork] at fork
        | suspended slots published incomplete settled => exact False.elim (incomplete _ ready)
        | completed outcome recorded =>
          have same := admitted (.completed outcome) rfl
          change outcome = .success (.arr (values.map codec.encode)) at same
          subst outcome
          simp only [← size, decode_group codec supported.1.1, action_pure_bind, rest.next_not_child nonempty]
          have remaining := ih included handle expanded (supported.2.apply values) (by simpa using nonempty)
            observed valid (prior.trans growth) (active.2.grow growth) fuel
            (by simp only [TreeRoute.prefixSteps] at enough; omega)
          exact remaining.remember.weaken fun _ _ h => h.2.imp_right
            (fun redirect => redirect.next (recorded.grow h.1))
  | @child children result next current target node index rest ih =>
    have member : (current, ExecutionTree.fork children result next) ∈ top.nodes Location.root := by
      apply embedded
      unfold ExecutionTree.nodes
      exact List.mem_cons_self
    have included := (ExecutionTree.child_nodes_subset children result next current index).trans embedded
    have redirecting := redirect_code current expanded supported
    cases expanded with
    | @success α codec count branches continuation outcomes values trees next evaluated collected childrenExpansion expanded
    | @failure α codec count branches continuation outcomes error trees evaluated collected childrenExpansion =>
      obtain ⟨enters, chosen⟩ := rest.child_path
      have different : current ≠ target := by
        intro same
        subst target
        simp [Location.entersChild] at enters
      let selected : Fin count := ⟨index.val, by rw [← childrenExpansion.size]; exact index.isLt⟩
      have inside : index.val < count := selected.isLt
      have branch := childrenExpansion.at selected index.isLt
      intro fuel enough
      cases fuel with
      | zero => simp [TreeRoute.prefixSteps] at enough
      | succ fuel =>
        rw [walk]
        apply ActionChecked.bind (load_checked _ current (top.readable _ rootSize _) (whole.coherent rootSize member) state bounded) bounded
        intro answer observed valid growth seen
        have admitted := seen.admitted whole rootSize member valid
        have present := seen.not_missing (active.1.imp (fun h => ⟨_, h⟩) (fun h => ⟨_, h⟩))
        simp only [beq_eq_false_iff_ne.mpr different, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        cases seen with
        | missing absent noFork => exact False.elim (present rfl)
        | completed outcome recorded =>
          have same := admitted (.completed outcome) rfl
          change outcome = _ at same
          rw [same] at recorded ⊢
          simp only [redirected, encodeOutcome] at redirecting
          simp only [enters, encodeOutcome, ↓reduceIte]
          try rw [redirecting]
          apply action_pure
          intro final finalValid later
          exact .inr ⟨current, children, _, _, .fork _ _ _ current, trivial, recorded.grow later, enters, rfl⟩
        | suspended slots published incomplete settled =>
          have allowed := admitted (.suspended slots) rfl
          have size : slots.size = count := allowed.1.trans childrenExpansion.size
          simp only [size, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, enters, Bool.not_true,
            chosen, inside, ↓reduceDIte]
          have remaining := ih included handle branch ((supported.1.2 selected).map codec.encode) (by simp)
            observed valid (prior.trans growth) (active.2.grow growth) fuel
            (by simp only [TreeRoute.prefixSteps] at enough; omega)
          apply remaining.remember.weaken
          intro response final h
          rcases h.2 with done | redirect
          · exact .inl done
          · exact .inr (redirect.child index (active.1.elim
              (fun descriptor => .inl ((growth.trans h.1) _ _ descriptor))
              (fun completed => .inr (completed.grow (growth.trans h.1)))))

/-- A redirect preserves the full program's durable routing prerequisites. -/
theorem Redirect.emits {tree target response state}
    (redirect : Redirect tree Location.root target response state) :
    tree.EmitsActivated (view state) response := by
  obtain ⟨location, children, result, next, route, active, _, _, rfl⟩ := redirect
  exact ExecutionTree.EmitsActivated.singleton ⟨_, route, active⟩

end LeanCloud.Backend.Proofs.Journal

