import LeanCloud.Proofs.DirectState
import LeanCloud.Proofs.Assumptions

/-! Finite evaluation derivations for the supported language. The natural index
counts executed control requests and child completions; it is an induction
measure, not the replay fuel budget. These are propositions about execution,
not another executable interpreter. -/

namespace LeanCloud.Proofs
open LeanEff DirectInterpreter.Internal

mutual
  inductive Evaluation {World : Type} (blobs : BlobModel World) :
      {α : Type} → Cloud (StateM World) α → World → Except CloudError α → World → Nat → Prop where
    | pure {α : Type} (value : α) (world : World) :
        Evaluation blobs (.pure value) world (.ok value) world 0
    | success {α β : Type} {request : Control (StateM World) β}
        {continuation : ArrsF (Control (StateM World)) β α}
        {world middle finalWorld value outcome controlWork continuationWork}
        (control : ControlEvaluation blobs request world (.ok value) middle controlWork)
        (rest : ContinuationEvaluation blobs continuation value middle outcome finalWorld continuationWork) :
        Evaluation blobs (.impure request continuation) world outcome finalWorld (controlWork + continuationWork)
    | failure {α β : Type} {request : Control (StateM World) β}
        (continuation : ArrsF (Control (StateM World)) β α) {world finalWorld error work}
        (control : ControlEvaluation blobs request world (.error error) finalWorld work) :
        Evaluation blobs (.impure request continuation) world (.error error) finalWorld work

  inductive ControlEvaluation {World : Type} (blobs : BlobModel World) :
      {α : Type} → Control (StateM World) α → World → Except CloudError α → World → Nat → Prop where
    | delay (world : World) : ControlEvaluation blobs .delay world (.ok ()) world 1
    | fail {α : Type} (world : World) (error : CloudError) :
        ControlEvaluation blobs (Control.fail (α := α) error) world (.error error) world 1
    | sequential {α : Type} {codec : Codec α} {operation : Operation (StateM World) α}
        {world finalWorld outcome} (law : CodecLaw codec)
        (executed : ((modelStorage blobs).execute operation).run Journal.empty world =
          ((outcome, Journal.empty), finalWorld)) :
        ControlEvaluation blobs (.sequential codec operation) world outcome finalWorld 1
    | parallel {α : Type} {codec : Codec α} {count : Nat}
        {branches : Fin count → Cloud (StateM World) α} {world finalWorld outcomes work}
        (law : CodecLaw codec)
        (children : ChildrenEvaluation blobs branches world outcomes finalWorld work) :
        ControlEvaluation blobs (.parallel codec count branches) world (outcomes.mapM id) finalWorld (work + 1)

  inductive ContinuationEvaluation {World : Type} (blobs : BlobModel World) :
      {α β : Type} → ArrsF (Control (StateM World)) α β → α →
      World → Except CloudError β → World → Nat → Prop where
    | one {α β : Type} {k : α → Cloud (StateM World) β} {value world outcome finalWorld work}
        (program : Evaluation blobs (k value) world outcome finalWorld work) :
        ContinuationEvaluation blobs (.one k) value world outcome finalWorld work
    | success {α β γ : Type} {first : ArrsF (Control (StateM World)) α β}
        {rest : ArrsF (Control (StateM World)) β γ} {value next world middle finalWorld outcome firstWork restWork}
        (head : ContinuationEvaluation blobs first value world (.ok next) middle firstWork)
        (tail : ContinuationEvaluation blobs rest next middle outcome finalWorld restWork) :
        ContinuationEvaluation blobs (.append first rest) value world outcome finalWorld (firstWork + restWork)
    | failure {α β γ : Type} {first : ArrsF (Control (StateM World)) α β}
        (rest : ArrsF (Control (StateM World)) β γ) {value world finalWorld error work}
        (head : ContinuationEvaluation blobs first value world (.error error) finalWorld work) :
        ContinuationEvaluation blobs (.append first rest) value world (.error error) finalWorld work

  inductive ChildrenEvaluation {World : Type} (blobs : BlobModel World) :
      {α : Type} → {count : Nat} → (Fin count → Cloud (StateM World) α) →
      World → Array (Except CloudError α) → World → Nat → Prop where
    | empty {α : Type} (branches : Fin 0 → Cloud (StateM World) α) (world : World) :
        ChildrenEvaluation blobs branches world #[] world 0
    | cons {α : Type} {count : Nat} {branches : Fin (count + 1) → Cloud (StateM World) α}
        {world middle finalWorld outcome outcomes headWork tailWork}
        (head : Evaluation blobs (branches 0) world outcome middle headWork)
        (tail : ChildrenEvaluation blobs (fun index => branches index.succ) middle outcomes finalWorld tailWork) :
        ChildrenEvaluation blobs branches world (#[outcome] ++ outcomes) finalWorld (headWork + 1 + tailWork)
end

mutual
  theorem Evaluation.sound {World α : Type} {blobs : BlobModel World} {program : Cloud (StateM World) α}
      {world finalWorld : World} {outcome : Except CloudError α} {work : Nat}
      (execution : Evaluation blobs program world outcome finalWorld work) :
      (eval (modelStorage blobs) program).run Journal.empty world = ((outcome, Journal.empty), finalWorld) := by
    match execution with
    | .pure value world => rfl
    | .success control rest =>
      rw [eval, run_bind_state, control.sound]
      exact rest.sound
    | .failure continuation control =>
      rw [eval, run_bind_state, control.sound]
  termination_by structural execution

  theorem ControlEvaluation.sound {World α : Type} {blobs : BlobModel World} {request : Control (StateM World) α}
      {world finalWorld : World} {outcome : Except CloudError α} {work : Nat}
      (execution : ControlEvaluation blobs request world outcome finalWorld work) :
      (evalControl (modelStorage blobs) request).run Journal.empty world = ((outcome, Journal.empty), finalWorld) := by
    match execution with
    | .delay world => rfl
    | .fail world error => rfl
    | .sequential law executed => exact executed
    | @ControlEvaluation.parallel _ _ _ codec count branches _ _ _ _ law children =>
      rw [direct_parallel_run]
      change (let ((outcomes, journal), world) :=
        (Array.ofFnM (m := StateT Journal (StateM World)) fun index =>
          (eval (modelStorage blobs) (branches index)).run) Journal.empty world
        ((outcomes.mapM id, journal), world)) = _
      rw [children.sound]
  termination_by structural execution

  theorem ContinuationEvaluation.sound {World α β : Type} {blobs : BlobModel World}
      {continuation : ArrsF (Control (StateM World)) α β} {value : α}
      {world finalWorld : World} {outcome : Except CloudError β} {work : Nat}
      (execution : ContinuationEvaluation blobs continuation value world outcome finalWorld work) :
      (evalContinuation (modelStorage blobs) continuation value).run Journal.empty world =
        ((outcome, Journal.empty), finalWorld) := by
    match execution with
    | .one program => exact program.sound
    | .success head tail =>
      rw [evalContinuation, run_bind_state, head.sound]
      exact tail.sound
    | .failure rest head => rw [evalContinuation, run_bind_state, head.sound]
  termination_by structural execution

  theorem ChildrenEvaluation.sound {World α : Type} {blobs : BlobModel World} {count : Nat}
      {branches : Fin count → Cloud (StateM World) α} {world finalWorld : World}
      {outcomes : Array (Except CloudError α)} {work : Nat}
      (execution : ChildrenEvaluation blobs branches world outcomes finalWorld work) :
      (Array.ofFnM (m := StateT Journal (StateM World)) fun index =>
        (eval (modelStorage blobs) (branches index)).run) Journal.empty world =
        ((outcomes, Journal.empty), finalWorld) := by
    match execution with
    | .empty branches world => rw [Array.ofFnM_zero]; rfl
    | .cons head tail =>
      rw [Array.ofFnM_succ']
      simp only [bind, StateT.bind, pure, StateT.pure]
      rw [head.sound]
      dsimp only
      rw [tail.sound]
  termination_by structural execution
end

/-- Finite array traversal combines one finite derivation for each child. -/
theorem ChildrenEvaluation.exists_of_children {World α : Type} (blobs : BlobModel World) {count : Nat}
    (branches : Fin count → Cloud (StateM World) α)
    (children : ∀ index world, ∃ outcome finalWorld work, Evaluation blobs (branches index) world outcome finalWorld work)
    (world : World) :
    ∃ outcomes finalWorld work, ChildrenEvaluation blobs branches world outcomes finalWorld work := by
  induction count generalizing world with
  | zero => exact ⟨#[], world, 0, .empty branches world⟩
  | succ count ih =>
    obtain ⟨outcome, middle, headWork, head⟩ := children 0 world
    obtain ⟨outcomes, finalWorld, tailWork, tail⟩ :=
      ih (fun index => branches index.succ) (fun index => children index.succ) middle
    exact ⟨_, _, _, .cons head tail⟩

mutual
  theorem Evaluation.exists {World α : Type} (blobs : BlobModel World) (program : Cloud (StateM World) α)
      (supported : Supported program) (world : World) :
      ∃ outcome finalWorld work, Evaluation blobs program world outcome finalWorld work := by
    match program with
    | .pure value => exact ⟨.ok value, world, 0, .pure value world⟩
    | .impure request continuation =>
      obtain ⟨outcome, middle, controlWork, control⟩ := ControlEvaluation.exists blobs request supported.1 world
      cases outcome with
      | error error => exact ⟨.error error, middle, controlWork, .failure continuation control⟩
      | ok value =>
        obtain ⟨outcome, finalWorld, restWork, rest⟩ :=
          ContinuationEvaluation.exists blobs continuation supported.2 value middle
        exact ⟨outcome, finalWorld, controlWork + restWork, .success control rest⟩
  termination_by structural program

  theorem ControlEvaluation.exists {World α : Type} (blobs : BlobModel World) (request : Control (StateM World) α)
      (supported : SupportedControl request) (world : World) :
      ∃ outcome finalWorld work, ControlEvaluation blobs request world outcome finalWorld work := by
    match request with
    | .delay => exact ⟨.ok (), world, 1, .delay world⟩
    | .fail error => exact ⟨.error error, world, 1, .fail world error⟩
    | .sequential codec operation =>
      have preserved := modelStorage_execute blobs operation Journal.empty world
      cases executed : ((modelStorage blobs).execute operation).run Journal.empty world with
      | mk pair finalWorld => cases pair with
        | mk outcome journal =>
          rw [executed] at preserved
          have equal : journal = Journal.empty := congrArg (fun result => result.1.2) preserved
          subst journal
          exact ⟨outcome, finalWorld, 1, .sequential supported executed⟩
    | .parallel codec count branches =>
      obtain ⟨outcomes, finalWorld, work, children⟩ := ChildrenEvaluation.exists_of_children blobs branches
        (fun index world => Evaluation.exists blobs (branches index) (supported.2 index) world) world
      exact ⟨outcomes.mapM id, finalWorld, work + 1, .parallel supported.1 children⟩
    | .choice .. => exact False.elim supported
  termination_by structural request

  theorem ContinuationEvaluation.exists {World α β : Type} (blobs : BlobModel World)
      (continuation : ArrsF (Control (StateM World)) α β)
      (supported : SupportedContinuation continuation) (value : α) (world : World) :
      ∃ outcome finalWorld work, ContinuationEvaluation blobs continuation value world outcome finalWorld work := by
    match continuation with
    | .one k =>
      obtain ⟨outcome, finalWorld, work, program⟩ := Evaluation.exists blobs (k value) (supported value) world
      exact ⟨outcome, finalWorld, work, .one program⟩
    | .append first rest =>
      obtain ⟨outcome, middle, firstWork, head⟩ := ContinuationEvaluation.exists blobs first supported.1 value world
      cases outcome with
      | error error => exact ⟨.error error, middle, firstWork, .failure rest head⟩
      | ok next =>
        obtain ⟨outcome, finalWorld, restWork, tail⟩ := ContinuationEvaluation.exists blobs rest supported.2 next middle
        exact ⟨outcome, finalWorld, firstWork + restWork, .success head tail⟩
  termination_by structural continuation
end

theorem ControlEvaluation.positive {World α : Type} {blobs : BlobModel World}
    {request : Control (StateM World) α} {world finalWorld : World} {outcome : Except CloudError α} {work : Nat}
    (execution : ControlEvaluation blobs request world outcome finalWorld work) : 0 < work := by
  cases execution <;> omega

theorem Evaluation.bind_success {World α β : Type} {blobs : BlobModel World}
    {program : Cloud (StateM World) α} {next : α → Cloud (StateM World) β}
    {world middle finalWorld : World} {value : α} {outcome : Except CloudError β} {firstWork nextWork : Nat}
    (first : Evaluation blobs program world (.ok value) middle firstWork)
    (rest : Evaluation blobs (next value) middle outcome finalWorld nextWork) :
    Evaluation blobs (EffF.bind program next) world outcome finalWorld (firstWork + nextWork) := by
  cases first with
  | pure value world => simpa [EffF.bind] using rest
  | success control continuation =>
    simpa only [EffF.bind, Nat.add_assoc] using
      Evaluation.success control (ContinuationEvaluation.success continuation (.one rest))

theorem Evaluation.bind_failure {World α β : Type} {blobs : BlobModel World}
    {program : Cloud (StateM World) α} {world finalWorld : World} {error : CloudError} {work : Nat}
    (first : Evaluation blobs program world (.error error) finalWorld work)
    (next : α → Cloud (StateM World) β) :
    Evaluation blobs (EffF.bind program next) world (.error error) finalWorld work := by
  cases first with
  | success control continuation =>
    exact .success control (.failure (.one next) continuation)
  | failure continuation control => exact .failure (.append continuation (.one next)) control

theorem Evaluation.map {World α β : Type} {blobs : BlobModel World}
    {program : Cloud (StateM World) α} {world finalWorld : World} {outcome : Except CloudError α} {work : Nat}
    (execution : Evaluation blobs program world outcome finalWorld work) (f : α → β) :
    Evaluation blobs (f <$> program) world (outcome.map f) finalWorld work := by
  cases outcome with
  | error error => exact execution.bind_failure (fun value => .pure (f value))
  | ok value =>
    change Evaluation blobs (EffF.bind program (fun value => .pure (f value))) world (.ok (f value)) finalWorld work
    simpa only [Nat.add_zero] using
      execution.bind_success (next := fun value => .pure (f value)) (Evaluation.pure (f value) finalWorld)

private theorem ContinuationEvaluation.reassociate {World α β γ δ : Type} {blobs : BlobModel World}
    {first : ArrsF (Control (StateM World)) α β} {second : ArrsF (Control (StateM World)) β γ}
    {rest : ArrsF (Control (StateM World)) γ δ} {value : α} {world finalWorld : World}
    {outcome : Except CloudError δ} {work : Nat}
    (execution : ContinuationEvaluation blobs (.append (.append first second) rest) value world outcome finalWorld work) :
    ContinuationEvaluation blobs (.append first (.append second rest)) value world outcome finalWorld work := by
  cases execution with
  | success head tail =>
    cases head with
    | success first second =>
      simpa only [Nat.add_assoc] using ContinuationEvaluation.success first (.success second tail)
  | failure _ head =>
    cases head with
    | success first second => exact .success first (.failure rest second)
    | failure _ first => exact .failure _ first

private theorem ContinuationEvaluation.viewLAppend {World α β γ : Type} {blobs : BlobModel World}
    (first : ArrsF (Control (StateM World)) α β) (rest : ArrsF (Control (StateM World)) β γ)
    (value : α) {world finalWorld : World} {outcome : Except CloudError γ} {work : Nat}
    (execution : ContinuationEvaluation blobs (.append first rest) value world outcome finalWorld work) :
    match ArrsF.viewLAppend first rest with
    | .one k => Evaluation blobs (k value) world outcome finalWorld work
    | .cons k remaining =>
      ContinuationEvaluation blobs (.append (.one k) remaining) value world outcome finalWorld work := by
  match first with
  | .one k => exact execution
  | .append first second =>
    exact ContinuationEvaluation.viewLAppend first (.append second rest) value execution.reassociate
termination_by sizeOf first

private theorem ContinuationEvaluation.viewL {World α β : Type} {blobs : BlobModel World}
    {continuation : ArrsF (Control (StateM World)) α β} {value : α} {world finalWorld : World}
    {outcome : Except CloudError β} {work : Nat}
    (execution : ContinuationEvaluation blobs continuation value world outcome finalWorld work) :
    match ArrsF.viewL continuation with
    | .one k => Evaluation blobs (k value) world outcome finalWorld work
    | .cons k remaining =>
      ContinuationEvaluation blobs (.append (.one k) remaining) value world outcome finalWorld work := by
  cases continuation with
  | one k => cases execution with | one program => exact program
  | append first rest => exact ContinuationEvaluation.viewLAppend first rest value execution

/-- Rebuilding the continuation queue retains both the finite derivation and its
work measure. This connects the direct evaluator's structural queues to replay's
use of `ArrsF.apply`. -/
theorem ContinuationEvaluation.apply {World α β : Type} {blobs : BlobModel World}
    {continuation : ArrsF (Control (StateM World)) α β} {value : α} {world finalWorld : World}
    {outcome : Except CloudError β} {work : Nat}
    (execution : ContinuationEvaluation blobs continuation value world outcome finalWorld work) :
    Evaluation blobs (ArrsF.apply continuation value) world outcome finalWorld work := by
  have traced := execution.viewL
  rw [ArrsF.apply]
  cases view : ArrsF.viewL continuation with
  | one k => simpa only [view] using traced
  | cons k rest =>
    simp only [view] at traced
    cases traced with
    | success head tail =>
      cases head with
      | one program => exact program.bind_success tail.apply
    | failure _ head =>
      cases head with
      | one program => exact program.bind_failure _
termination_by sizeOf continuation
decreasing_by simpa [view] using ArrsF.viewL_rest_lt continuation

end LeanCloud.Proofs
