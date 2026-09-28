import LeanCloud.Proofs.FairDriver

/-! Primitive queue laws suffice: interpreter invariants and finite work are
proved internally, rather than imposed on the queue implementation. -/
namespace LeanCloud.Proofs
open Lean ReplayModel ReplayInterpreter.Internal

/-- Polling selects pending work or reports a recorded completion. Acknowledging
an item applies exactly the response published by the interpreter. -/
structure QueueContract (queue : LeanCloud.WorkQueue State Id) : Prop where
  poll : ∀ state, ∃ response,
    queue.next state = (response, state) ∧
    match response with
    | .idle => True
    | .completed exit => state.completed = some exit
    | .item target => state.completed = none ∧ target ∈ state.pending
  acknowledge : ∀ state target response,
    queue.complete target response state = ((), update state target response)

theorem RootSnapshot.round {queue : LeanCloud.WorkQueue State Id}
    {root : Cloud Id Json} {state response nextState}
    (snapshot : RootSnapshot root state) (supported : PureProgram root)
    (round : DriverRound queue root state response nextState) : RootSnapshot root nextState := by
  cases round with
  | idle _ => exact snapshot
  | completed _ _ => exact snapshot
  | item selected _ stepped _ => exact snapshot.worker_step supported (.process _ _ _ _ _ _ selected stepped)

/-- Every selected pending location can be processed with finite fuel. -/
theorem QueueContract.round_exists {queue : LeanCloud.WorkQueue State Id}
    {root : Cloud Id Json} {state}
    (contract : QueueContract queue) (snapshot : RootSnapshot root state) (supported : PureProgram root) :
    ∃ response nextState, DriverRound queue root state response nextState := by
  obtain ⟨response, polled, valid⟩ := contract.poll state
  cases response with
  | idle => exact ⟨.idle, state, .idle polled⟩
  | completed exit => exact ⟨.completed exit, state, .completed valid polled⟩
  | item target =>
    rcases state with ⟨journal, pending, completed⟩
    obtain ⟨unfinished, selected⟩ := valid
    dsimp only at unfinished selected
    subst completed
    obtain ⟨status, structural, source, queued, _⟩ := snapshot
    obtain ⟨updated, _, _, response, bound, _, _, _, _, executed⟩ :=
      source.step_preserves supported (queued.mem_iff.mpr selected)
    exact ⟨.item target, _, .item selected polled (fun fuel => executed fuel pending)
      (contract.acknowledge _ target response)⟩

/-- Construct observations of the supplied primitives, starting from an empty
Db and the root work item. No completed run is assumed. -/
theorem QueueContract.trace_exists {queue : LeanCloud.WorkQueue State Id}
    {root : Cloud Id Json} (contract : QueueContract queue) (supported : PureProgram root) :
    ∃ trace : DriverTrace queue root, trace.states 0 = initial := by
  classical
  let Live := {state : State // RootSnapshot root state}
  have advance (live : Live) :
      ∃ response, ∃ next : Live, DriverRound queue root live.val response next.val := by
    obtain ⟨response, state, round⟩ := contract.round_exists live.property supported
    exact ⟨response, ⟨state, live.property.round supported round⟩, round⟩
  let response (live : Live) := (advance live).choose
  let next (live : Live) := (advance live).choose_spec.choose
  have observation (live : Live) : DriverRound queue root live.val (response live) (next live).val :=
    (advance live).choose_spec.choose_spec
  let start : Live := ⟨initial, .initial root⟩
  let sequence : Nat → Live := fun n => Nat.rec start (fun _ live => next live) n
  exact ⟨⟨fun n => (sequence n).val, fun n => response (sequence n), fun n => observation (sequence n)⟩, rfl⟩

/-- A pure workflow has the same value or CloudError under direct evaluation
and replay with a lawful fair queue. The fuel bound may depend on the schedule.
Only the interpreter's Db and pending locations occur in the model. -/
theorem same_output [codec : Codec α]
    (queue : LeanCloud.WorkQueue State Id) (program : ι → Cloud Id α) (input : ι)
    (law : CodecLaw codec) (supported : PureProgram (program input))
    (contract : QueueContract queue)
    (fair : ∀ trace : DriverTrace queue (codec.encode <$> program input),
      trace.states 0 = initial → WorkQueue.Fair trace.queueTrace) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      ((LeanCloud.interpret db noBlobs queue fuel program input).run initial).1 = direct (program input) := by
  obtain ⟨trace, start⟩ := contract.trace_exists (supported.map codec.encode)
  exact fair_queue_same_output queue program input law supported trace start (fair trace start)

end LeanCloud.Proofs
