import LeanCloud.Proofs.ScheduledWork
import LeanCloud.Proofs.ScheduledDriver
import LeanCloud.Proofs.FairProgress

/-! Infinite observations of actual queue polls and worker calls. Fairness is
the only liveness assumption: finite processing work is derived from the program.
A round includes one poll, any selected worker call, and its acknowledgement. -/

namespace LeanCloud.Proofs
open Lean ReplayModel ReplayInterpreter.Internal

inductive DriverRound (queue : LeanCloud.WorkQueue State Id)
    (root : Cloud Id Json) : State → Work → State → Prop where
  | idle {state}
      (polled : queue.next state = ((Work.idle, state))) :
      DriverRound queue root state .idle state
  | completed {state exit}
      (recorded : state.completed = some exit)
      (polled : queue.next state = ((Work.completed exit, state))) :
      DriverRound queue root state (.completed exit) state
  | item {journal updated pending target response bound}
      (selected : target ∈ pending)
      (polled : queue.next ⟨journal, pending, none⟩ = ((Work.item target, ⟨journal, pending, none⟩)))
      (stepped : ∀ fuel,
        (step db noBlobs (fuel + bound) root target).run ⟨journal, pending, none⟩ =
          ((.ok response, ⟨updated, pending, none⟩)))
      (published : queue.complete target response ⟨updated, pending, none⟩ =
        (((), update ⟨updated, pending, none⟩ target response))) :
      DriverRound queue root ⟨journal, pending, none⟩ (.item target)
        (update ⟨updated, pending, none⟩ target response)

structure DriverTrace (queue : LeanCloud.WorkQueue State Id)
    (root : Cloud Id Json) where
  states : Nat → State
  responses : Nat → Work
  rounds : ∀ n, DriverRound queue root (states n) (responses n) (states (n + 1))

def selectedWork : Work → Nat
  | .item _ => 1
  | _ => 0

def DriverTrace.processed {queue : LeanCloud.WorkQueue State Id}
    {root : Cloud Id Json} (trace : DriverTrace queue root) : Nat → Nat
  | 0 => 0
  | n + 1 => trace.processed n + selectedWork (trace.responses n)

def DriverTrace.queueTrace {queue : LeanCloud.WorkQueue State Id}
    {root : Cloud Id Json} (trace : DriverTrace queue root) : WorkQueue.Trace :=
  ⟨fun n target => target ∈ (trace.states n).pending, trace.responses⟩

theorem RootWorkSnapshot.round {queue : LeanCloud.WorkQueue State Id}
    {root : Cloud Id Json} {state spent response nextState}
    (snapshot : RootWorkSnapshot root state spent) (supported : PureProgram root)
    (round : DriverRound queue root state response nextState) :
    RootWorkSnapshot root nextState (spent + selectedWork response) := by
  cases round with
  | idle _ => exact snapshot
  | completed _ _ => exact snapshot
  | item selected _ stepped _ => exact snapshot.worker_step supported (.process _ _ _ _ _ _ selected stepped)

theorem DriverTrace.snapshots {queue : LeanCloud.WorkQueue State Id}
    {root : Cloud Id Json} (trace : DriverTrace queue root) (initial : trace.states 0 = ⟨Journal.empty, [Location.root], none⟩)
    (supported : PureProgram root) (n : Nat) :
    RootWorkSnapshot root (trace.states n) (trace.processed n) := by
  induction n with
  | zero => simpa only [processed, initial] using RootWorkSnapshot.initial root
  | succ n ih => exact ih.round supported (trace.rounds n)

theorem RootSnapshot.completed_empty {root : Cloud Id Json}
    {state exit}
    (snapshot : RootSnapshot root state) (completed : state.completed = some exit) :
    state.pending = [] := by
  obtain ⟨status, pending, source, queued, recorded⟩ := snapshot
  rw [completed] at recorded
  cases status with
  | none => cases recorded
  | some value =>
    have empty := source.pending_empty
    have same : pending = [] := by simpa using empty
    rw [same] at queued
    exact queued.symm.eq_nil

theorem DriverRound.queue_safety {queue : LeanCloud.WorkQueue State Id}
    {root : Cloud Id Json} {state response nextState}
    (round : DriverRound queue root state response nextState)
    (snapshot : RootSnapshot root state) (supported : PureProgram root) :
    (∀ target, response = .item target → target ∈ state.pending) ∧
    (∀ target, target ∈ state.pending → response ≠ .item target → target ∈ nextState.pending) ∧
    (∀ exit, response = .completed exit → state.pending = []) := by
  cases round with
  | idle _ =>
    refine ⟨?_, ?_, ?_⟩
    · intro _ h; cases h
    · intro _ h _; exact h
    · intro _ h; cases h
  | completed recorded _ =>
    refine ⟨?_, ?_, ?_⟩
    · intro _ h; cases h
    · intro _ h _; exact h
    · intro exit h; cases h; exact snapshot.completed_empty recorded
  | @item journal updated pending target response bound selected polled stepped published =>
    refine ⟨by intro other h; cases h; exact selected, ?_, by intro _ h; cases h⟩
    intro other member different
    exact snapshot.retains_unselected supported selected stepped member (by intro same; subst other; exact different rfl)

theorem DriverTrace.queue_laws {queue : LeanCloud.WorkQueue State Id}
    {root : Cloud Id Json} (trace : DriverTrace queue root) (initial : trace.states 0 = ⟨Journal.empty, [Location.root], none⟩)
    (supported : PureProgram root)
    (fair : WorkQueue.Fair trace.queueTrace) : WorkQueue.Laws trace.queueTrace := by
  have safety n := (trace.rounds n).queue_safety (trace.snapshots initial supported n).forget supported
  refine ⟨?_, ?_, ?_, fair⟩
  · intro n target selected
    apply (safety n).1 target
    cases response : trace.responses n <;> simp [queueTrace, WorkQueue.Trace.selected, response] at selected ⊢
    exact selected
  · intro n target pending different
    apply (safety n).2.1 target pending
    intro same
    exact different (by simp [queueTrace, WorkQueue.Trace.selected, same])
  · intro n exit completed target member
    have empty := (safety n).2.2 exit completed
    change target ∈ (trace.states n).pending at member
    rw [empty] at member
    cases member

def remainingWork (bound spent : Nat) (completed : Option Exit) : Nat :=
  match completed with
  | some _ => 0
  | none => bound - spent

theorem DriverRound.progress {queue : LeanCloud.WorkQueue State Id}
    {root : Cloud Id Json} {state response nextState bound spent}
    (round : DriverRound queue root state response nextState)
    (bounded : spent + unfinishedWork state.completed ≤ bound) :
    remainingWork bound (spent + selectedWork response) nextState.completed ≤ remainingWork bound spent state.completed ∧
    (∀ target, response = .item target →
      remainingWork bound (spent + selectedWork response) nextState.completed < remainingWork bound spent state.completed) := by
  cases round with
  | idle _ => exact ⟨Nat.le_refl _, by intro _ h; cases h⟩
  | completed _ _ => exact ⟨Nat.le_refl _, by intro _ h; cases h⟩
  | @item journal updated pending target response fuel selected polled stepped published =>
    cases response <;> simp only [remainingWork, selectedWork, update, unfinishedWork] at bounded ⊢ <;>
      exact ⟨by omega, by intro _ _; omega⟩

/-- A ranking function for the actual interpreter, derived from one finite
direct derivation. It is not a backend assumption. -/
def DriverTrace.progress {queue : LeanCloud.WorkQueue State Id}
    {root : Cloud Id Json} (trace : DriverTrace queue root) (initial : trace.states 0 = ⟨Journal.empty, [Location.root], none⟩)
    (supported : PureProgram root)
    {outcome work} {evaluation : Evaluation root outcome} (canonical : ProgramWork 0 evaluation work) :
    WorkQueue.Progress trace.queueTrace := by
  let bound := work + returnWork outcome
  have snapshots := trace.snapshots initial supported
  have bounded n := (snapshots n).bounded canonical supported
  have advances n := (trace.rounds n).progress (bounded n)
  refine ⟨fun n => remainingWork bound (trace.processed n) (trace.states n).completed, ?_, ?_, ?_⟩
  · intro n target selected
    apply (advances n).2 target
    cases response : trace.responses n <;> simp [queueTrace, WorkQueue.Trace.selected, response] at selected ⊢
    exact selected
  · intro n
    exact (advances n).1
  · intro n positive
    have unfinished : (trace.states n).completed = none := by
      cases result : (trace.states n).completed with
      | none => rfl
      | some value => simp [remainingWork, result] at positive
    exact (snapshots n).forget.unfinished_pending unfinished

/-- Every valid fair trace eventually records the root outcome. This needs no
assumption that there is already a finite completed execution. -/
theorem DriverTrace.eventually_completed {queue : LeanCloud.WorkQueue State Id}
    {root : Cloud Id Json} (trace : DriverTrace queue root) (initial : trace.states 0 = ⟨Journal.empty, [Location.root], none⟩)
    (supported : PureProgram root)
    (fair : WorkQueue.Fair trace.queueTrace) : ∃ n exit, (trace.states n).completed = some exit := by
  obtain ⟨outcome, evaluation⟩ := Evaluation.exists root supported
  obtain ⟨work, canonical⟩ := evaluation.work_exists
  let progress := trace.progress initial supported canonical
  obtain ⟨n, _, finished⟩ := WorkQueue.eventually_finished (trace.queue_laws initial supported fair) progress 0
  cases result : (trace.states n).completed with
  | some exit => exact ⟨n, exit, result⟩
  | none =>
    have bound := (trace.snapshots initial supported n).bounded canonical supported
    change remainingWork (work + returnWork outcome) (trace.processed n) (trace.states n).completed = 0 at finished
    simp only [result, remainingWork] at finished
    simp only [result, unfinishedWork] at bound
    omega

/-- A round either finishes immediately or can prepend itself to a later
completed execution. A completed root is never required to poll again. -/
theorem DriverRound.prepend {queue : LeanCloud.WorkQueue State Id}
    {root : Cloud Id Json} {state response nextState}
    (round : DriverRound queue root state response nextState)
    (unfinished : state.completed = none)
    (remaining : nextState.completed = none →
      ∃ exit finalState, DriverExecution queue root nextState exit finalState) :
    ∃ exit finalState, DriverExecution queue root state exit finalState := by
  cases round with
  | idle polled =>
    obtain ⟨exit, finalState, rest⟩ := remaining unfinished
    exact ⟨exit, finalState, .idle polled rest⟩
  | completed recorded _ => rw [unfinished] at recorded; cases recorded
  | @item journal updated pending target response bound selected polled stepped published =>
    cases response with
    | runnable locations =>
      obtain ⟨exit, finalState, rest⟩ := remaining rfl
      exact ⟨exit, finalState, .more selected polled stepped published rest⟩
    | done exit => exact ⟨exit, _, .finish selected polled stepped published⟩

theorem DriverTrace.finite_execution {queue : LeanCloud.WorkQueue State Id}
    {root : Cloud Id Json} (trace : DriverTrace queue root)
    (start length : Nat) (unfinished : (trace.states start).completed = none)
    {exit} (completed : (trace.states (start + length)).completed = some exit) :
    ∃ result finalState, DriverExecution queue root (trace.states start)
      result finalState := by
  induction length generalizing start with
  | zero => simp only [Nat.add_zero, unfinished] at completed; cases completed
  | succ length ih =>
    apply (trace.rounds start).prepend unfinished
    intro nextUnfinished
    exact ih (start + 1) nextUnfinished (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using completed)

/-- Fairness constructs a finite execution of the actual driver. -/
theorem DriverTrace.execution_exists {queue : LeanCloud.WorkQueue State Id}
    {root : Cloud Id Json} (trace : DriverTrace queue root) (initial : trace.states 0 = ⟨Journal.empty, [Location.root], none⟩)
    (supported : PureProgram root)
    (fair : WorkQueue.Fair trace.queueTrace) :
    ∃ exit finalState, DriverExecution queue root ⟨Journal.empty, [Location.root], none⟩
       exit finalState := by
  obtain ⟨n, exit, completed⟩ := trace.eventually_completed initial supported fair
  have executed := trace.finite_execution 0 n (by rw [initial]) (by simpa using completed)
  simpa only [initial] using executed

/-- Fairness supplies a sufficient fuel budget for the public interpreter. -/
theorem fair_queue_same_output [codec : Codec α]
    (queue : LeanCloud.WorkQueue State Id) (program : ι → Cloud Id α)
    (input : ι) (law : CodecLaw codec) (supported : PureProgram (program input))
    (trace : DriverTrace queue (codec.encode <$> program input))
    (initial : trace.states 0 = ReplayModel.initial) (fair : WorkQueue.Fair trace.queueTrace) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      ((LeanCloud.interpret db noBlobs queue fuel program input).run ReplayModel.initial).1 = direct (program input) := by
  obtain ⟨exit, finalState, execution⟩ := trace.execution_exists initial (supported.map codec.encode) fair
  exact arbitrary_queue_same_output queue program input law supported execution

end LeanCloud.Proofs
