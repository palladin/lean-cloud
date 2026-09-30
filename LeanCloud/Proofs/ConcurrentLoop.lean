import LeanCloud.Proofs.ConcurrentWorker
import LeanCloud.Proofs.SimulationLiveness
import LeanCloud.Proofs.SimulationPrefix

/-! Safety of the actual queue-driven interpreter, including finite fuel.
Insufficient fuel can stop a worker, but cannot change the workflow's meaning
or corrupt the shared journal/queue invariant. -/

namespace LeanCloud.Proofs.ConcurrentQueue
open Lean LeanEff Simulation SimulationBackend ReplayRecovery

def exhausted : CloudError := ⟨.protocol, "Interpreter fuel exhausted"⟩

private def truncation (db : Db σ (SimM δ)) : ReplayRelation db db where
  relates := Truncates exhausted
  pure _ := Truncates.refl _ _
  throw _ := Truncates.refl _ _
  bind := Truncates.bind
  get _ := Truncates.refl _ _
  put _ _ := Truncates.refl _ _

theorem step_truncates (db : Db σ (SimM δ)) (blobs : BlobStorage σ (SimM δ))
    (program : Cloud (SimM δ) Json) (supported : PureProgram program) (location : Location) (fuel extra : Nat) :
    Truncates exhausted (ReplayInterpreter.Internal.step db blobs fuel program location)
      (ReplayInterpreter.Internal.step db blobs (fuel + extra) program location) :=
  (truncation db).step_add blobs blobs fuel extra (fun _ _ _ => Truncates.stop _ _) program supported location

/-- Increasing fuel preserves every primitive request and reply of the smaller
run until that run exhausts its budget. This covers both queue polling and
reconstruction, for any queue and Db implementation. -/
theorem run_truncates [Codec α] (db : Db σ (SimM δ)) (blobs : BlobStorage σ (SimM δ))
    (queue : WorkQueue σ (SimM δ)) (program : Cloud (SimM δ) Json)
    (supported : PureProgram program) (fuel extra : Nat) :
    Truncates exhausted
      (ReplayInterpreter.Internal.run (α := α) db blobs queue fuel program)
      (ReplayInterpreter.Internal.run db blobs queue (fuel + extra) program) := by
  induction fuel with
  | zero => exact Truncates.stop _ _
  | succ fuel ih =>
    simp only [Nat.succ_add, ReplayInterpreter.Internal.run]
    apply Truncates.bind (Truncates.refl _ _)
    intro work
    cases work with
    | completed outcome => exact Truncates.refl _ _
    | idle => exact ih
    | item location =>
      have steps := step_truncates db blobs program supported location (fuel + 1) extra
      rw [Nat.add_right_comm fuel 1 extra] at steps
      apply Truncates.bind steps
      intro response
      apply Truncates.bind (Truncates.refl _ _)
      intro _
      cases response with
      | done outcome => exact Truncates.refl _ _
      | runnable _ => exact ih

/-- Any legal finite schedule of the original interpreter attempts can be
replayed with larger per-worker budgets. It makes exactly the same durable
changes, and keeps all outputs except a smaller run's fuel-exhaustion result.
No queue fairness, successful completion, or crash bound is required. -/
theorem attempts_extend [codec : Codec α] (program : ι → Cloud M α) (input : ι)
    (supported : PureProgram (program input)) (duration : Nat) (fuel extra : Fin count → Nat)
    (events : List (Event count))
    (final : Simulation.State Durable (Except CloudError α × SimulationBackend.Worker) count)
    (executed :
      let start := fun worker => attempt (fuel worker) duration program input
      Simulation.run start SimulationBackend.advance events
        (Simulation.State.initial SimulationBackend.initial start) = .ok final) :
    ∃ extended,
      (let start := fun worker => attempt (fuel worker + extra worker) duration program input
       Simulation.run start SimulationBackend.advance events
         (Simulation.State.initial SimulationBackend.initial start) = .ok extended) ∧
      Simulation.State.Prefix (fun returned => returned.1 = .error exhausted) final extended := by
  have starts worker : Simulation.Prefix (fun returned => returned.1 = .error exhausted)
      (attempt (fuel worker) duration program input)
      (attempt (fuel worker + extra worker) duration program input) :=
    (run_truncates SimulationBackend.db SimulationBackend.noBlobs (queue duration)
      (codec.encode <$> program input) (supported.map codec.encode) (fuel worker) (extra worker)).program ⟨(), none⟩
  exact Simulation.Prefix.run
    (source := Simulation.State.initial SimulationBackend.initial
      (fun worker => attempt (fuel worker) duration program input)) starts SimulationBackend.advance events
    ⟨rfl, fun worker => (starts worker).workers⟩ executed

theorem step_bounded {program : Cloud M Json} {tree current node}
    (whole : Expansion program tree) (supported : PureProgram program)
    (route : TreeRoute tree Location.root current node)
    (comparable : Comparable (tree.journal Location.root)) (sameExit : (node.exit == node.exit) = true)
    (state : Durable) (valid : Valid tree state)
    (active : route.Activated (ConcurrentJournal.view state)) (fuel : Nat) (worker : SimulationBackend.Worker) :
    Safe (Valid tree) Grows
      (fun returned final => (returned.1 = .error exhausted ∧ fuel < sizeOf tree) ∨ ∃ response,
        returned = (.ok response, worker) ∧ ConcurrentJournal.Emits tree response final ∧
        ConcurrentJournal.StepProgress tree current node state response final)
      (.ofProgram ((ReplayInterpreter.Internal.step SimulationBackend.db SimulationBackend.noBlobs fuel program current).run worker)) state := by
  by_cases enough : sizeOf tree ≤ fuel
  · apply (step_safe whole supported route comparable sameExit state valid active fuel
      (Nat.le_trans route.fuel_bound enough) worker).weaken
    intro returned final kept done
    exact .inr done
  have enough' : route.prefixSteps + 1 ≤ fuel + sizeOf tree := Nat.le_trans route.fuel_bound (by omega)
  have safe := step_safe whole supported route comparable sameExit state valid active (fuel + sizeOf tree) enough' worker
  have bounded := safe.truncates Grows.refl (fun a b => a.trans b) valid
    (step_truncates SimulationBackend.db SimulationBackend.noBlobs program supported current fuel (sizeOf tree))
  apply bounded.weaken
  intro returned final kept done
  exact done.imp (fun stopped => ⟨stopped, Nat.lt_of_not_ge enough⟩) id

theorem Next.grow {tree returned before after} (next : Next tree returned before)
    (growth : Grows before after) : Next tree returned after := by
  rcases returned with ⟨work, worker⟩
  cases work with
  | idle => exact next
  | completed outcome => exact ⟨next.1, next.2.1, growth.completed outcome next.2.2⟩
  | item location =>
    obtain ⟨receipt, stored, active⟩ := next
    exact ⟨receipt, stored, active.grow growth.journal.1⟩

private theorem next_action (tree : ExecutionTree) (duration : Nat) (worker : SimulationBackend.Worker)
    (state : Durable) (valid : Valid tree state) :
    Safe (Valid tree) Grows
      (fun returned final => ∃ work, returned.1 = .ok work ∧ Next tree (work, returned.2) final)
      (.ofProgram ((liftM (queue duration).next :
        ExceptT CloudError (StateT SimulationBackend.Worker M) Work).run worker)) state := by
  apply Safe.bind Grows.refl (fun a b => a.trans b) (next_safe tree duration worker state) valid
  intro returned current kept next
  apply Safe.finished
  intro final finalValid later
  exact ⟨returned.1, rfl, next.grow later⟩

private theorem complete_action {tree : ExecutionTree} (duration : Nat) (location : Location)
    (receipt : LeaseQueueModel.Receipt) (response : StepResult) (state : Durable) (valid : Valid tree state)
    (emitted : ConcurrentJournal.Emits tree response state) :
    Safe (Valid tree) Grows
      (fun returned final => returned = (.ok (), (⟨(), none⟩ : SimulationBackend.Worker)) ∧
        ConcurrentJournal.Emits tree response final ∧ FinalStored response final)
      (.ofProgram ((liftM ((queue duration).complete location response) :
        ExceptT CloudError (StateT SimulationBackend.Worker M) Unit).run ⟨(), some (location, receipt)⟩)) state := by
  apply Safe.bind Grows.refl (fun a b => a.trans b)
    ((complete_safe duration location receipt response state valid emitted).remember
      (fun a b => a.trans b) state (.refl _)) valid
  intro returned current kept h
  obtain ⟨growth, rfl, stored⟩ := h
  apply Safe.finished
  intro final finalValid later
  exact ⟨rfl, emitted.grow (growth.trans later).journal,
    by cases response with
      | done outcome => exact later.completed outcome stored
      | runnable _ => trivial⟩

/-- The outcome's ordinary codec/error interpretation, with no backend state. -/
def expected [Codec α] (tree : ExecutionTree) : Except CloudError α :=
  (ReplayInterpreter.Internal.result (m := Id) tree.exit).run

def Answers [Codec α] (tree : ExecutionTree) (returned : Except CloudError α × SimulationBackend.Worker)
    (_ : Durable) : Prop := returned.1 = expected tree ∨ returned.1 = .error exhausted

theorem result_eq [Codec α] (outcome : Exit) (worker : SimulationBackend.Worker) :
    (ReplayInterpreter.Internal.result (m := StateT SimulationBackend.Worker M) (α := α) outcome).run worker =
      pure ((ReplayInterpreter.Internal.result (m := Id) (α := α) outcome).run, worker) := by
  cases outcome with
  | success value =>
    simp only [ReplayInterpreter.Internal.result, ReplayInterpreter.Internal.decode]
    cases Codec.decode (α := α) value <;> rfl
  | failure error | cancelled reason => rfl

private theorem result_safe [Codec α] (tree : ExecutionTree) (worker : SimulationBackend.Worker) (state : Durable) :
    Safe (Valid tree) Grows (Answers (α := α) tree)
      (.ofProgram ((ReplayInterpreter.Internal.result (m := StateT SimulationBackend.Worker M) tree.exit).run worker)) state := by
  rw [result_eq]
  exact .finished fun _ _ _ => .inl rfl

/-- The actual worker loop preserves the shared invariant for every fuel
budget. Every returned result is the pure tree's decoded outcome, or the
explicit fuel-exhaustion error. No successful step or final output is assumed. -/
theorem run_safe [Codec α] {program : Cloud M Json} {tree : ExecutionTree}
    (whole : Expansion program tree) (supported : PureProgram program)
    (comparable : Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (duration fuel : Nat) (worker : SimulationBackend.Worker) (state : Durable) (valid : Valid tree state) :
    Safe (Valid tree) Grows (Answers (α := α) tree)
      (.ofProgram ((ReplayInterpreter.Internal.run SimulationBackend.db SimulationBackend.noBlobs
        (queue duration) fuel program).run worker)) state := by
  induction fuel generalizing worker state with
  | zero => exact .finished fun _ _ _ => .inr rfl
  | succ fuel ih =>
    rw [ReplayInterpreter.Internal.run]
    apply Safe.bind Grows.refl (fun a b => a.trans b) (next_action tree duration worker state valid) valid
    intro returned polled kept done
    rcases returned with ⟨outcome, worker⟩
    obtain ⟨work, same, next⟩ := done
    dsimp only at same
    subst outcome
    cases work with
    | completed outcome =>
      have same := next.2.1
      subst outcome
      exact result_safe tree worker polled
    | idle => exact ih worker polled kept
    | item location =>
      obtain ⟨receipt, delivered, node, route, active⟩ := next
      apply Safe.bind Grows.refl (fun a b => a.trans b)
        (step_bounded whole supported route comparable (sameExit _ _ route.member) polled kept active (fuel + 1) worker) kept
      intro returned executed executedValid result
      rcases result with ⟨stopped, _short⟩ | ⟨response, rfl, emitted, _progress⟩
      · rcases returned with ⟨outcome, handle⟩
        dsimp only at stopped
        subst outcome
        exact .finished fun _ _ _ => .inr rfl
      · cases worker with
        | mk backend delivery =>
          cases backend
          dsimp only at delivered
          subst delivery
          apply Safe.bind Grows.refl (fun a b => a.trans b)
            (complete_action duration location receipt response executed executedValid emitted) executedValid
          intro returned published publishedValid done
          obtain ⟨rfl, emitted, stored⟩ := done
          cases response with
          | done outcome =>
            change outcome = tree.exit at emitted
            subst outcome
            exact result_safe tree _ published
          | runnable _ => exact ih _ published publishedValid

/-- Any finite legal schedule of the actual interpreter attempts, starting
from the empty journal and one root message. Workers crash independently and
restart with fresh receipts. Every returned outcome is the original tree's
outcome or fuel exhaustion; the durable final result cannot be changed. -/
theorem attempts_safe [codec : Codec α] (program : ι → Cloud M α) (input : ι)
    {tree : ExecutionTree} (whole : Expansion (codec.encode <$> program input) tree)
    (supported : PureProgram (program input))
    (comparable : Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (duration : Nat) (fuel : Fin count → Nat) (events : List (Event count))
    (final : Simulation.State Durable (Except CloudError α × SimulationBackend.Worker) count)
    (executed :
      let start := fun worker => attempt (fuel worker) duration program input
      Simulation.run start SimulationBackend.advance events
        (Simulation.State.initial SimulationBackend.initial start) = .ok final) :
    Grows SimulationBackend.initial final.durable ∧ Valid tree final.durable ∧
      ∀ worker returned, (final.workers worker).outcome? = some returned → Answers tree returned final.durable := by
  let start := fun worker => attempt (fuel worker) duration program input
  have fresh worker state (valid : Valid tree state) :
      Safe (Valid tree) Grows (Answers tree) (.ofProgram (start worker)) state :=
    run_safe whole (supported.map codec.encode) comparable sameExit duration (fuel worker) _ state valid
  have initial : AllSafe (Valid tree) Grows (fun _ => Answers tree)
      (Simulation.State.initial SimulationBackend.initial start) :=
    ⟨Valid.initial tree, fun worker => fresh worker _ (Valid.initial tree)⟩
  obtain ⟨growth, valid, workers⟩ := Simulation.run_safe (valid := Valid tree) (grows := Grows)
    Grows.refl (fun a b => a.trans b) start SimulationBackend.advance (fun _ => Answers tree) fresh
    (fun elapsed state valid => ⟨valid.advance elapsed, Grows.advance elapsed state⟩)
    events initial executed
  exact ⟨growth, valid, fun worker returned finished => (workers worker).returned Grows.refl valid finished⟩

/-- Fair scheduling and the end of a worker's crashes make its actual attempt
return. Fuel exhaustion is an allowed return, not workflow completion. -/
theorem attempts_return [codec : Codec α] (program : ι → Cloud M α) (input : ι)
    {tree : ExecutionTree} (whole : Expansion (codec.encode <$> program input) tree)
    (supported : PureProgram (program input))
    (comparable : Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (duration : Nat) (fuel : Fin count → Nat)
    (trace : Simulation.Trace (fun worker => attempt (fuel worker) duration program input) SimulationBackend.advance)
    (initialized : trace.states 0 = Simulation.State.initial SimulationBackend.initial
      (fun worker => attempt (fuel worker) duration program input))
    (fair : trace.WeaklyFair) (worker : Fin count) (cut : Nat) (noCrash : trace.NoCrashesAfter worker cut) :
    ∃ later returned, cut ≤ later ∧ (trace.states later).workers worker = .finished returned ∧
      Answers tree returned (trace.states later).durable := by
  have fresh worker state (valid : Valid tree state) :
      Safe (Valid tree) Grows (Answers tree)
        (.ofProgram (attempt (fuel worker) duration program input)) state :=
    run_safe whole (supported.map codec.encode) comparable sameExit duration (fuel worker) _ state valid
  apply trace.eventually_returns fair Grows.refl (fun a b => a.trans b) fresh
    (fun elapsed state valid => ⟨valid.advance elapsed, Grows.advance elapsed state⟩) _ worker cut noCrash
  rw [initialized]
  exact ⟨Valid.initial tree, fun worker => fresh worker _ (Valid.initial tree)⟩

end LeanCloud.Proofs.ConcurrentQueue
