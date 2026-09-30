import LeanCloud.Proofs.ConcurrentFuel

/-! Realize any finite prefix of repeated workers with the actual finite loop.
Only proof-only repetition events disappear. All commits, saved replies, crashes,
restarts and clock advances retain their order and their durable effects. -/

namespace LeanCloud.Proofs.ConcurrentFuel
open Lean Simulation SimulationBackend ConcurrentRepeated

def eventsBefore (trace : RawTrace duration traversal program count) : Nat → List (Simulation.Event count)
  | 0 => []
  | n + 1 => match trace.events n with
    | .ordinary event => eventsBefore trace n ++ [event]
    | .repeatIteration _ => eventsBefore trace n

/-- A finite prefix needs at most one outer-loop unit per repeated-model event,
in addition to its fixed traversal budget. Restart restores the initial budget. -/
theorem finite_prefix [Codec α] {program : Cloud M Json} {tree : ExecutionTree}
    (whole : Expansion program tree) (supported : PureProgram program)
    (comparable : ReplayRecovery.Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (duration traversal : Nat) (enough : sizeOf tree ≤ traversal)
    (trace : RawTrace duration traversal program count)
    (initialized : trace.states 0 = Simulation.State.initial SimulationBackend.initial
      (fun _ : Fin count => rawIteration duration traversal program))
    (limit : Nat) (budget : Fin count → Nat) (enoughBudget : ∀ worker, traversal + limit ≤ budget worker) :
    ∀ n, n ≤ limit → ∃ remaining : Fin count → Nat, ∃ target : Simulation.State Durable (Answer α) count,
      (let start := fun worker : Fin count => loop duration (budget worker + 1) program
       Simulation.run start SimulationBackend.advance (eventsBefore trace n)
         (Simulation.State.initial SimulationBackend.initial start) = .ok target) ∧
      Related duration remaining program (trace.states n) target ∧
      ∀ worker, traversal + limit - n ≤ remaining worker := by
  obtain ⟨kept, _⟩ := raw_certified whole supported comparable sameExit duration traversal enough trace initialized
  have answers n worker returned (finished : ((trace.states n).workers worker).outcome? = some returned) :
      Returned tree returned ((recordTrace trace).states n).durable := by
    apply ((kept n).2 worker).returned ConcurrentAudit.Grows.refl (kept n).1
    change (((History.repeatedTrace trace).states n).workers worker).outcome? = _
    rwa [History.repeated_trace_outcome]
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨budget, Simulation.State.initial SimulationBackend.initial (fun worker => loop duration (budget worker + 1) program), rfl, ?_, ?_⟩
    · rw [initialized]
      exact ⟨rfl, fun worker => Follows.entry duration traversal (budget worker) program supported (by have bound := enoughBudget worker; omega)⟩
    · intro worker; simpa using enoughBudget worker
  | succ n ih =>
    intro within
    obtain ⟨remaining, target, ran, related, reserve⟩ := ih (by omega)
    cases event : trace.events n with
    | ordinary action =>
      have sourceStep := trace.schedule.execution n action (by simp [Repeated.Trace.schedule, event])
      obtain ⟨extended, executed, follows⟩ := related.ordinary duration traversal budget remaining program supported
        (fun worker => by have bound := enoughBudget worker; omega) action sourceStep
      refine ⟨remainingAfter budget remaining action, extended, ?_, follows, ?_⟩
      · simp only [eventsBefore, event]
        rw [Simulation.run, List.foldlM_append]
        simp only [List.foldlM_cons, List.foldlM_nil, bind_pure]
        change (Simulation.run _ _ (eventsBefore trace n) _ >>= fun state => Simulation.step _ _ action state) = _
        rw [ran]
        exact executed
      · intro worker
        have reserved := reserve worker
        have initialReserve := enoughBudget worker
        cases action <;> simp only [remainingAfter]
        all_goals first | omega | split <;> omega
    | repeatIteration worker =>
      have sourceStep := trace.execution n
      cases observed : (trace.states n).workers worker <;>
        simp only [Repeated.step, event, observed] at sourceStep
      case finished value =>
        split at sourceStep
        next allowed =>
          obtain ⟨outcome, same, _⟩ := answers n worker value (by rw [observed]; rfl)
          subst value
          have same := (again_iff (.ok outcome, (⟨(), none⟩ : SimulationBackend.Worker))).mp allowed
          cases same
          have nextState := (Except.ok.inj sourceStep).symm
          cases available : remaining worker with
          | zero => have reserved := reserve worker; rw [available] at reserved; omega
          | succ left =>
            have follows := related.repeatIteration worker traversal left supported (by
              have reserved := reserve worker; rw [available] at reserved; omega) available observed
            rw [← nextState] at follows
            refine ⟨fun index => if index = worker then left else remaining index, target, ?_, follows, ?_⟩
            · simpa only [eventsBefore, event] using ran
            · intro index
              by_cases same : index = worker
              · subst index
                have reserved := reserve worker
                rw [available] at reserved
                simp only [↓reduceIte]
                omega
              · simp only [same, ↓reduceIte]
                have reserved := reserve index
                omega
        next refused => cases sourceStep
      all_goals cases sourceStep

/-- A successful terminal iteration maps to the final interpreter result,
with no exhaustion exception in this conclusion. Workflow failures are included. -/
theorem Related.returned [Codec α] {duration remaining program outcome}
    {source : Simulation.State Durable Outcome count} {target : Simulation.State Durable (Answer α) count}
    (same : Related duration remaining program source target) (worker : Fin count)
    (finished : (source.workers worker).outcome? = some (.ok (some outcome), ⟨(), none⟩)) :
    (target.workers worker).outcome? = some
      ((ReplayInterpreter.Internal.result (m := Id) (α := α) outcome).run, ⟨(), none⟩) := by
  have follows := same.2 worker
  cases observed : source.workers worker <;> simp only [observed, Simulation.Worker.outcome?] at finished
  case finished value =>
    cases finished
    rw [observed] at follows
    have exactResult := follows.returned
    rw [resume, ConcurrentQueue.result_eq] at exactResult
    rcases exactResult.returned rfl with impossible | returned
    · exact False.elim impossible
    · exact returned
  all_goals cases finished

/-- The finite loop realizes a completed repeated prefix with an explicit
budget. This theorem reuses its actual events; it does not choose a new schedule. -/
theorem realizes_return [Codec α] {program : Cloud M Json} {tree : ExecutionTree}
    (whole : Expansion program tree) (supported : PureProgram program)
    (comparable : ReplayRecovery.Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (duration traversal : Nat) (enough : sizeOf tree ≤ traversal)
    (trace : RawTrace duration traversal program count)
    (initialized : trace.states 0 = Simulation.State.initial SimulationBackend.initial
      (fun _ : Fin count => rawIteration duration traversal program))
    (atTime : Nat) (budget : Fin count → Nat) (enoughBudget : ∀ worker, traversal + atTime ≤ budget worker) (worker : Fin count)
    (finished : ((trace.states atTime).workers worker).outcome? = some (.ok (some tree.exit), ⟨(), none⟩)) :
    ∃ target : Simulation.State Durable (Answer α) count,
      (let start := fun worker : Fin count => loop duration (budget worker + 1) program
       Simulation.run start SimulationBackend.advance (eventsBefore trace atTime)
         (Simulation.State.initial SimulationBackend.initial start) = .ok target) ∧
      target.durable = (trace.states atTime).durable ∧
      (target.workers worker).outcome? = some (ConcurrentQueue.expected tree, ⟨(), none⟩) := by
  obtain ⟨remaining, target, executed, related, _⟩ := finite_prefix (α := α) whole supported comparable sameExit duration traversal enough
    trace initialized atTime budget enoughBudget atTime (Nat.le_refl _)
  exact ⟨target, executed, related.1.symm, related.returned worker finished⟩

end LeanCloud.Proofs.ConcurrentFuel
