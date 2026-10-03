import LeanCloud.Proofs.MainTheorems

/-! A kernel-checked witness that the completion theorem's processing-window
assumption can hold for the actual deployment, starting from empty storage.
The trace uses broker delivery and separate operation commit/reply events. -/

namespace LeanCloudTests.ProgressWitness
open Lean LeanEff LeanCloud LeanCloud.Proofs SimulationBackend SimulationProgress

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private def source (_ : Unit) : Cloud (SimM World) Bool := EffF.pure true
private def actors : Simulation.Start World Unit 2 := start 10 10 100 source ()
private abbrev State := Simulation.State World Unit 2
private abbrev Trace := SchedulerOwnership.Trace actors (fun _ => True)
private abbrev Event := Sum (Simulation.Event 2) NetworkEvent

private def runEvents : List Event → State → Except Simulation.Error State
  | [], state => .ok state
  | .inl event :: rest, state => do
      let next ← SimulationBackend.step actors event state
      runEvents rest next
  | .inr event :: rest, state =>
      runEvents rest { state with world := networkStep event state.world }

private theorem run_trace (events : List Event) {before after : State}
    (ran : runEvents events before = .ok after) : Trace before after := by
  induction events generalizing before with
  | nil => cases ran; exact .refl _
  | cons event rest ih =>
    cases event with
    | inl event =>
      cases first : SimulationBackend.step actors event before with
      | error error =>
        simp only [runEvents, first] at ran
        change Except.error error = Except.ok after at ran
        cases ran
      | ok middle =>
        have tail : runEvents rest middle = .ok after := by simpa only [runEvents, first] using! ran
        exact (SchedulerOwnership.Trace.actor (.refl before) event trivial first).trans (ih tail)
    | inr event =>
      exact (SchedulerOwnership.Trace.network (.refl before) event).trans (ih ran)

private def afterEvents (events : List Event) (before : State) : State :=
  (runEvents events before).toOption.getD before

private theorem after_trace (events : List Event) (before : State)
    (ok : (runEvents events before).isOk = true) : Trace before (afterEvents events before) := by
  cases ran : runEvents events before with
  | error error => rw [ran] at ok; cases ok
  | ok after =>
    simpa only [afterEvents, ran, Except.toOption, Option.getD] using run_trace events ran

private def cycles (actor : Fin 2) (count : Nat) : List Event :=
  (List.replicate count [.inl (.commit actor), .inl (.resume actor)]).flatten

-- Start both actors, request an assignment, deliver it, and let the worker receive it.
private def boot := cycles 0 3 ++ cycles 1 3 ++ [.inr (.deliver 0)] ++
  cycles 0 5 ++ [.inr (.deliver 0)] ++ cycles 1 1
private def reading := cycles 1 1
-- The scheduler advances its durable clock while the worker is suspended.
private def interleaving := [.inr (.tick 1)] ++ cycles 0 4
private def creating := cycles 1 1
private def working := cycles 1 2
private def reporting := cycles 1 2 ++ [.inr (.deliver 0)]
private def saving := cycles 0 2 ++ [.inl (.commit 0)]

private def initial : State := Simulation.State.initial {} actors
private def started := afterEvents boot initial
private def readState := afterEvents reading started
private def interleaved := afterEvents interleaving readState
private def created := afterEvents creating interleaved
private def executed := afterEvents working created
private def delivered := afterEvents reporting executed
private def saved := afterEvents saving delivered

private theorem boot_trace : Trace initial started := after_trace boot initial (by cbv)
private theorem read_trace : Trace started readState := after_trace reading started (by cbv)
private theorem interleaved_trace : Trace readState interleaved := after_trace interleaving readState (by cbv)
private theorem create_trace : Trace interleaved created := after_trace creating interleaved (by cbv)
private theorem work_trace : Trace created executed := after_trace working created (by cbv)
private theorem report_trace : Trace executed delivered := after_trace reporting executed (by cbv)
private theorem save_trace : Trace delivered saved := after_trace saving delivered (by cbv)

private def assignment : Assignment := ⟨0, Location.root, Location.root, false⟩
private def report : Report := ⟨"worker-1", 0, .ok .done, #[ReplayStore.returnKey Location.root]⟩

-- Compute a finite witness for the existing Execution relation. This only runs
-- SimM operations for the proof check; it does not implement Cloud semantics.
mutual
  private def denote (program : SimM δ α) (world : δ) : α × δ × Nat :=
    match program with
    | .pure value => (value, world, 0)
    | .impure (.step _ _ operation) next =>
      let rest := denoteNext next (operation world).1 (operation world).2
      (rest.1, rest.2.1, rest.2.2 + 1)
  termination_by structural program

  private def denoteNext (next : ArrsF (Atomic δ) α β) (value : α) (world : δ) : β × δ × Nat :=
    match next with
    | .one next => denote (next value) world
    | .append head tail =>
      let first := denoteNext head value world
      let rest := denoteNext tail first.1 first.2.1
      (rest.1, rest.2.1, first.2.2 + rest.2.2)
  termination_by structural next
end

mutual
  private theorem denote_sound (program : SimM δ α) (world : δ) :
      Execution program world (denote program world).1 (denote program world).2.1 (denote program world).2.2 :=
    match program with
    | .pure value => .pure value world
    | .impure (.step remote label operation) next =>
      .step remote label operation next world (denoteNext_sound next (operation world).1 (operation world).2)
  termination_by structural program

  private theorem denoteNext_sound (next : ArrsF (Atomic δ) α β) (value : α) (world : δ) :
      Continuation next value world (denoteNext next value world).1 (denoteNext next value world).2.1
        (denoteNext next value world).2.2 :=
    match next with
    | .one next => .one next value (denote_sound (next value) world)
    | .append head tail =>
      .append (denoteNext_sound head value world)
        (denoteNext_sound tail (denoteNext head value world).1 (denoteNext head value world).2.1)
  termination_by structural next
end

private def resumeProgram (program : SimM World α) (world : World) : SimM World α :=
  match program with
  | .pure value => .pure value
  | .impure (.step _ _ operation) next => next.apply (operation world).1

private def workerProgram := Worker.execute "worker-1" (observed "worker-1") blobs 10 source () assignment
private def afterRead := resumeProgram workerProgram started.world
private def afterCreate := resumeProgram afterRead interleaved.world

private theorem worker_tail : Execution afterCreate created.world report executed.world 2 := by
  let checked := denote afterCreate created.world
  have same : checked = (report, executed.world, 2) := by
    dsimp only [checked]
    cbv
  have valid := denote_sound afterCreate created.world
  change Execution _ _ checked.1 checked.2.1 checked.2.2 at valid
  rw [same] at valid
  exact valid

private theorem worker_execution :
    DeploymentExecution.Execution actors workerProgram started report executed := by
  apply DeploymentExecution.Execution.step (waiting := .refl started) (committed := read_trace)
  · cbv
  · change DeploymentExecution.Execution actors afterRead readState report executed
    conv => arg 2; cbv
    apply DeploymentExecution.Execution.step (waiting := interleaved_trace) (committed := create_trace)
    · cbv
    · have tail : DeploymentExecution.Execution actors afterCreate created report executed :=
        .uninterrupted worker_tail work_trace
      conv at tail => arg 2; cbv
      conv => arg 2; cbv
      exact tail

private theorem window : DeploymentProgress.Window actors 10 source () initial saved := by
  refine ⟨started, executed, delivered, saved, "worker-1", assignment, report,
    boot_trace, ?_, worker_execution, report_trace, ?_, ?_, save_trace, ?_, .refl _⟩
  · cbv; exact List.mem_singleton_self _
  · cbv; exact List.mem_singleton_self _
  · refine ⟨delivered.world.scheduler.jobs[0]!, ?_, 100, ?_⟩
    · cbv; exact Array.mem_def.mpr (List.mem_singleton_self _)
    · cbv
  · cbv

private def sampled : DeploymentProgress.Run actors where
  state | 0 => initial | _ + 1 => saved
  initial := rfl
  next index := by
    cases index with
    | zero => exact ((boot_trace.trans worker_execution.trace).trans report_trace).trans save_trace
    | succ _ => exact .refl _

/-- The operational premise of the main completion theorem has a real witness.
Neither the actors nor the initial storage are replaced by fabricated states. -/
theorem processing_windows_exist :
    ∃ run : DeploymentProgress.Run (start (workers := 1) 10 10 100 source ()),
      DeploymentProgress.MakesProgress 1 10 10 100 source () run := by
  refine ⟨sampled, ?_⟩
  intro index unfinished
  cases index with
  | zero => exact ⟨1, by decide, window⟩
  | succ index =>
    have done : (sampled.state (index + 1)).world.scheduler.finished = true := by cbv
    rw [done] at unfinished
    cases unfinished

end LeanCloudTests.ProgressWitness
