import LeanCloud.Proofs.SimulationLogic

/-! Finite uninterrupted execution of an existing SimM program. This proof
relation counts atomic operations; it is not a new runtime interpreter. Each
operation is realized by separate commit and reply events in the actual Sim.
It supplies a possible uninterrupted execution, not a fairness assumption. -/

namespace LeanCloud.Proofs.SimulationProgress
open LeanEff Simulation SimulationLogic

mutual
  inductive Execution : SimM δ α → δ → α → δ → Nat → Prop where
    | pure (value : α) (world : δ) : Execution (.pure value) world value world 0
    | step (remote : Bool) (label : String) (operation : δ → β × δ)
        (next : ArrsF (Atomic δ) β α) (world : δ)
        (rest : Continuation next (operation world).1 (operation world).2 value final steps) :
        Execution (.impure (.step remote label operation) next) world value final (steps + 1)

  inductive Continuation : ArrsF (Atomic δ) α β → α → δ → β → δ → Nat → Prop where
    | one (next : α → SimM δ β) (value : α)
        (rest : Execution (next value) world result final steps) :
        Continuation (.one next) value world result final steps
    | append (first : Continuation head value world middle between firstSteps)
        (rest : Continuation tail middle between result final restSteps) :
        Continuation (.append head tail) value world result final (firstSteps + restSteps)
end

mutual
  theorem execution_exists (program : SimM δ α) (world : δ) :
      ∃ value final steps, Execution program world value final steps :=
    match program with
    | .pure value => ⟨value, world, 0, .pure value world⟩
    | .impure (.step remote label operation) next => by
      obtain ⟨value, final, steps, rest⟩ := continuation_exists next (operation world).1 (operation world).2
      exact ⟨value, final, steps + 1, .step remote label operation next world rest⟩
  termination_by structural program

  theorem continuation_exists (next : ArrsF (Atomic δ) α β) (value : α) (world : δ) :
      ∃ result final steps, Continuation next value world result final steps :=
    match next with
    | .one next => by
      obtain ⟨result, final, steps, rest⟩ := execution_exists (next value) world
      exact ⟨result, final, steps, .one next value rest⟩
    | .append head tail => by
      obtain ⟨middle, between, firstSteps, first⟩ := continuation_exists head value world
      obtain ⟨result, final, restSteps, rest⟩ := continuation_exists tail middle between
      exact ⟨result, final, firstSteps + restSteps, .append first rest⟩
  termination_by structural next
end

theorem Execution.bind {program : SimM δ α} {next : α → SimM δ β}
    (first : Execution program world value between firstSteps)
    (rest : Execution (next value) between result final restSteps) :
    Execution (EffF.bind program next) world result final (firstSteps + restSteps) := by
  cases first with
  | pure => simpa [EffF.bind] using rest
  | step remote label operation continuation world continued =>
    simpa [EffF.bind, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Execution.step remote label operation (continuation.append (.one next)) world
        (.append continued (.one next _ rest))

theorem Execution.send (remote : Bool) (label : String) (operation : δ → α × δ) (world : δ) :
    Execution (EffF.send (.step remote label operation)) world (operation world).1 (operation world).2 1 :=
  .step remote label operation (.one .pure) world (.one .pure _ (.pure _ _))

private def View : ArrsF.ViewL (Atomic δ) α β → α → δ → β → δ → Nat → Prop
  | .one next, value, world, result, final, steps => Execution (next value) world result final steps
  | .cons next tail, value, world, result, final, steps =>
      ∃ middle between firstSteps restSteps,
        Execution (next value) world middle between firstSteps ∧
        Continuation tail middle between result final restSteps ∧ steps = firstSteps + restSteps

private theorem viewLAppend (head : ArrsF (Atomic δ) α β) (tail : ArrsF (Atomic δ) β γ)
    (first : Continuation head value world middle between firstSteps)
    (rest : Continuation tail middle between result final restSteps) :
    View (head.viewLAppend tail) value world result final (firstSteps + restSteps) := by
  cases first with
  | one next value first => exact ⟨_, _, _, _, first, rest, rfl⟩
  | append first second =>
    simpa [ArrsF.viewLAppend, Nat.add_assoc] using viewLAppend _ _ first (.append second rest)
termination_by sizeOf head

private theorem viewL (next : ArrsF (Atomic δ) α β)
    (executed : Continuation next value world result final steps) :
    View next.viewL value world result final steps := by
  cases executed with
  | one next value rest => exact rest
  | append first rest => exact viewLAppend _ _ first rest

theorem Continuation.apply (next : ArrsF (Atomic δ) α β)
    (executed : Continuation next value world result final steps) :
    Execution (next.apply value) world result final steps := by
  have viewed := viewL next executed
  rw [ArrsF.apply]
  split
  next continuation found =>
    rw [found] at viewed
    exact viewed
  next continuation rest found =>
    rw [found] at viewed
    obtain ⟨middle, between, firstSteps, restSteps, first, tail, rfl⟩ := viewed
    exact first.bind (Continuation.apply rest tail)
termination_by sizeOf next
decreasing_by
  have smaller := ArrsF.viewL_rest_lt next
  simp_all

mutual
  theorem Execution.post (rules : Rules δ) {program : SimM δ α}
      (executed : Execution program world value final steps)
      {pre : δ → Prop} {post : α → δ → Prop}
      (valid : rules.Program pre post program) (invariant : rules.invariant world) (holds : pre world) :
      rules.invariant final ∧ post value final :=
    match executed with
    | .pure _ _ => ⟨invariant, valid world invariant holds⟩
    | .step _ _ _ _ _ rest => by
      obtain ⟨required, reply, entails, operation, continuation⟩ := valid
      obtain ⟨invariant, _, replied⟩ := operation.execute world invariant (entails world invariant holds)
      exact rest.post rules continuation invariant replied
  termination_by structural executed

  theorem Continuation.post (rules : Rules δ) {next : ArrsF (Atomic δ) α β}
      (executed : Continuation next value world result final steps)
      {pre : α → δ → Prop} {post : β → δ → Prop}
      (valid : rules.Continuation pre post next) (invariant : rules.invariant world) (holds : pre value world) :
      rules.invariant final ∧ post result final :=
    match executed with
    | .one _ _ rest => rest.post rules (valid value) invariant holds
    | .append first rest => by
      obtain ⟨middle, firstValid, restValid⟩ := valid
      obtain ⟨invariant, holds⟩ := first.post rules firstValid invariant holds
      exact rest.post rules restValid invariant holds
  termination_by structural executed
end

private theorem setActor_current (state : State δ α count) (actor : Fin count) :
    state.setActor actor (state.actors actor) = state := by
  cases state
  simp only [State.setActor]
  congr
  funext index
  split <;> simp_all

/-- Realize an execution using only this actor's commit and reply events.
Other actors, process generations, and abandoned requests remain unchanged.
There are exactly two simulator events per atomic operation. -/
theorem Execution.run (start : Start δ α count) (actor : Fin count)
    {program : SimM δ α} (executed : Execution program world value final steps)
    (state : State δ α count)
    (current : state.actors actor = .ofProgram program) (sameWorld : state.world = world) :
    ∃ events : List (Event count),
      (∀ event ∈ events, event = .commit actor ∨ event = .resume actor) ∧
      events.length = 2 * steps ∧
      Simulation.run start events state =
        .ok { state.setActor actor (.finished value) with world := final } := by
  cases executed with
  | pure value world =>
    change state.actors actor = .finished value at current
    have unchanged : state.setActor actor (.finished value) = state := by
      rw [← current]
      exact setActor_current state actor
    refine ⟨[], by simp, rfl, ?_⟩
    change Except.ok state = _
    rw [unchanged, ← sameWorld]
  | step remote label operation next world rest =>
    let committed : State δ α count :=
      { state.setActor actor (.responding (operation world).1 next) with world := (operation world).2 }
    let resumed := committed.setActor actor (.ofProgram (next.apply (operation world).1))
    have commit : Simulation.step start (.commit actor) state = .ok committed := by
      simp [Simulation.step, current, Actor.ofProgram, sameWorld, committed]
    have resume : Simulation.step start (.resume actor) committed = .ok resumed := by
      simp [Simulation.step, committed, resumed, State.setActor]
    obtain ⟨events, onlyActor, length, finished⟩ :=
      (rest.apply next).run start actor resumed (by simp [resumed, State.setActor]) rfl
    refine ⟨.commit actor :: .resume actor :: events, ?_, ?_, ?_⟩
    · intro event member
      rcases List.mem_cons.mp member with rfl | member
      · exact Or.inl rfl
      rcases List.mem_cons.mp member with rfl | member
      · exact Or.inr rfl
      exact onlyActor event member
    · simp only [List.length_cons, length]
      omega
    · change (do
        let committed ← Simulation.step start (.commit actor) state
        let resumed ← Simulation.step start (.resume actor) committed
        Simulation.run start events resumed) = _
      rw [commit]
      change (do
        let resumed ← Simulation.step start (.resume actor) committed
        Simulation.run start events resumed) = _
      rw [resume]
      change Simulation.run start events resumed = _
      rw [finished]
      simp [resumed, committed, State.setActor]
      funext index
      split <;> simp_all
termination_by steps

/-- A valid program has a finite uninterrupted execution satisfying its
postcondition. This is an opportunity for progress, not a claim that an
arbitrary schedule gives the actor that opportunity. -/
theorem completes (rules : Rules δ) (start : Start δ α count) (actor : Fin count)
    {program : SimM δ α} {pre : δ → Prop} {post : α → δ → Prop}
    (valid : rules.Program pre post program) (state : State δ α count)
    (current : state.actors actor = .ofProgram program)
    (invariant : rules.invariant state.world) (holds : pre state.world) :
    ∃ events value world,
      (∀ event ∈ events, event = .commit actor ∨ event = .resume actor) ∧
      Simulation.run start events state = .ok { state.setActor actor (.finished value) with world } ∧
      rules.invariant world ∧ post value world := by
  obtain ⟨value, world, steps, executed⟩ := execution_exists program state.world
  obtain ⟨events, onlyActor, _, finished⟩ := executed.run start actor state current rfl
  exact ⟨events, value, world, onlyActor, finished, executed.post rules valid invariant holds⟩

end LeanCloud.Proofs.SimulationProgress
