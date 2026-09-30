import LeanCloud.Proofs.SimulationComposition

/-! A finite legal schedule can be reused when computations are extended past
an explicit stopping result. Commits, saved replies, crashes, and restarts keep
their individual boundaries; every shared durable state remains identical. -/

namespace LeanCloud.Simulation
open LeanEff

def State.Prefix (stop : α → Prop) (first second : State δ α count) : Prop :=
  first.durable = second.durable ∧ ∀ index, Worker.Prefix stop (first.workers index) (second.workers index)

theorem State.Prefix.refl (stop : α → Prop) (state : State δ α count) : State.Prefix stop state state :=
  ⟨rfl, fun index => .refl stop (state.workers index)⟩

theorem State.Prefix.trans {stop : α → Prop} {first middle last : State δ α count}
    (before : State.Prefix stop first middle) (after : State.Prefix stop middle last) : State.Prefix stop first last :=
  ⟨before.1.trans after.1, fun index => (before.2 index).trans (after.2 index)⟩

theorem State.Prefix.replace {stop : α → Prop} {first second : State δ α count}
    (same : State.Prefix stop first second) (index : Fin count) {left right : Worker δ α}
    (next : Worker.Prefix stop left right) (durable : δ) :
    State.Prefix stop { first.setWorker index left with durable }
      { second.setWorker index right with durable } := by
  refine ⟨rfl, ?_⟩
  intro other
  by_cases equal : other = index
  · subst other; simpa only [State.setWorker_same] using next
  · simpa only [State.setWorker_other _ _ _ _ equal] using same.2 other

/-- A schedule valid for the shorter computations is also valid for their
extensions. An exhausted worker cannot receive a legal event in the shorter
schedule, so its extension simply remains paused. -/
theorem Prefix.step_at {stop : α → Prop} {first second : Fin count → SimM δ α}
    (clock : Nat → δ → δ) (event : Event count)
    (starts : ∀ index, event = .restart index → Prefix stop (first index) (second index))
    {source target final : State δ α count}
    (same : State.Prefix stop source target)
    (executed : Simulation.step first clock event source = .ok final) :
    ∃ extended, Simulation.step second clock event target = .ok extended ∧ State.Prefix stop final extended := by
  cases event with
  | commit index =>
    have selected := same.2 index
    generalize left : source.workers index = small at selected
    generalize right : target.workers index = large at selected
    cases selected with
    | waiting operation small large next =>
      simp only [Simulation.step, left, Except.ok.injEq] at executed
      subst final
      refine ⟨_, by simp only [Simulation.step, right]; rfl, ?_⟩
      rw [same.1]
      exact same.replace index (.responding _ _ _ (next _)) _
    | responding | stopped | finished | truncated => simp [Simulation.step, left] at executed
  | resume index =>
    have selected := same.2 index
    generalize left : source.workers index = small at selected
    generalize right : target.workers index = large at selected
    cases selected with
    | responding value small large next =>
      simp only [Simulation.step, left, Except.ok.injEq] at executed
      subst final
      refine ⟨_, by simp only [Simulation.step, right]; rfl, ?_⟩
      have related := same.replace index next.workers target.durable
      simpa only [State.Prefix, State.setWorker, same.1] using related
    | waiting | stopped | finished | truncated => simp [Simulation.step, left] at executed
  | crash index =>
    have selected := same.2 index
    generalize left : source.workers index = small at selected
    generalize right : target.workers index = large at selected
    cases selected with
    | waiting | responding =>
      simp only [Simulation.step, left, Except.ok.injEq] at executed
      subst final
      refine ⟨_, by simp only [Simulation.step, right]; rfl, ?_⟩
      have related := same.replace index .stopped target.durable
      simpa only [State.Prefix, State.setWorker, same.1] using related
    | stopped | finished | truncated => simp [Simulation.step, left] at executed
  | restart index =>
    have selected := same.2 index
    generalize left : source.workers index = small at selected
    generalize right : target.workers index = large at selected
    cases selected with
    | stopped =>
      simp only [Simulation.step, left, Except.ok.injEq] at executed
      subst final
      refine ⟨_, by simp only [Simulation.step, right]; rfl, ?_⟩
      have related := same.replace index (starts index rfl).workers target.durable
      simpa only [State.Prefix, State.setWorker, same.1] using related
    | waiting | responding | finished | truncated => simp [Simulation.step, left] at executed
  | advanceTime elapsed =>
    simp only [Simulation.step, Except.ok.injEq] at executed
    subst final
    exact ⟨_, rfl, congrArg (clock elapsed) same.1, same.2⟩

theorem Prefix.step {stop : α → Prop} {first second : Fin count → SimM δ α}
    (starts : ∀ index, Prefix stop (first index) (second index)) (clock : Nat → δ → δ)
    (event : Event count) {source target final : State δ α count}
    (same : State.Prefix stop source target)
    (executed : Simulation.step first clock event source = .ok final) :
    ∃ extended, Simulation.step second clock event target = .ok extended ∧ State.Prefix stop final extended :=
  Prefix.step_at clock event (fun index _ => starts index) same executed

/-- Reuse the exact finite event list, including independent crashes and
restarts. The larger computations commit the same durable changes and preserve
every returned value that was not an allowed truncation. -/
theorem Prefix.run {stop : α → Prop} {first second : Fin count → SimM δ α}
    (starts : ∀ index, Prefix stop (first index) (second index)) (clock : Nat → δ → δ)
    (events : List (Event count)) {source target final : State δ α count}
    (same : State.Prefix stop source target)
    (executed : Simulation.run first clock events source = .ok final) :
    ∃ extended, Simulation.run second clock events target = .ok extended ∧ State.Prefix stop final extended := by
  induction events generalizing source target with
  | nil => cases executed; exact ⟨target, rfl, same⟩
  | cons event events ih =>
    change (Simulation.step first clock event source >>= fun middle =>
      Simulation.run first clock events middle) = .ok final at executed
    cases firstStep : Simulation.step first clock event source with
    | error error => simp [firstStep, bind, Except.bind] at executed
    | ok middle =>
      obtain ⟨next, committed, related⟩ := Prefix.step starts clock event same firstStep
      obtain ⟨extended, finished, preserved⟩ := ih related (by
        simpa only [firstStep, bind, Except.bind] using executed)
      refine ⟨extended, ?_, preserved⟩
      change (Simulation.step second clock event target >>= fun middle =>
        Simulation.run second clock events middle) = .ok extended
      rw [committed]
      exact finished

end LeanCloud.Simulation
