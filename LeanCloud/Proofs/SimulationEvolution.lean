import LeanCloud.Simulation
import LeanCloud.Proofs.Effects

/-! Lift an atomic state relation through actual Sim events. Delayed replies do
not change durable state; remote requests retain their contract after a crash. -/

namespace LeanCloud.Proofs.SimulationEvolution
open LeanEff Simulation

variable {δ α : Type} (advance : δ → δ → Prop)

def Allowed : Atomic δ β → Prop
  | .step _ _ operation => ∀ world, advance world (operation world).2

variable {advance} (allowed : {β : Type} → Atomic δ β → Prop)

def ActorValid : Actor δ α → Prop
  | .waiting remote label operation next =>
      allowed (.step remote label operation) ∧ Effects.Continuation allowed next
  | .responding _ next => Effects.Continuation allowed next
  | .stopped | .finished _ => True

theorem ofProgram {program : SimM δ α} (valid : Effects.Program allowed program) :
    ActorValid allowed (Actor.ofProgram program) := by
  cases program with
  | pure value => trivial
  | impure operation next => cases operation; exact valid

structure Valid (allowed : Fin count → {β : Type} → Atomic δ β → Prop)
    (orphanAdvance : δ → δ → Prop) (state : State δ α count) : Prop where
  actors : ∀ actor, ActorValid (allowed actor) (state.actors actor)
  orphans : ∀ orphan ∈ state.orphans, ∀ world, orphanAdvance world (orphan.commit world)

variable {allowed : Fin count → {β : Type} → Atomic δ β → Prop} {orphanAdvance : δ → δ → Prop}

theorem initial (world : δ) (start : Start δ α count)
    (valid : ∀ actor generation, Effects.Program (allowed actor) (start actor generation)) :
    Valid allowed orphanAdvance (State.initial world start) :=
  ⟨fun actor => ofProgram (allowed actor) (valid actor 0), by simp [State.initial]⟩

private theorem setActor {state : State δ α count} (valid : Valid allowed orphanAdvance state)
    (actor : Fin count) (replacement : Actor δ α) (sound : ActorValid (allowed actor) replacement) :
    Valid allowed orphanAdvance (state.setActor actor replacement) := by
  refine ⟨?_, valid.orphans⟩
  intro index
  dsimp only [State.setActor]
  split
  next same => subst index; exact sound
  next => exact valid.actors index

/-- Every actual event retains its request contracts. A normal commit follows
its actor's relation; orphan commits follow the remote relation. This separates
private local writes from operations that can survive the originating process. -/
theorem step_preserves (advance : Fin count → δ → δ → Prop)
    (reflexive : ∀ world, orphanAdvance world world) (start : Start δ α count)
    (starts : ∀ actor generation, Effects.Program (allowed actor) (start actor generation))
    (commits : ∀ actor {β : Type} remote label (operation : δ → β × δ),
      allowed actor (.step remote label operation) → ∀ world, advance actor world (operation world).2)
    (remoteCommits : ∀ actor {β : Type} label (operation : δ → β × δ),
      allowed actor (.step true label operation) → ∀ world, orphanAdvance world (operation world).2)
    (state after : State δ α count) (event : Event count) (valid : Valid allowed orphanAdvance state)
    (executed : Simulation.step start event state = .ok after) :
    Valid allowed orphanAdvance after ∧
      ((∃ actor, event = .commit actor ∧ advance actor state.world after.world) ∨
        orphanAdvance state.world after.world) := by
  cases event with
  | commit actor =>
    cases current : state.actors actor <;> simp only [Simulation.step, current] at executed <;> try contradiction
    next remote label operation next =>
      cases executed
      have sound := valid.actors actor
      rw [current] at sound
      have changed := setActor valid actor (.responding (operation state.world).1 next) sound.2
      exact ⟨⟨changed.actors, changed.orphans⟩, .inl ⟨actor, rfl, commits actor remote label operation sound.1 state.world⟩⟩
  | resume actor =>
    cases current : state.actors actor <;> simp only [Simulation.step, current] at executed <;> try contradiction
    next value next =>
      cases executed
      have sound := valid.actors actor
      rw [current] at sound
      exact ⟨setActor valid actor _ (ofProgram (allowed actor) (Effects.apply _ next sound value)), .inr (reflexive _)⟩
  | crash actor =>
    cases current : state.actors actor <;> simp only [Simulation.step, current] at executed <;> try contradiction
    · rename_i remote label operation next
      cases executed
      have changed := setActor valid actor .stopped trivial
      have sound := valid.actors actor
      rw [current] at sound
      refine ⟨⟨changed.actors, ?_⟩, .inr (reflexive _)⟩
      intro orphan member world
      split at member
      next isRemote =>
        rcases Array.mem_push.mp member with previous | same
        · exact valid.orphans orphan previous world
        · subst orphan
          have request := sound.1
          rw [isRemote] at request
          exact remoteCommits actor label operation request world
      · exact valid.orphans orphan member world
    · cases executed
      exact ⟨setActor valid actor .stopped trivial, .inr (reflexive _)⟩
  | restart actor =>
    cases current : state.actors actor <;> simp only [Simulation.step, current] at executed <;> try contradiction
    cases executed
    have changed := setActor valid actor _ (ofProgram (allowed actor) (starts actor (state.generations actor + 1)))
    exact ⟨⟨changed.actors, changed.orphans⟩, .inr (reflexive _)⟩
  | commitOrphan index =>
    simp only [Simulation.step] at executed
    split at executed
    next inside =>
      cases executed
      refine ⟨⟨valid.actors, ?_⟩, .inr (valid.orphans _ (Array.getElem_mem inside) state.world)⟩
      intro orphan member
      exact valid.orphans orphan (Array.mem_of_mem_eraseIdx member)
    next => cases executed
  | discardOrphan index =>
    simp only [Simulation.step] at executed
    split at executed
    next inside =>
      cases executed
      refine ⟨⟨valid.actors, ?_⟩, .inr (reflexive _)⟩
      intro orphan member
      exact valid.orphans orphan (Array.mem_of_mem_eraseIdx member)
    next => cases executed

end LeanCloud.Proofs.SimulationEvolution
