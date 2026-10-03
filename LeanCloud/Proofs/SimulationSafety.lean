import LeanCloud.Proofs.SimulationLogic

/-! Soundness of continuation assertions for the existing simulator. Actor
guarantees must respect other actors' interference assumptions. A remote commit
must respect every actor, because its original process may already have died. -/

namespace LeanCloud.Proofs.SimulationSafety
open LeanEff Simulation SimulationLogic

structure System (δ : Type) (count : Nat) where
  invariant : δ → Prop
  evolution : δ → δ → Prop
  rely : Fin count → δ → δ → Prop
  guarantee : Fin count → Bool → δ → δ → Prop
  reflexive : ∀ world, evolution world world
  transitive : ∀ {first middle last}, evolution first middle → evolution middle last → evolution first last
  compatible : ∀ actor remote before after,
    invariant before → invariant after → guarantee actor remote before after →
      evolution before after ∧ ∀ other, other ≠ actor ∨ remote = true → rely other before after

namespace System
variable {δ α : Type} {count : Nat} (system : System δ count)

def rules (actor : Fin count) : Rules δ :=
  ⟨system.invariant, system.rely actor, system.evolution, system.guarantee actor⟩

/-- An abandoned request keeps its original stable precondition. Its result is
discarded, but its durable mutation must remain safe for all surviving actors. -/
def OrphanValid (orphan : Orphan δ) (world : δ) : Prop :=
  ∃ required : δ → Prop, required world ∧
    (∀ before after, system.invariant before → system.invariant after →
      system.evolution before after → required before → required after) ∧
    ∀ world, system.invariant world → required world →
      system.invariant (orphan.commit world) ∧ system.evolution world (orphan.commit world) ∧
        ∀ actor, system.rely actor world (orphan.commit world)

structure Valid (post : Fin count → α → δ → Prop) (state : State δ α count) : Prop where
  invariant : system.invariant state.world
  actors : ∀ actor, (system.rules actor).ActorValid (post actor) (state.actors actor) state.world
  orphans : ∀ orphan ∈ state.orphans, system.OrphanValid orphan state.world

theorem initial (world : δ) (start : Start δ α count) (post : Fin count → α → δ → Prop)
    (invariant : system.invariant world)
    (starts : ∀ actor generation, (system.rules actor).Program (fun _ => True) (post actor) (start actor generation)) :
    system.Valid post (State.initial world start) :=
  ⟨invariant, fun actor => (system.rules actor).ofProgram (starts actor 0) invariant trivial,
    by simp [State.initial]⟩

private theorem OrphanValid.advance {orphan : Orphan δ} {before after : δ}
    (valid : system.OrphanValid orphan before) (first : system.invariant before) (last : system.invariant after)
    (moves : system.evolution before after) : system.OrphanValid orphan after := by
  obtain ⟨required, holds, stable, execute⟩ := valid
  exact ⟨required, stable before after first last moves holds, stable, execute⟩

private theorem setActor {post : Fin count → α → δ → Prop} {state : State δ α count}
    (valid : system.Valid post state) (actor : Fin count) (replacement : Actor δ α)
    (sound : (system.rules actor).ActorValid (post actor) replacement state.world) :
    system.Valid post (state.setActor actor replacement) := by
  refine ⟨valid.invariant, ?_, valid.orphans⟩
  intro index
  dsimp only [State.setActor]
  split
  next same => subst index; exact sound
  next => exact valid.actors index

/-- A world update that satisfies all actors' rely relations preserves their
saved reply assertions. This also applies to transport events outside Sim.step. -/
theorem Valid.advance {post : Fin count → α → δ → Prop} {state : State δ α count} {world : δ}
    (valid : system.Valid post state) (postStable : ∀ actor value,
      (system.rules actor).Stable (system.rely actor) (post actor value))
    (invariant : system.invariant world) (moves : system.evolution state.world world)
    (rely : ∀ actor, system.rely actor state.world world) :
    system.Valid post { state with world } :=
  ⟨invariant,
    fun actor => (valid.actors actor).advance _ (postStable actor) valid.invariant invariant (rely actor),
    fun orphan member => (valid.orphans orphan member).advance system valid.invariant invariant moves⟩

/-- One actual simulator event preserves all continuation assertions and the
shared invariant. Starts and atomic contracts are proof obligations about code;
the theorem does not assume safety of execution traces. -/
theorem step_preserves (start : Start δ α count) (post : Fin count → α → δ → Prop)
    (postStable : ∀ actor value, (system.rules actor).Stable (system.rely actor) (post actor value))
    (starts : ∀ actor generation, (system.rules actor).Program (fun _ => True) (post actor) (start actor generation))
    (state after : State δ α count) (event : Event count) (valid : system.Valid post state)
    (executed : Simulation.step start event state = .ok after) :
    system.Valid post after ∧ system.evolution state.world after.world := by
  cases event with
  | commit actor =>
    cases current : state.actors actor <;> simp only [Simulation.step, current] at executed <;> try contradiction
    next remote label operation next =>
      have sound := valid.actors actor
      rw [current] at sound
      obtain ⟨required, reply, holds, contract, continuation⟩ := sound
      obtain ⟨invariant, guarantee, replied⟩ := contract.execute state.world valid.invariant holds
      obtain ⟨moves, rely⟩ := system.compatible actor remote _ _ valid.invariant invariant guarantee
      cases executed
      refine ⟨⟨invariant, ?_, ?_⟩, moves⟩
      · intro index
        dsimp only [State.setActor]
        split
        next same => subst index; exact ⟨reply, replied, contract.replying, continuation⟩
        next different =>
          exact (valid.actors index).advance _ (postStable index) valid.invariant invariant (rely index (.inl different))
      · intro orphan member
        exact (valid.orphans orphan member).advance system valid.invariant invariant moves
  | resume actor =>
    cases current : state.actors actor <;> simp only [Simulation.step, current] at executed <;> try contradiction
    next value next =>
      have sound := valid.actors actor
      rw [current] at sound
      obtain ⟨reply, holds, stable, continuation⟩ := sound
      cases executed
      exact ⟨setActor system valid actor _ ((system.rules actor).ofProgram
        ((system.rules actor).apply next continuation value) valid.invariant holds), system.reflexive _⟩
  | crash actor =>
    cases current : state.actors actor <;> simp only [Simulation.step, current] at executed <;> try contradiction
    · rename_i remote label operation next
      have sound := valid.actors actor
      rw [current] at sound
      obtain ⟨required, reply, holds, contract, continuation⟩ := sound
      cases executed
      have changed := setActor system valid actor .stopped trivial
      refine ⟨⟨valid.invariant, changed.actors, ?_⟩, system.reflexive _⟩
      intro orphan member
      split at member
      next remote =>
        rcases Array.mem_push.mp member with previous | same
        · exact valid.orphans orphan previous
        · subst orphan
          refine ⟨required, holds, contract.orphan remote, ?_⟩
          intro world invariant holds
          obtain ⟨invariant', guarantee, _⟩ := contract.execute world invariant holds
          obtain ⟨moves, rely⟩ := system.compatible actor _ _ _ invariant invariant' guarantee
          exact ⟨invariant', moves, fun other => rely other (.inr remote)⟩
      next => exact valid.orphans orphan member
    · cases executed
      exact ⟨setActor system valid actor .stopped trivial, system.reflexive _⟩
  | restart actor =>
    cases current : state.actors actor <;> simp only [Simulation.step, current] at executed <;> try contradiction
    cases executed
    have changed := setActor system valid actor _ ((system.rules actor).ofProgram
      (starts actor (state.generations actor + 1)) valid.invariant trivial)
    exact ⟨⟨changed.invariant, changed.actors, changed.orphans⟩, system.reflexive _⟩
  | commitOrphan index =>
    simp only [Simulation.step] at executed
    split at executed
    next inside =>
      obtain ⟨required, holds, stable, commit⟩ := valid.orphans _ (Array.getElem_mem inside)
      obtain ⟨invariant, moves, rely⟩ := commit state.world valid.invariant holds
      have advanced := valid.advance system postStable invariant moves rely
      cases executed
      refine ⟨⟨invariant, advanced.actors, ?_⟩, moves⟩
      intro orphan member
      exact advanced.orphans orphan (Array.mem_of_mem_eraseIdx member)
    next => cases executed
  | discardOrphan index =>
    simp only [Simulation.step] at executed
    split at executed
    next inside =>
      cases executed
      refine ⟨⟨valid.invariant, valid.actors, ?_⟩, system.reflexive _⟩
      intro orphan member
      exact valid.orphans orphan (Array.mem_of_mem_eraseIdx member)
    next => cases executed

end System
end LeanCloud.Proofs.SimulationSafety
