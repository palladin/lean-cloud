import LeanCloud.Proofs.BackendFuelCrash

namespace LeanCloud.Backend.Proofs.Fuel
open Lean LeanEff LeanCloud.Proofs Execution Iteration

theorem CallFollows.rebudget [Codec α] {remaining updated source}
    {left : Call Outcome} {right : Call (Answer α)}
    (same : CallFollows remaining source left right)
    (unchanged : ∀ owner, left.caller = some owner → updated owner.worker = remaining owner.worker) :
    CallFollows updated source left right := by
  cases same with
  | pending owner operation rest =>
    cases rest with
    | orphan => exact .pending _ _ .orphan
    | live follows =>
      apply CallFollows.pending
      rw [unchanged owner rfl]
      exact .live follows
  | committed owner operation value rest =>
    cases rest with
    | orphan => exact .committed _ _ _ .orphan
    | live follows =>
      apply CallFollows.committed
      rw [unchanged owner rfl]
      exact .live follows
  | retired => exact .retired

theorem WorkerFollows.rebudget [Codec α] {remaining updated source mapping count index worker}
    {after : Execution.State (Answer α)}
    (same : WorkerFollows remaining source mapping count index worker after)
    (unchanged : updated index = remaining index) :
    WorkerFollows updated source mapping count index worker after := by
  unfold WorkerFollows at same ⊢
  rw [unchanged]
  exact same

theorem Linked.inactive_caller {before : Execution.State α} (linked : Linked before)
    {index : Nat} {worker : Execution.Worker α}
    (held : before.workers[index]? = some worker)
    (inactive : ∀ id, worker.status ≠ .waiting id)
    {id : Nat} {call : Call α} (stored : before.calls[id]? = some call) {owner : Owner}
    (live : call.caller = some owner) : owner.worker ≠ index := by
  intro equal
  have waiting := linked id call stored owner live
  rw [equal, held] at waiting
  exact inactive id (congrArg Execution.Worker.status (Option.some.inj waiting))

theorem Related.reset [Codec α] {remaining source mapping before after}
    (same : Related (α := α) remaining source mapping before after) (linked : Linked before)
    {index attempt} (stopped : before.workers[index]? = some ⟨attempt, .stopped⟩) (budget : Nat) :
    Related (extend remaining index budget) source mapping before after := by
  constructor
  · exact same.services
  · exact same.size
  · intro other worker held
    by_cases equal : other = index
    · subst other
      rw [stopped] at held
      cases held
      exact same.workers index _ stopped
    · exact (same.workers other worker held).rebudget (by simp [extend, equal])
  · intro id call held
    obtain ⟨current, stored, follows⟩ := same.calls id call held
    refine ⟨current, stored, follows.rebudget ?_⟩
    intro owner live
    have different := Linked.inactive_caller linked stopped (by intro _ impossible; cases impossible) held live
    simp [extend, different]
  · exact same.injective

theorem Related.restart [Codec α] {remaining source mapping before after}
    (same : Related (α := α) remaining source mapping before after) (linked : Linked before)
    (traversal : Nat) (supported : PureProgram source)
    (count : Nat) (budget : Nat → Nat) (index : Nat)
    (enough : traversal ≤ budget index + 1)
    {final : Execution.State Outcome}
    (executed : step (Array.replicate count (Iteration.program traversal source)) (.restart index) before = .ok final) :
    ∃ target lastMap, Transition ((Array.range count).map fun index => loop (α := α) (budget index + 1) source)
        (.restart index) after target ∧
      Related (extend remaining index (budget index)) source lastMap final target := by
  simp only [step] at executed
  split at executed <;> try contradiction
  rename_i worker held
  split at executed <;> try contradiction
  rename_i actual entry
  split at executed <;> try contradiction
  rename_i stopped
  cases executed
  have sourceEntry := (Array.mem_replicate.mp (Array.mem_of_getElem? entry)).2
  subst actual
  have inside : index < count := by simpa using (Array.getElem?_eq_some_iff.mp entry).choose
  have stoppedEq : before.workers[index]? = some ⟨worker.attempt, .stopped⟩ := by
    rw [held]; congr; cases worker; simp_all
  have reset := same.reset linked stoppedEq (budget index)
  obtain ⟨lastMap, activated⟩ := reset.activate ⟨index, worker.attempt + 1⟩
    (Iteration.program traversal source) (loop (budget index + 1) source)
    (Array.getElem?_eq_some_iff.mp held).choose
    (by simpa only [extend, ↓reduceIte] using Follows.entry (α := α) traversal (budget index) source supported enough)
  refine ⟨Execution.activate ⟨index, worker.attempt + 1⟩ (loop (budget index + 1) source) after,
    lastMap, .restart ?_, activated⟩
  have targetStopped := same.workers index _ stoppedEq
  change after.workers[index]? = some ⟨worker.attempt, .stopped⟩ at targetStopped
  simp [step, targetStopped, inside]
  rfl

end LeanCloud.Backend.Proofs.Fuel
