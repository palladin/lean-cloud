import LeanCloud.Proofs.BackendFuelProgram

namespace LeanCloud.Backend.Proofs.Fuel
open Lean LeanEff LeanCloud.Proofs Execution Iteration

/-- Private service-call ids may be renamed when erasing iteration boundaries:
the finite loop can issue its next request before the repeated proof model does.
The operation, reply, owner generation and order of commits are preserved. -/
inductive ContinuationFollows [Codec α] (remaining : Nat) (source : Cloud Replay.M Json) :
    Option (ArrsF Request β Outcome) → Option (ArrsF Request β (Answer α)) → Prop where
  | orphan : ContinuationFollows remaining source none none
  | live {left right}
      (same : ∀ value, Follows (FuelStopped Worker.exhausted)
        (fun returned => Program.ofEff (resume remaining source returned))
        (Program.ofArrs left value) (Program.ofArrs right value)) :
      ContinuationFollows remaining source (some left) (some right)

inductive CallFollows [Codec α] (remaining : Nat → Nat) (source : Cloud Replay.M Json) :
    Call Outcome → Call (Answer α) → Prop where
  | pending {β : Type} (owner : Owner) (operation : Request β) {left right}
      (same : ContinuationFollows (remaining owner.worker) source left right) :
      CallFollows remaining source (.pending owner operation left) (.pending owner operation right)
  | committed {β : Type} (owner : Owner) (operation : Request β) (value : β) {left right}
      (same : ContinuationFollows (remaining owner.worker) source left right) :
      CallFollows remaining source (.committed owner operation value left) (.committed owner operation value right)
  | retired : CallFollows remaining source .retired .retired

theorem CallFollows.caller [Codec α] {remaining source} {left : Call Outcome} {right : Call (Answer α)}
    (same : CallFollows remaining source left right) : left.caller = right.caller := by
  cases same with
  | pending owner operation same | committed owner operation value same => cases same <;> rfl
  | retired => rfl

theorem CallFollows.orphan [Codec α] {remaining source} {left : Call Outcome} {right : Call (Answer α)}
    (same : CallFollows remaining source left right) (owner : Owner) :
    CallFollows remaining source (left.orphan owner) (right.orphan owner) := by
  cases same with
  | pending caller operation same =>
    simp only [Call.orphan]
    split
    · exact .pending _ _ .orphan
    · exact .pending _ _ same
  | committed caller operation value same =>
    simp only [Call.orphan]
    split
    · exact .committed _ _ _ .orphan
    · exact .committed _ _ _ same
  | retired => exact .retired

def WorkerFollows [Codec α] (remaining : Nat → Nat) (source : Cloud Replay.M Json) (mapping : Nat → Nat)
    (calls : Nat) (index : Nat) (worker : Execution.Worker Outcome) (target : Execution.State (Answer α)) : Prop :=
  match worker.status with
  | .stopped => target.workers[index]? = some ⟨worker.attempt, .stopped⟩
  | .waiting id => id < calls ∧ target.workers[index]? = some ⟨worker.attempt, .waiting (mapping id)⟩
  | .finished returned => FuelStopped Worker.exhausted returned ∨
      Continues ⟨index, worker.attempt⟩ (Program.ofEff (resume (remaining index) source returned)) target

structure Related [Codec α] (remaining : Nat → Nat) (source : Cloud Replay.M Json) (mapping : Nat → Nat)
    (before : Execution.State Outcome) (after : Execution.State (Answer α)) : Prop where
  services : before.services = after.services
  size : before.workers.size = after.workers.size
  workers : ∀ (index : Nat) worker, before.workers[index]? = some worker →
    WorkerFollows remaining source mapping before.calls.size index worker after
  calls : ∀ (id : Nat) call, before.calls[id]? = some call →
    ∃ current, after.calls[mapping id]? = some current ∧ CallFollows remaining source call current
  injective : ∀ first last, first < before.calls.size → last < before.calls.size →
    mapping first = mapping last → first = last

theorem Related.mapped_inside [Codec α] {remaining source mapping before after}
    (same : Related (α := α) remaining source mapping before after) {id : Nat} (inside : id < before.calls.size) :
    mapping id < after.calls.size := by
  obtain ⟨call, held, _⟩ := same.calls id before.calls[id] (Array.getElem?_eq_getElem inside)
  exact (Array.getElem?_eq_some_iff.mp held).choose

theorem Continues.frame {owner : Owner} {program : Program α} {before after : Execution.State α}
    (continued : Continues owner program before)
    (worker : after.workers[owner.worker]? = before.workers[owner.worker]?)
    (calls : ∀ (id : Nat) call, before.calls[id]? = some call → after.calls[id]? = some call) :
    Continues owner program after := by
  cases continued with
  | pure held => exact .pure (worker.trans held)
  | request held => exact .request ⟨worker.trans held.1, calls _ _ held.2⟩

theorem WorkerFollows.frame [Codec α] {remaining source firstMap lastMap beforeSize afterSize index worker}
    {before after : Execution.State (Answer α)}
    (same : WorkerFollows remaining source firstMap beforeSize index worker before)
    (larger : beforeSize ≤ afterSize) (mapping : ∀ id, id < beforeSize → lastMap id = firstMap id)
    (held : after.workers[index]? = before.workers[index]?)
    (calls : ∀ (id : Nat) call, before.calls[id]? = some call → after.calls[id]? = some call) :
    WorkerFollows remaining source lastMap afterSize index worker after := by
  simp only [WorkerFollows] at same ⊢
  cases status : worker.status with
  | stopped => simp only [status] at same; exact held.trans same
  | waiting id =>
    simp only [status] at same
    exact ⟨Nat.lt_of_lt_of_le same.1 larger, by rw [mapping id same.1]; exact held.trans same.2⟩
  | finished returned =>
    simp only [status] at same
    exact same.imp_right (fun continued => Continues.frame continued held calls)

end LeanCloud.Backend.Proofs.Fuel
