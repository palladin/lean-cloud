import LeanCloud.Backend.Model
import LeanEff.Core

/-!
Backend requests outlive their callers. The scheduler independently commits a
request, delivers its reply, or crashes/replaces a worker. This is execution of
service requests; Cloud continues to use the existing replay interpreter.
-/

namespace LeanCloud.Backend
open LeanEff

abbrev M := EffF Request

def request (operation : Request α) : M α := EffF.send operation

namespace Execution

structure Owner where
  worker : Nat
  attempt : Nat
  deriving Repr, BEq, DecidableEq

inductive Status (α : Type) where
  | waiting (call : Nat)
  | stopped
  | finished (value : α)

structure Worker (α : Type) where
  attempt : Nat := 0
  status : Status α

/-- A continuation is volatile; the already-issued request is not. -/
inductive Call (α : Type) where
  | pending {β : Type} (owner : Owner) (operation : Request β)
      (next : Option (ArrsF Request β α))
  | committed {β : Type} (owner : Owner) (operation : Request β) (value : β)
      (next : Option (ArrsF Request β α))
  | retired

def Call.orphan (owner : Owner) : Call α → Call α
  | .pending caller operation next => .pending caller operation (if caller == owner then none else next)
  | .committed caller operation value next =>
      .committed caller operation value (if caller == owner then none else next)
  | .retired => .retired

structure State (α : Type) where
  services : Backend.State := {}
  workers : Array (Worker α) := #[]
  calls : Array (Call α) := #[]

/-- Pure reduction ends at the next service request. Each request is assigned
one identity before the environment is allowed to commit it. -/
def activate (owner : Owner) (program : M α) (state : State α) : State α :=
  match program with
  | .pure value => { state with workers := state.workers.setIfInBounds owner.worker ⟨owner.attempt, .finished value⟩ }
  | .impure operation next =>
      { state with
        workers := state.workers.setIfInBounds owner.worker ⟨owner.attempt, .waiting state.calls.size⟩
        calls := state.calls.push (.pending owner operation (some next)) }

def initial (services : Backend.State) (programs : Array (M α)) : State α :=
  let empty : State α := { services, workers := programs.map fun _ => ⟨0, .stopped⟩ }
  (List.range programs.size).foldl (fun state worker =>
    match programs[worker]? with
    | none => state
    | some program => activate ⟨worker, 0⟩ program state) empty

inductive Event where
  | commit (call : Nat) (decision : Decision := {})
  | reply (call : Nat)
  | crash (worker : Nat)
  | restart (worker : Nat)
  deriving Repr, BEq

def owns (owner : Owner) (call : Nat) (state : State α) : Bool :=
  match state.workers[owner.worker]? with
  | some ⟨attempt, .waiting expected⟩ => attempt == owner.attempt && expected == call
  | _ => false

def step (programs : Array (M α)) (event : Event) (state : State α) : Except String (State α) := do
  match event with
  | .commit id decision =>
    let some (.pending owner operation next) := state.calls[id]?
      | throw "Commit requires a pending request"
    match execute decision operation state.services with
    | .error error => throw error
    | .ok (value, services) =>
      return { state with
        services := services
        calls := state.calls.setIfInBounds id (.committed owner operation value next) }
  | .reply id =>
    let some (.committed owner _ value next) := state.calls[id]?
      | throw "Reply requires a committed request"
    let retired := { state with calls := state.calls.setIfInBounds id .retired }
    match next with
    | none => return retired
    | some next =>
      unless owns owner id state do throw "Reply belongs to an obsolete attempt"
      return activate owner (ArrsF.apply next value) retired
  | .crash id =>
    let some worker := state.workers[id]? | throw "Unknown worker"
    match worker.status with
    | .waiting _ =>
      return { state with
        workers := state.workers.setIfInBounds id { worker with status := .stopped }
        calls := state.calls.map (Call.orphan ⟨id, worker.attempt⟩) }
    | _ => throw "Crash requires a running worker"
  | .restart id =>
    let some worker := state.workers[id]? | throw "Unknown worker"
    let some program := programs[id]? | throw "Missing worker entry point"
    match worker.status with
    | .stopped => return activate ⟨id, worker.attempt + 1⟩ program state
    | _ => throw "Restart requires a stopped worker"

def run (programs : Array (M α)) (events : List Event) (state : State α) : Except String (State α) :=
  events.foldlM (fun state event => step programs event state) state

/-- Only a committed service operation changes durable state. In particular,
crash, replacement and reply delivery cannot roll back a completed write. -/
theorem activate_preserves (owner : Owner) (program : M α) (state : State α) :
    (activate owner program state).services = state.services := by
  cases program <;> rfl

theorem initial_preserves (services : Backend.State) (programs : Array (M α)) :
    (initial services programs).services = services := by
  have fold (indices : List Nat) (state : State α) :
      (indices.foldl (fun current worker =>
        match programs[worker]? with
        | none => current
        | some program => activate ⟨worker, 0⟩ program current) state).services = state.services := by
    induction indices generalizing state with
    | nil => rfl
    | cons worker rest ih =>
      rw [List.foldl_cons, ih]
      cases programs[worker]? with
      | none => rfl
      | some program => exact activate_preserves _ _ _
  exact fold _ _

theorem crash_preserves (programs : Array (M α)) (worker : Nat) (before after : State α)
    (executed : step programs (.crash worker) before = .ok after) :
    after.services = before.services := by
  simp only [step] at executed
  split at executed <;> try cases executed
  split at executed <;> cases executed
  rfl

theorem restart_preserves (programs : Array (M α)) (worker : Nat) (before after : State α)
    (executed : step programs (.restart worker) before = .ok after) :
    after.services = before.services := by
  simp only [step] at executed
  split at executed <;> try cases executed
  split at executed <;> try cases executed
  split at executed <;> cases executed
  exact activate_preserves _ _ _

theorem reply_preserves (programs : Array (M α)) (call : Nat) (before after : State α)
    (executed : step programs (.reply call) before = .ok after) :
    after.services = before.services := by
  simp only [step] at executed
  split at executed <;> try cases executed
  split at executed
  · cases executed; rfl
  · split at executed
    · cases executed
      exact activate_preserves _ _ _
    · cases executed

/-- Every durable change has a typed, previously issued service request as
its cause. This includes commits whose worker has crashed or been replaced. -/
theorem commit_sound (programs : Array (M α)) (call : Nat) (decision : Decision)
    (before after : State α)
    (executed : step programs (.commit call decision) before = .ok after) :
    ∃ (β : Type) (owner : Owner) (operation : Request β)
      (next : Option (ArrsF Request β α)) (value : β),
      before.calls[call]? = some (.pending owner operation next) ∧
      Commits before.services operation value after.services := by
  simp only [step] at executed
  split at executed
  next β owner operation next found =>
    cases result : execute decision operation before.services with
    | error error => simp [result] at executed
    | ok returned =>
      obtain ⟨value, services⟩ := returned
      simp only [result] at executed
      cases executed
      exact ⟨β, owner, operation, next, value, found,
        execute_sound decision operation before.services services value result⟩
  next => cases executed

/-- A service history may stutter between committed primitives. The relation
contains no workflow-specific correctness or completion premise. -/
def ServiceStep (before after : Backend.State) : Prop :=
  after = before ∨ ∃ (β : Type) (operation : Request β) (value : β),
    Commits before operation value after

theorem step_sound (programs : Array (M α)) (event : Event) (before after : State α)
    (executed : step programs event before = .ok after) :
    ServiceStep before.services after.services := by
  cases event with
  | commit call decision =>
    obtain ⟨β, _, operation, _, value, _, committed⟩ := commit_sound programs call decision before after executed
    exact .inr ⟨β, operation, value, committed⟩
  | reply call => exact .inl (reply_preserves programs call before after executed)
  | crash worker => exact .inl (crash_preserves programs worker before after executed)
  | restart worker => exact .inl (restart_preserves programs worker before after executed)

/-- Observable scheduling actions. Queue-selection decisions belong to an
executable instance, not to the abstract execution contract. -/
inductive Action where
  | commit (call : Nat)
  | reply (call : Nat)
  | crash (worker : Nat)
  | restart (worker : Nat)
  deriving Repr, BEq, DecidableEq

def Event.action : Event → Action
  | .commit call _ => .commit call
  | .reply call => .reply call
  | .crash worker => .crash worker
  | .restart worker => .restart worker

/-- Contract-based execution. A committed reply may be any reply allowed by
the service laws; no executable selection policy is assumed. Local actions use
the same continuation, crash and replacement code as the test driver. -/
inductive Transition (programs : Array (M α)) : Action → State α → State α → Prop where
  | commit {β : Type} {before : State α} {call : Nat} {owner : Owner}
      {operation : Request β} {next : Option (ArrsF Request β α)} {value : β} {services : Backend.State}
      (issued : before.calls[call]? = some (.pending owner operation next))
      (lawful : Commits before.services operation value services) :
      Transition programs (.commit call) before
        { before with services, calls := before.calls.setIfInBounds call (.committed owner operation value next) }
  | reply {call before after}
      (executed : step programs (.reply call) before = .ok after) :
      Transition programs (.reply call) before after
  | crash {worker before after}
      (executed : step programs (.crash worker) before = .ok after) :
      Transition programs (.crash worker) before after
  | restart {worker before after}
      (executed : step programs (.restart worker) before = .ok after) :
      Transition programs (.restart worker) before after

/-- The executable scheduler is one instance of the abstract execution model. -/
theorem step_refines (programs : Array (M α)) (event : Event) (before after : State α)
    (executed : step programs event before = .ok after) :
    Transition programs event.action before after := by
  cases event with
  | reply call => exact .reply executed
  | crash worker => exact .crash executed
  | restart worker => exact .restart executed
  | commit call decision =>
    simp only [step] at executed
    split at executed
    next β owner operation next found =>
      cases result : execute decision operation before.services with
      | error error => simp [result] at executed
      | ok returned =>
        obtain ⟨value, services⟩ := returned
        simp only [result] at executed
        cases executed
        exact .commit found (execute_sound decision operation before.services services value result)
    next => cases executed

/-- Any representation satisfying the primitive laws can supply this commit.
There is no assumption about a workflow result or the caller's continuation. -/
theorem lawful_commit (laws : Laws δ) (programs : Array (M α))
    (before : State α) (durable after : δ) (call : Nat) (owner : Owner)
    (operation : Request β) (next : Option (ArrsF Request β α)) (value : β)
    (represented : before.services = laws.view durable)
    (issued : before.calls[call]? = some (.pending owner operation next))
    (performed : laws.operation operation durable value after) :
    Transition programs (.commit call) before
      { before with
        services := laws.view after
        calls := before.calls.setIfInBounds call (.committed owner operation value next) } := by
  apply Transition.commit issued
  rw [represented]
  exact laws.commits operation durable value after performed

theorem Transition.service_sound {programs : Array (M α)} {action before after}
    (transition : Transition programs action before after) :
    ServiceStep before.services after.services := by
  cases transition with
  | commit issued lawful => exact .inr ⟨_, _, _, lawful⟩
  | reply executed => exact .inl (reply_preserves programs _ _ _ executed)
  | crash executed => exact .inl (crash_preserves programs _ _ _ executed)
  | restart executed => exact .inl (restart_preserves programs _ _ _ executed)

end Execution
end LeanCloud.Backend
