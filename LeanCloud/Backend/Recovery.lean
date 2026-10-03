import LeanCloud.Backend.Execution

/-! Recovery and fairness are obligations of the environment. They mention
enabled requests, replies, worker replacement and unsettled publications, never
the expected workflow output. Safety does not require any of these assumptions.
-/

namespace LeanCloud.Backend.Execution

/-- Stuttering permits service downtime and ordinary scheduler delay. -/
structure Trace (programs : Array (Backend.M α)) where
  states : Nat → State α
  events : Nat → Option Action
  execution : ∀ n,
    match events n with
    | none => states (n + 1) = states n
    | some action => Transition programs action (states n) (states (n + 1))

def Pending (state : State α) (call : Nat) : Prop :=
  ∃ (β : Type) (owner : Owner) (operation : Request β) (next : LeanEff.ArrsF Request β α),
    state.calls[call]? = some (.pending owner operation (some next))

def Responding (state : State α) (call : Nat) : Prop :=
  ∃ (β : Type) (owner : Owner) (operation : Request β) (value : β) (next : LeanEff.ArrsF Request β α),
    state.calls[call]? = some (.committed owner operation value (some next))

def Stopped (state : State α) (worker : Nat) : Prop :=
  ∃ attempt, state.workers[worker]? = some ⟨attempt, .stopped⟩

/-- A permanently enabled request, reply or replacement cannot be postponed
forever. Orphaned requests need not receive replies. Their late commits remain
legal even though fairness does not force them. -/
structure WeaklyFair (trace : Trace programs) : Prop where
  commit : ∀ call cut, (∀ n, cut ≤ n → Pending (trace.states n) call) →
    ∃ n, cut ≤ n ∧ trace.events n = some (.commit call)
  reply : ∀ call cut, (∀ n, cut ≤ n → Responding (trace.states n) call) →
    ∃ n, cut ≤ n ∧ trace.events n = some (.reply call)
  restart : ∀ worker cut, (∀ n, cut ≤ n → Stopped (trace.states n) worker) →
    ∃ n, cut ≤ n ∧ trace.events n = some (.restart worker)

/-- Consumers issue arbitrarily late dequeue calls. Replies may be empty;
selection fairness is a separate service obligation. -/
def PollingForever (states : Nat → State α) (events : Nat → Option Action) : Prop :=
  ∀ cut, ∃ time call owner reply next, cut ≤ time ∧ events time = some (.commit call) ∧
    (states (time + 1)).calls[call]? = some (.committed owner .dequeue reply next)

/-- With continuing consumer demand, every accepted, unsettled publication is
eventually selected or settled. No delivery is owed after consumers stop.
An acknowledged publication may still be redelivered, but owes no further
delivery. Retention/dead-letter recovery is required to uphold this obligation. -/
def FairDelivery (trace : Trace programs) : Prop :=
  PollingForever trace.states trace.events →
  ∀ cut id message,
    (trace.states cut).services.queue.messages[id]? = some message →
    message.acknowledged = false →
    ∃ n, cut ≤ n ∧
      ((∃ settled, (trace.states n).services.queue.messages[id]? = some settled ∧
          settled.acknowledged = true) ∨
       ∃ call owner next location receipt,
         trace.events n = some (.commit call) ∧
         (trace.states (n + 1)).calls[call]? =
           some (.committed owner .dequeue (some (location, receipt)) next) ∧
         (trace.states (n + 1)).services.queue.receipts[receipt]? = some id)

/-- Logical slots may be backed by replacement containers. This initial
recovery contract permits arbitrarily many finite crashes and imposes no bound
on restart delay. Availability and sufficient attempt fuel remain explicit. -/
structure Recovery (trace : Trace programs) where
  nonempty : 0 < programs.size
  stableFrom : Nat
  crashesStop : ∀ n worker, stableFrom ≤ n → trace.events n ≠ some (.crash worker)
  workers : WeaklyFair trace
  delivery : FairDelivery trace

end LeanCloud.Backend.Execution
