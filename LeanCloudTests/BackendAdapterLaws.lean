import LeanCloud.Backend.Check
import LeanCloud.LeaseQueue
import LeanCloudTests.Support

/-! Provider-independent adapter checks. Supply fresh, isolated Db/queue handles.
The exact same observations are interpreted by Backend.Check; the test contains
no PostgreSQL, RabbitMQ, SQS or Service Bus behavior assumptions. -/

namespace LeanCloudTests.BackendAdapterLaws
open Lean LeanCloud Backend

structure Session (ρ : Type) where
  db : LeanCloud.Db Unit IO
  queue : LeaseQueue Unit IO ρ
  receipts : IO.Ref (Array ρ)
  possible : IO.Ref (Array Backend.State)

def Session.open (db : LeanCloud.Db Unit IO) (queue : LeaseQueue Unit IO ρ) : IO (Session ρ) := do
  return ⟨db, queue, ← IO.mkRef #[], ← IO.mkRef #[{}]⟩

private def Session.performRaw (session : Session ρ) : {α : Type} → Request α → IO α
    | _, .get key => (session.db.get key ()).map Prod.fst
    | _, .put key value => (session.db.put key value ()).map Prod.fst
    | _, .enqueue location => (session.queue.enqueue location ()).map Prod.fst
    | _, .dequeue => do
      let (delivery, _) ← session.queue.dequeue ()
      match delivery with
      | none => pure none
      | some (location, receipt) =>
        let receipts ← session.receipts.get
        session.receipts.set (receipts.push receipt)
        pure (some (location, receipts.size))
    | _, .acknowledge id => do
      let some receipt := (← session.receipts.get)[id]?
        | throw (IO.userError "Test referenced an unknown delivery")
      (session.queue.acknowledge receipt ()).map Prod.fst

def Session.perform (session : Session ρ) (operation : Request α) : IO α := do
  let reply ← session.performRaw operation
  let possibilities ← IO.ofExcept (Backend.Check.observe operation reply (← session.possible.get))
  session.possible.set possibilities
  return reply

/-- Generated same-key retries and independently addressed reads, followed by
unordered queue delivery. The bound is a test deadline, not a fairness proof. -/
def run (db : LeanCloud.Db Unit IO) (queue : LeaseQueue Unit IO ρ) (seed : Nat) : IO Unit := do
  let session ← Session.open db queue
  for index in [:32] do
    let key := s!"contract/{seed}/{(index * 17 + seed) % 11}"
    let value := toJson ((index * 17 + seed) % 11)
    let _ ← session.perform (.get key)
    let _ ← session.perform (.put key value)
    let _ ← session.perform (.get key)
    let _ ← session.perform (.put key value)
  for index in [:8] do
    session.perform (.enqueue (Location.root.child index))
  let mut seen : Array Location := #[]
  for _ in [:160] do
    if seen.size == 8 then break
    match ← session.perform .dequeue with
    | none => pure ()
    | some (location, receipt) =>
      unless seen.contains location do seen := seen.push location
      let _ ← session.perform (.acknowledge receipt)
  assertEq seen.size 8 "Queue did not deliver all publications within the test deadline"

end LeanCloudTests.BackendAdapterLaws
