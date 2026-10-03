import LeanCloud.DirectInterpreter
import LeanCloud.ReplayInterpreter
import LeanCloud.Proofs.Model

/-! Pure reference execution of the ordinary interpreters. The database is a
key/value function and work is a list. One worker always selects the head; new
locations go before the remaining work. There are no leases, clocks, or IO. -/

namespace LeanCloud.Pure
open Lean

structure State where
  journal : Proofs.Journal := Proofs.Journal.empty
  pending : List Location := [Location.root]
  completed : Option Exit := none

def initial : State := {}

def db : Db State Id where
  get key state := (state.journal key, state)
  put key value state :=
    (true, {state with journal := state.journal.write key value})

def queue : WorkQueue State Id where
  next state :=
    let work := match state.completed with
      | some outcome => Work.completed outcome
      | none => match state.pending with
        | [] => .idle
        | location :: _ => .item location
    (work, state)
  complete location response state :=
    ((), match response with
      | .runnable locations =>
        {state with pending := locations.toList ++ state.pending.erase location}
      | .done outcome => {state with pending := [], completed := some outcome})

/-- Blob operations are outside the pure fragment. -/
def noBlobs : BlobStorage σ Id where
  putBlob _ := throw ⟨.unsupported, "Blob operations are outside the pure fragment"⟩
  readBlob _ := throw ⟨.unsupported, "Blob operations are outside the pure fragment"⟩
  resolveBlob _ := throw ⟨.unsupported, "Blob operations are outside the pure fragment"⟩

/-- Direct evaluation needs no execution records or fuel. -/
def direct (program : ι → Cloud Id α) (input : ι) : Except CloudError α :=
  ((DirectInterpreter.interpret (noBlobs : BlobStorage Unit Id) program input).run ()).1

/-- Resume the same program and input using the saved records and work list.
Returning the state makes suspension and location-based resumption inspectable. -/
def resume [Codec α] (fuel : Nat) (program : ι → Cloud Id α) (input : ι)
    (state : State) : Except CloudError α × State :=
  (LeanCloud.interpret db noBlobs queue fuel program input).run state

/-- Start with an empty database and the root location. The equivalence theorem
covers ordinary pure values, delay, failure, and parallel, with lawful codecs. -/
def replay [Codec α] (fuel : Nat) (program : ι → Cloud Id α) (input : ι) : Except CloudError α :=
  (resume fuel program input initial).1

end LeanCloud.Pure
