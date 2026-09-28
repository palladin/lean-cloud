import LeanCloud.Core
import LeanCloud.Db
import LeanCloud.BlobStorage
import LeanCloud.WorkQueue
import LeanCloud.Result

/-! Replay of locations supplied by the environment. Each step reconstructs its
computation and advances one effect, fork, join, or completion. The environment
retains pending work and the final outcome across restarts. -/

namespace LeanCloud.ReplayInterpreter.Internal
open Lean LeanEff

def load [Monad m] (db : Db σ m) (location : Location) :
    ExceptT CloudError (StateT σ m) (Option Result) := do
  let some value ← db.get location.key | return none
  match fromJson? value with
  | .ok result => return some result
  | .error message => throw ⟨.codec, message⟩

def save [Monad m] (db : Db σ m) (location : Location) (result : Result) :
    ExceptT CloudError (StateT σ m) Unit := do
  unless ← db.put location.key (toJson result) do
    throw ⟨.protocol, s!"Db rejected result at {location.key}"⟩

def decode [Monad m] (codec : Codec α) (value : Json) : ExceptT CloudError m α :=
  match codec.decode value with
  | .ok value => pure value
  | .error message => throw ⟨.codec, message⟩

def decodeGroup [Monad m] (codec : Codec α) (count : Nat) (value : Json) :
    ExceptT CloudError m (Array α) := do
  let _ : Codec α := codec
  let values ← decode (inferInstance : Codec (Array α)) value
  if values.size != count then throw ⟨.divergence, "Parallel child count changed"⟩
  return values

/-- Commit a terminal child and wake its parent only when all slots are filled.
Updating the child before its parent permits recovery of either committed prefix. -/
def finish [Monad m] (db : Db σ m) (current : Location) (outcome : Exit) :
    ExceptT CloudError (StateT σ m) StepResult := do
  match ← load db current with
  | none => save db current (.completed outcome)
  | some (.completed recorded) =>
    if recorded != outcome then throw ⟨.divergence, "Completion changed during replay"⟩
  | some (.suspended _) => throw ⟨.divergence, "Expected a completed computation"⟩
  match current.parent? with
  | none => return .done outcome
  | some (parent, index) =>
    let some group ← load db parent | throw ⟨.protocol, "Missing parent suspension"⟩
    let updated ← match Result.recordChild group index outcome with
      | .ok result => pure result
      | .error error => throw error
    save db parent updated
    match updated with
    | .suspended _ => return .runnable #[]
    | .completed _ => return .runnable #[parent]

/-- Reconstruct a selected location. Recorded prefixes consume traversal fuel,
but never call the chooser or repeat primitive effects. -/
def walk [Monad m] (db : Db σ m) (blobs : BlobStorage σ m) (fuel : Nat)
    (program : Cloud m Json) (current target : Location) :
    ExceptT CloudError (StateT σ m) StepResult :=
  match fuel with
  | 0 => throw ⟨.protocol, "Interpreter fuel exhausted"⟩
  | fuel + 1 =>
    match program with
    | EffF.pure value =>
      if current == target then finish db current (.success value)
      else throw ⟨.divergence, "Computation ended before the requested location"⟩
    | .impure request continuation =>
      match request, continuation with
      | .delay, continuation => walk db blobs fuel (ArrsF.apply continuation ()) current target
      | .fail error, _ =>
        if current == target then finish db current (.failure error)
        else throw ⟨.divergence, "Computation ended before the requested location"⟩
      | .choice .., _ => throw ⟨.unsupported, "Choice is not implemented yet"⟩
      | .sequential codec operation, continuation => do
        let outcome ← match ← load db current with
          | some (.completed outcome) => pure outcome
          | some (.suspended _) => throw ⟨.divergence, "Expected a sequential result"⟩
          | none => do
            if current != target then throw ⟨.divergence, "Missing replay result"⟩
            let outcome ← try
              pure (.success (codec.encode (← blobs.execute operation)))
            catch error => pure (.failure error)
            save db current (.completed outcome)
            pure outcome
        match outcome with
        | .success value =>
          let value ← decode codec value
          if current == target then return .runnable #[current.next]
          else walk db blobs fuel (ArrsF.apply continuation value) current.next target
        | outcome =>
          if current == target then finish db current outcome
          else throw ⟨.divergence, "Computation ended before the requested location"⟩
      | .parallel codec count branches, continuation => do
        let existing ← load db current
        if current == target && existing.isNone then
          save db current (Result.settle (Array.replicate count none))
          return .runnable (if count == 0 then #[current] else Array.ofFn fun i : Fin count => current.child i.val)
        let some result := existing | throw ⟨.divergence, "Missing replay suspension"⟩
        match result with
        | .completed (.success value) =>
          let values ← decodeGroup codec count value
          if current == target then return .runnable #[current.next]
          else walk db blobs fuel (ArrsF.apply continuation values) current.next target
        | .completed outcome =>
          if current == target then finish db current outcome
          else throw ⟨.divergence, "Computation ended before the requested location"⟩
        | .suspended children =>
          if children.size != count then throw ⟨.divergence, "Parallel child count changed"⟩
          if current == target then
            return .runnable ((Array.ofFn fun i : Fin count => i.val).filterMap fun i =>
              if children[i]!.isNone then some (current.child i) else none)
          if !current.entersChild target then throw ⟨.divergence, "Earlier suspension has no complete result"⟩
          let index := target[current.size]!.1
          if inside : index < count then
            walk db blobs fuel (codec.encode <$> branches ⟨index, inside⟩) (current.child index) target
          else throw ⟨.protocol, "Child index is outside the group"⟩

def step [Monad m] (db : Db σ m) (blobs : BlobStorage σ m) (fuel : Nat)
    (root : Cloud m Json) (location : Location) : ExceptT CloudError (StateT σ m) StepResult := do
  if location.isEmpty || location[0]!.1 != 0 then
    throw ⟨.protocol, "A location must begin with the root branch 0"⟩
  -- A crash can leave the last child queued after its parent result was saved.
  -- Retry the queue update by publishing the parent's join, without descending
  -- through a group whose result has already replaced its suspended children.
  if let some (parent, _) := location.parent? then
    if let some (.completed _) ← load db parent then
      return .runnable #[parent]
  walk db blobs fuel root Location.root location

def result [Monad m] [codec : Codec α] (outcome : Exit) : ExceptT CloudError m α :=
  match outcome with
  | .success value => decode codec value
  | .failure error => throw error
  | .cancelled _ => throw ⟨.unsupported, "Cancellation is not implemented yet"⟩

def run [Monad m] [Codec α] (db : Db σ m) (blobs : BlobStorage σ m) (queue : WorkQueue σ m) (fuel : Nat)
    (root : Cloud m Json) : ExceptT CloudError (StateT σ m) α :=
  match fuel with
  | 0 => throw ⟨.protocol, "Interpreter fuel exhausted"⟩
  | fuel + 1 => do
    match ← queue.next with
    | .completed outcome => result outcome
    | .idle => run db blobs queue fuel root
    | .item location =>
      let update ← step db blobs (fuel + 1) root location
      queue.complete location update
      match update with
      | .done outcome => result outcome
      | .runnable _ => run db blobs queue fuel root

end LeanCloud.ReplayInterpreter.Internal

namespace LeanCloud
open Lean ReplayInterpreter.Internal

/-- Run work supplied by the environment until the root completes. Fuel bounds
queue polls and each reconstruction traversal. A new environment starts with the
root item; a restart reuses the same queue, journal, program, and input. -/
def interpret {σ ι α : Type} {m : Type → Type} [Monad m] [Codec α]
    (db : Db σ m) (blobs : BlobStorage σ m) (queue : WorkQueue σ m) (fuel : Nat)
    (program : ι → Cloud m α) (input : ι) : ExceptT CloudError (StateT σ m) α :=
  run db blobs queue fuel (Codec.encode <$> program input)

end LeanCloud
