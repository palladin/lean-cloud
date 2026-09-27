import LeanCloud.Core
import LeanCloud.Location
import LeanCloud.Storage

/-! Location-directed replay interpreter.
Each step reconstructs execution from recorded results at a location, then advances
until suspension or completion. Continuations are rebuilt through replay. -/

namespace LeanCloud
open Lean LeanEff

/-- Only outcomes and partial groups are stored; computations remain local. -/
inductive Result where
  | completed (outcome : Exit)
  | suspended (children : Array (Option Exit))
  deriving Repr, BEq, ToJson, FromJson

namespace Result

/-- Parallel resumes once every child has a result, in the original array order. -/
def settle (children : Array (Option Exit)) : Result :=
  match children.mapM id with
  | none => .suspended children
  | some outcomes =>
    match outcomes.mapM (fun outcome => match outcome with
      | .success value => Except.ok value
      | outcome => Except.error outcome) with
    | .ok values => .completed (.success (Json.arr values))
    | .error outcome => .completed outcome

def recordChild (result : Result) (index : Nat) (outcome : Exit) : Except CloudError Result := do
  match result with
  | .completed _ => return result
  | .suspended children =>
    if index ≥ children.size then throw ⟨.protocol, "Child is outside the suspended group"⟩
    if let some existing := children[index]! then
      if existing == outcome then return result
      throw ⟨.divergence, "Child completion changed during replay"⟩
    return settle (children.set! index (some outcome))

end Result

open Result (settle recordChild)

namespace ReplayInterpreter.Internal

def load [Monad m] (storage : Storage σ m) (location : Location) :
    ExceptT CloudError (StateT σ m) (Option Result) := do
  let some value ← storage.get location.key | return none
  match fromJson? value with
  | .ok result => return some result
  | .error message => throw ⟨.codec, message⟩

def save [Monad m] (storage : Storage σ m) (location : Location) (result : Result) :
    ExceptT CloudError (StateT σ m) Unit := do
  unless ← storage.put location.key (toJson result) do
    throw ⟨.protocol, s!"Storage rejected result at {location.key}"⟩

def decode [Monad m] (codec : Codec α) (value : Json) : ExceptT CloudError m α :=
  match codec.decode value with
  | .ok value => pure value
  | .error message => throw ⟨.codec, message⟩

/-- A completed value or the location of an unresolved parallel group. -/
inductive StepResult where
  | done (value : Json) (location : Location) (remainingFuel : Nat)
  | suspended (location : Location) (remainingFuel : Nat)
  deriving Repr

/-- Reconstruct the requested location, then run to the next unresolved group.
The loop uses encoded branch results so descending into a child can change its
Lean result type without changing the loop's type. Parent code is rebuilt from root.
Running the action returns `m (Except CloudError StepResult × σ)`, retaining storage
updates even when stepping ends in an error. -/
def step {σ : Type} {m : Type → Type} [Monad m] (storage : Storage σ m)
    (fuel : Nat) (root : Cloud m Json) (location : Location) :
    ExceptT CloudError (StateT σ m) StepResult := do
  if location.isEmpty || location[0]!.1 != 0 then
    throw ⟨.protocol, "A location must begin with the root branch 0"⟩
  walk fuel root Location.root location
where
  walk (fuel : Nat) (program : Cloud m Json) (current target : Location) :
      ExceptT CloudError (StateT σ m) StepResult :=
    match fuel with
    | 0 => throw ⟨.protocol, "Interpreter fuel exhausted"⟩
    | fuel + 1 =>
      let finish (outcome : Exit) (target : Location) : ExceptT CloudError (StateT σ m) StepResult := do
        if current.before target then
          throw (⟨.divergence, "Computation ended before the requested location"⟩ : CloudError)
        match ← load storage current with
        | none => save storage current (.completed outcome)
        | some (.completed recorded) =>
          if recorded != outcome then
            throw ⟨.divergence, "Completion changed during replay"⟩
        | some (.suspended ..) => throw ⟨.divergence, "Expected a completed computation"⟩
        match current.parent? with
        | none =>
          match outcome with
          | .success value => return StepResult.done value current fuel
          | .failure error => throw error
          | .cancelled _ => throw ⟨.unsupported, "Cancellation is not implemented yet"⟩
        | some (parent, index) =>
          let some group ← load storage parent | throw ⟨.protocol, "Missing parent suspension"⟩
          let updated ← match recordChild group index outcome with
            | .ok value => pure value
            | .error error => throw error
          save storage parent updated
          match updated with
          | .suspended _ => return StepResult.suspended parent fuel
          | .completed _ =>
            -- Rebuilding restores the parent's lexical environment and continuation.
            walk fuel root Location.root parent

      let sequential {β : Type} (request : Operation m β) (codec : Codec β)
          (resume : β → Cloud m Json) : ExceptT CloudError (StateT σ m) StepResult := do
        let outcome ← match ← load storage current with
          | some (.completed outcome) => pure outcome
          | some (.suspended ..) => throw ⟨.divergence, "Expected a sequential result"⟩
          | none => do
            if current.before target then throw ⟨.divergence, "Missing replay result"⟩
            let outcome ← try
              pure (.success (codec.encode (← storage.execute request)))
            catch error => pure (.failure error)
            save storage current (.completed outcome)
            pure outcome
        match outcome with
        | .success value =>
          let value ← decode codec value
          walk fuel (resume value) current.next target
        | outcome => finish outcome target

      let parallel {β : Type} (codec : Codec β) (count : Nat)
          (branches : Fin count → Cloud m β) (resume : Array β → Cloud m Json) :
          ExceptT CloudError (StateT σ m) StepResult := do
        if current.entersChild target && target[current.size]!.1 ≥ count then
          throw ⟨.protocol, "Child index is outside the group"⟩
        let result ← match ← load storage current with
          | some result => pure result
          | none => do
            if current.before target then throw ⟨.divergence, "Missing replay suspension"⟩
            let result := settle (Array.replicate count none)
            save storage current result
            pure result
        match result with
        | .completed (.success value) =>
          let _ : Codec β := codec
          let value ← decode (inferInstance : Codec (Array β)) value
          -- A completed ancestor group no longer needs its requested child resumed.
          let target := if current.entersChild target then current.next else target
          walk fuel (resume value) current.next target
        | .completed outcome =>
          finish outcome (if current.entersChild target then current else target)
        | .suspended children =>
          if children.size != count then
            throw ⟨.divergence, "Parallel child count changed"⟩
          if current.entersChild target then
            let index := target[current.size]!.1
            if h : index < count then
              walk fuel (codec.encode <$> branches ⟨index, h⟩) (current.child index) target
            else throw ⟨.protocol, "Child index is outside the group"⟩
          else if current.before target then
            throw ⟨.divergence, "Earlier suspension has no complete result"⟩
          else return StepResult.suspended current fuel

      match program with
      | .pure value => finish (.success value) target
      | .impure request continuation =>
        match request, continuation with
        | .delay, continuation => walk fuel (ArrsF.apply continuation ()) current target
        | .fail error, _ => finish (.failure error) target
        | .parallel codec count branches, continuation =>
          parallel codec count branches (ArrsF.apply continuation)
        | .choice .., _ => throw ⟨.unsupported, "Choice is not implemented yet"⟩
        | .sequential codec operation, continuation =>
          sequential operation codec (ArrsF.apply continuation)

end ReplayInterpreter.Internal

open ReplayInterpreter.Internal

/-- Run a program to its final result, driving unfinished parallel children in array
order. Suspension and replay locations stay internal. Running with an initial storage
state returns `m (Except CloudError α × σ)`, preserving writes even on failure. -/
def interpret {σ ι α : Type} {m : Type → Type} [Monad m] [Codec α]
    (storage : Storage σ m) (fuel : Nat) (program : ι → Cloud m α) (input : ι) :
    ExceptT CloudError (StateT σ m) α :=
  run fuel (Codec.encode <$> program input) Location.root
where
  run (fuel : Nat) (root : Cloud m Json) (location : Location) :
      ExceptT CloudError (StateT σ m) α := do
    match ← step storage fuel root location with
    | .done value _ _ => decode (inferInstance : Codec α) value
    | .suspended location remainingFuel =>
      let nextLocation ← match ← load storage location with
        | some (.suspended children) =>
          let some index := children.findIdx? Option.isNone
            | throw ⟨.protocol, "Suspended parallel has no unfinished child"⟩
          pure (location.child index)
        | some (.completed _) => pure location
        | none => throw ⟨.protocol, "Missing parallel suspension"⟩
      if _h : remainingFuel < fuel then
        run remainingFuel root nextLocation
      else
        throw ⟨.protocol, "Step did not consume fuel"⟩
  termination_by fuel
  decreasing_by exact _h

end LeanCloud
