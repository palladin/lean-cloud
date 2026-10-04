import LeanCloud.Core
import LeanCloud.BlobStorage
import LeanCloud.ReplayStore
import LeanCloud.Coordination

/-! A worker reconstructs an assignment from the root, then executes until the
next fork or branch completion. Sequential results and joined arrays are immutable
global records. Partial joins and assignment ownership live only in the scheduler. -/

namespace LeanCloud.ReplayInterpreter
open Lean LeanEff

/-- Wait for every child, then select the first error in source order, exactly
as the direct interpreter does. The scheduler never performs this reduction. -/
def collect (children : Array Exit) : Exit :=
  match children.mapM fun outcome => match outcome with
      | .success value => Except.ok value
      | other => Except.error other with
  | .ok values => .success (Json.arr values)
  | .error outcome => outcome

-- Stable internal names let proofs unfold the actual interpreter helpers.
namespace Internal

def decode [Monad m] (codec : Codec α) (value : Json) : ExceptT CloudError m α :=
  match codec.decode value with
  | .ok value => pure value
  | .error message => throw ⟨.codec, message⟩

def decodeGroup [Monad m] (codec : Codec α) (count : Nat) (value : Json) :
    ExceptT CloudError m (Array α) := do
  let _ : Codec α := codec
  let values ← decode (inferInstance : Codec (Array α)) value
  unless values.size == count do throw ⟨.divergence, "Parallel child count changed"⟩
  return values

def request (codec : Codec α) : Operation m α → Request
  | .exec label _ => ⟨"exec", codec.schema, toJson label⟩
  | .putBlob bytes => ⟨"putBlob", codec.schema, encodeBytes bytes⟩
  | .readBlob ref => ⟨"readBlob", codec.schema, toJson ref⟩
  | .resolveBlob name => ⟨"resolveBlob", codec.schema, toJson name⟩

def check [Monad m] (expected : Request) (record : ReplayRecord) :
    ExceptT CloudError m Exit := do
  unless record.request == expected do
    throw ⟨.divergence, "Replay request changed at a recorded location"⟩
  return record.outcome

def finish [Monad m] (store : ReplayStore m) (branch : Location) (outcome : Exit) :
    ExceptT CloudError m Progress := do
  store.finish branch outcome
  return .done

def join [Monad m] (store : ReplayStore m) (location : Location) (count : Nat) :
    ExceptT CloudError m Exit := do
  let outcomes ← (Array.range count).mapM fun index => do
    let some outcome ← store.outcome (location.child index)
      | throw ⟨.protocol, "Scheduler resumed a group before its children completed"⟩
    return outcome
  return collect outcomes

end Internal
open Internal

def result [Monad m] [codec : Codec α] (outcome : Exit) : ExceptT CloudError m α :=
  match outcome with
  | .success value => decode codec value
  | .failure error => throw error
  | .cancelled reason => throw ⟨.cancelled, reason⟩

/-- `active` becomes true at the assigned location. Before that point only
recorded values may be used; after it, missing command results may be executed.
The program retains its result type. Its encoder is used only for completion;
descending into a child selects that child's encoder. -/
def walk [Monad m] (store : ReplayStore m) (blobs : BlobStorage m) (assignment : Assignment)
    (fuel : Nat) (encode : α → Json) (program : Cloud m α) (current : Location) (active : Bool := false) :
    ExceptT CloudError m Progress :=
  match fuel with
  | 0 => throw ⟨.protocol, "Interpreter fuel exhausted"⟩
  | fuel + 1 =>
    let active := active || current == assignment.location
    match program with
    | EffF.pure value => do
      unless active do throw ⟨.divergence, "Computation ended before the assigned location"⟩
      finish store assignment.branch (.success (encode value))
    | .impure control continuation =>
      match control, continuation with
      | .delay, continuation =>
        walk store blobs assignment fuel encode (ArrsF.apply continuation ()) current active
      | .fail error, _ => do
        unless active do throw ⟨.divergence, "Computation failed before the assigned location"⟩
        finish store assignment.branch (.failure error)
      | .command codec operation, continuation => do
        let expected := request codec operation
        let outcome ← match ← store.read (ReplayStore.valueKey current) with
          | some record => check expected record
          | none => do
            unless active do throw ⟨.divergence, "Missing result in replay prefix"⟩
            let outcome ← try
              pure (.success (codec.encode (← blobs.execute operation)))
            catch error => pure (.failure error)
            check expected (← store.create (ReplayStore.valueKey current) ⟨expected, outcome⟩)
        match outcome with
        | .success value =>
          let value ← decode codec value
          walk store blobs assignment fuel encode (ArrsF.apply continuation value) current.next active
        | outcome =>
          unless active do throw ⟨.divergence, "Replay prefix failed"⟩
          finish store assignment.branch outcome
      | .parallel codec count branches, continuation => do
        let expected : Request := ⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩
        -- Descending into a child requires no mutable suspension record.
        if !active && current.entersChild assignment.location then
          let index := assignment.location[current.size]!.1
          if inside : index < count then
            walk store blobs assignment fuel codec.encode (branches ⟨index, inside⟩)
              (current.child index)
          else throw ⟨.divergence, "Child index is outside the group"⟩
        else
          let existing ← store.read (ReplayStore.valueKey current)
          if existing.isNone && (current != assignment.location || !assignment.joining) then
            unless active do throw ⟨.divergence, "Missing joined result in replay prefix"⟩
            return .fork current count
          let outcome ← match existing with
            | some record => check expected record
            | none => do
              unless active do throw ⟨.divergence, "Missing joined result in replay prefix"⟩
              let outcome ← join store current count
              check expected (← store.create (ReplayStore.valueKey current) ⟨expected, outcome⟩)
          match outcome with
          | .success value =>
            let values ← decodeGroup codec count value
            walk store blobs assignment fuel encode (ArrsF.apply continuation values) current.next active
          | outcome =>
            unless active do throw ⟨.divergence, "Replay prefix failed"⟩
            finish store assignment.branch outcome

/-- Run one assigned branch segment. Repeated attempts reuse its durable return
record, including a write whose acknowledgement was lost in a crash. -/
def step [Monad m] [Codec α] (store : ReplayStore m) (blobs : BlobStorage m) (fuel : Nat)
    (program : ι → Cloud m α) (input : ι) (assignment : Assignment) :
    ExceptT CloudError m Progress := do
  unless !assignment.location.isEmpty && assignment.location[0]!.1 == 0 do
    throw ⟨.protocol, "A location must start at root branch 0"⟩
  if (← store.outcome assignment.branch).isSome then return .done
  walk store blobs assignment fuel Codec.encode (program input) Location.root

end LeanCloud.ReplayInterpreter
