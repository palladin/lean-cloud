import LeanCloud.Core
import LeanCloud.BlobStorage
import LeanCloud.ReplayStore
import LeanCloud.Coordination

/-! `step` starts at the root. `reconstruct` follows recorded results to the
assigned location, then calls `execute` with the remaining fuel. `execute` runs
until the next fork or branch completion.

Command results, joined arrays, and branch returns are immutable global records.
Partial joins and assignment ownership live only in the scheduler. -/

namespace LeanCloud.ReplayInterpreter
open Lean LeanEff

/-- Combine completed child results in source order, selecting the first error
if any. The worker calls this after every child has returned. -/
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

/-- Reuse a command's record, or execute the command and publish its result.
Always use the record returned by `create`: another attempt may have published first.
Only workflow errors are recorded; failures in the base monad still escape. -/
def command [Monad m] (store : ReplayStore m) (blobs : BlobStorage m)
    (current : Location) (codec : Codec α) (operation : Operation m α) :
    ExceptT CloudError m Exit := do
  let expected := request codec operation
  match ← store.read (ReplayStore.valueKey current) with
  | some record => check expected record
  | none =>
    let outcome ← try
      pure (.success (codec.encode (← blobs.execute operation)))
    catch error => pure (.failure error)
    check expected (← store.create (ReplayStore.valueKey current) ⟨expected, outcome⟩)

/-- Decode a successful result and continue, or finish the assigned branch. -/
@[inline] def resume [Monad m] (store : ReplayStore m) (branch : Location)
    (decode : Json → ExceptT CloudError m α) (next : α → ExceptT CloudError m Progress)
    (outcome : Exit) : ExceptT CloudError m Progress :=
  match outcome with
  | .success value => do next (← decode value)
  | outcome => finish store branch outcome

/-- Reconstruction requires an existing successful result; it never creates one. -/
def recorded [Monad m] (store : ReplayStore m) (current : Location)
    (expected : Request) (missing : String) : ExceptT CloudError m Json := do
  let some record ← store.read (ReplayStore.valueKey current)
    | throw ⟨.divergence, missing⟩
  match ← check expected record with
  | .success value => return value
  | _ => throw ⟨.divergence, "Replay prefix failed"⟩

/-- The scheduler authorizes a join only after all child returns are durable. -/
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

/-- Optional diagnostic context. It is not persisted and never affects routing. -/
abbrev Observer (m : Type → Type u) := Location → Option SourceSiteId → m Unit

/-- Execute the assigned branch segment. Commands reuse or create records;
parallel groups reuse a result, perform an authorized join, or suspend. -/
def execute [Monad m] (store : ReplayStore m) (blobs : BlobStorage m) (assignment : Assignment)
    (fuel : Nat) (encode : α → Json) (program : Cloud m α) (current : Location)
    (observer : Option (Observer m) := none) :
    ExceptT CloudError m Progress :=
  match fuel with
  | 0 => throw ⟨.protocol, "Interpreter fuel exhausted"⟩
  | fuel + 1 =>
    let action :=
      match program with
      | EffF.pure _ value => finish store assignment.branch (.success (encode value))
      | .impure _ control continuation =>
        match control, continuation with
        | .delay, continuation =>
          execute store blobs assignment fuel encode (ArrsF.apply continuation ()) current observer
        | .fail error, _ => finish store assignment.branch (.failure error)
        | .command codec operation, continuation => do
          let outcome ← command store blobs current codec operation
          resume store assignment.branch (decode codec)
            (fun value => execute store blobs assignment fuel encode
              (ArrsF.apply continuation value) current.next observer) outcome
        | .parallel codec count _, continuation => do
          let expected : Request := ⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩
          let existing ← store.read (ReplayStore.valueKey current)
          if existing.isNone && (current != assignment.location || !assignment.joining) then
            return .fork current count
          let outcome ← match existing with
            | some record => check expected record
            | none => do
              let outcome ← join store current count
              check expected (← store.create (ReplayStore.valueKey current) ⟨expected, outcome⟩)
          resume store assignment.branch (decodeGroup codec count)
            (fun values => execute store blobs assignment fuel encode
              (ArrsF.apply continuation values) current.next observer) outcome
    match observer with
    | none => action
    | some visit => do
      visit current program.metadata
      action

/-- Follow the recorded prefix from the root to the assignment. Descending into
a child selects its computation and result encoder. At the target, execution
starts directly: changing phase consumes no fuel and adds no observation. -/
def reconstruct [Monad m] (store : ReplayStore m) (blobs : BlobStorage m) (assignment : Assignment)
    (fuel : Nat) (encode : α → Json) (program : Cloud m α) (current : Location)
    (observer : Option (Observer m) := none) : ExceptT CloudError m Progress :=
  match fuel with
  | 0 => throw ⟨.protocol, "Interpreter fuel exhausted"⟩
  | fuel + 1 =>
    if current == assignment.location then
      execute store blobs assignment (fuel + 1) encode program current observer
    else
      let action :=
        match program with
        | EffF.pure _ _ => throw ⟨.divergence, "Computation ended before the assigned location"⟩
        | .impure _ control continuation =>
          match control, continuation with
          | .delay, continuation =>
            reconstruct store blobs assignment fuel encode (ArrsF.apply continuation ()) current observer
          | .fail _, _ => throw ⟨.divergence, "Computation failed before the assigned location"⟩
          | .command codec operation, continuation => do
            let wire ← recorded store current (request codec operation) "Missing result in replay prefix"
            let value ← decode codec wire
            reconstruct store blobs assignment fuel encode (ArrsF.apply continuation value) current.next observer
          | .parallel codec count branches, continuation => do
            if current.entersChild assignment.location then
              let index := assignment.location[current.size]!.1
              if inside : index < count then
                reconstruct store blobs assignment fuel codec.encode (branches ⟨index, inside⟩)
                  (current.child index) observer
              else throw ⟨.divergence, "Child index is outside the group"⟩
            else
              let expected : Request := ⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩
              let wire ← recorded store current expected "Missing joined result in replay prefix"
              let values ← decodeGroup codec count wire
              reconstruct store blobs assignment fuel encode (ArrsF.apply continuation values) current.next observer
      match observer with
      | none => action
      | some visit => do
        visit current program.metadata
        action

/-- Run one assigned branch segment. Repeated attempts reuse its durable return
record, including a write whose acknowledgement was lost in a crash. -/
def step [Monad m] [Codec α] (store : ReplayStore m) (blobs : BlobStorage m) (fuel : Nat)
    (program : ι → Cloud m α) (input : ι) (assignment : Assignment)
    (observer : Option (Observer m) := none) :
    ExceptT CloudError m Progress := do
  unless !assignment.location.isEmpty && assignment.location[0]!.1 == 0 do
    throw ⟨.protocol, "A location must start at root branch 0"⟩
  if (← store.outcome assignment.branch).isSome then return .done
  reconstruct store blobs assignment fuel Codec.encode (program input) Location.root observer

end LeanCloud.ReplayInterpreter
