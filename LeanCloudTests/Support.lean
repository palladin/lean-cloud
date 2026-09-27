import LeanCloud

namespace LeanCloudTests
open Lean LeanCloud

structure TestCase where
  name : String
  run : IO Unit

def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def assertEq [BEq α] [Repr α] (actual expected : α) (context : String := "Values differ") : IO Unit :=
  assertTrue (actual == expected) s!"{context}\nexpected: {reprStr expected}\nactual:   {reprStr actual}"

def assertOutcome [BEq α] [Repr α] (actual expected : Except CloudError α) : IO Unit :=
  match actual, expected with
  | .ok a, .ok b => assertEq a b "Results differ"
  | .error a, .error b => assertEq a b "Errors differ"
  | _, _ => throw (IO.userError s!"Outcomes differ\nexpected: {reprStr expected}\nactual: {reprStr actual}")

def assertError (actual : Except CloudError α) (kind : ErrorKind) : IO Unit :=
  match actual with
  | .error error => assertEq error.kind kind
  | .ok _ => throw (IO.userError s!"Expected {reprStr kind}, got success")

structure World where
  records : List (String × Json) := []
  blobs : List (String × ByteArray) := []
  names : List (String × BlobRef) := []
  nextBlob : Nat := 0
  trace : Array (String × Json) := #[]
  recordGets : Nat := 0
  recordPuts : Nat := 0
  rejectPuts : Bool := false
  rejectBlobPuts : Bool := false
  crashAfterPut : Option Nat := none
  crashBeforePut : Option Nat := none

abbrev Ref := IO.Ref World
abbrev Program (α : Type) := Ref → Cloud IO α

def makeRef (key : String) (bytes : ByteArray) : BlobRef :=
  ⟨key, bytes.size, modelChecksum bytes⟩

def initial : World :=
  let bytes := "seed: λ 🌍".toUTF8
  { blobs := [("seed-bytes", bytes)], names := [("seed", makeRef "seed-bytes" bytes)] }

def appendEvent (ref : Ref) (name : String) (payload : Json) : IO Unit :=
  ref.modify fun world => { world with trace := world.trace.push (name, payload) }

/-- Unique blob keys deliberately expose duplicate effects during replay. -/
def storage : Storage Ref IO where
  get key ref := do
    ref.modify fun world => { world with recordGets := world.recordGets + 1 }
    return ((← ref.get).records.lookup key, ref)
  put key value ref := do
    let world ← ref.get
    let writes := world.recordPuts + 1
    ref.modify fun world => { world with recordPuts := writes }
    if world.crashBeforePut == some writes then
      ref.modify fun world => { world with crashBeforePut := none }
      throw (IO.userError "injected crash before journal commit")
    if world.rejectPuts then return (false, ref)
    ref.modify fun world => { world with
      records := (key, value) :: world.records.filter (fun entry => entry.1 != key) }
    if world.crashAfterPut == some writes then
      ref.modify fun world => { world with crashAfterPut := none }
      throw (IO.userError "injected crash after journal commit")
    return (true, ref)
  putBlob bytes ref := do
    appendEvent ref "putBlob" (encodeBytes bytes)
    let world ← ref.get
    if world.rejectBlobPuts then
      return (.error ⟨.application, "blob write rejected"⟩, ref)
    let blob := makeRef s!"blob/{world.nextBlob}" bytes
    ref.modify fun world => { world with
      nextBlob := world.nextBlob + 1
      blobs := (blob.key, bytes) :: world.blobs }
    return (.ok blob, ref)
  readBlob blob ref := do
    appendEvent ref "readBlob" (toJson blob)
    let some bytes := (← ref.get).blobs.lookup blob.key
      | return (.error ⟨.missingBlob, s!"Missing blob: {blob.key}"⟩, ref)
    if bytes.size != blob.size || modelChecksum bytes != blob.checksum then
      return (.error ⟨.integrity, "Blob reference does not match its bytes"⟩, ref)
    return (.ok bytes, ref)
  resolveBlob name ref := do
    appendEvent ref "resolveBlob" (toJson name)
    match (← ref.get).names.lookup name with
    | some blob => return (.ok blob, ref)
    | none => return (.error ⟨.missingBlob, s!"Missing name: {name}"⟩, ref)

def execValue [Codec α] (ref : Ref) (label : String) (value : α) : Cloud IO α :=
  Cloud.exec (fun _ => do
    appendEvent ref s!"exec:{label}" (Codec.encode value)
    return value) label

/-- Compare observable backend state separately from replay bookkeeping. -/
def externalState (world : World) : Json := Json.mkObj [
  ("blobs", toJson (world.blobs.map fun (key, bytes) => (key, encodeBytes bytes))),
  ("names", toJson world.names), ("nextBlob", toJson world.nextBlob)]

def journal (world : World) : List (String × Json) :=
  world.records.mergeSort (fun a b => a.1 ≤ b.1)

def assertObservations (actual expected : World) : IO Unit := do
  assertEq actual.trace expected.trace "Primitive effect order or multiplicity differs"
  assertEq (externalState actual) (externalState expected) "Backend state differs"

def replayFuel : Nat := 200000

def runDirect (program : Program α) (ref : Ref) : IO (Except CloudError α) := do
  let (result, _) ← (DirectInterpreter.interpret storage program ref).run ref
  return result

def runReplay [Codec α] (program : Program α) (ref : Ref) (fuel : Nat := replayFuel) :
    IO (Except CloudError α) := do
  let (result, _) ← (interpret storage fuel program ref).run ref
  return result

/-- Fresh-run comparison plus a second replay that must perform no new primitive effects. -/
def differential [Codec α] [BEq α] [Repr α] (program : Program α) (world : World := initial) :
    IO (Except CloudError α × World) := do
  let directRef ← IO.mkRef world
  let replayRef ← IO.mkRef world
  let expected ← runDirect program directRef
  let actual ← runReplay program replayRef
  assertOutcome actual expected
  let directWorld ← directRef.get
  let replayWorld ← replayRef.get
  assertEq directWorld.recordGets world.recordGets "Direct interpreter read the journal"
  assertEq directWorld.recordPuts world.recordPuts "Direct interpreter wrote the journal"
  assertObservations replayWorld directWorld
  let repeated ← runReplay program replayRef
  assertOutcome repeated expected
  assertObservations (← replayRef.get) replayWorld
  assertEq (journal (← replayRef.get)) (journal replayWorld) "Warm replay changed recorded outcomes"
  return (actual, replayWorld)

def expect [Codec α] [BEq α] [Repr α] (name : String) (program : Program α)
    (expected : Except CloudError α) (world : World := initial) : TestCase :=
  ⟨s!"differential/{name}", do
    let (actual, _) ← differential program world
    assertOutcome actual expected⟩

end LeanCloudTests
