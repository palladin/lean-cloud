import LeanCloudTests.Support

namespace LeanCloudTests
open Lean LeanCloud

def deep (ref : Ref) : Nat → Cloud IO Nat
  | 0 => execValue ref "deep-leaf" 0
  | n + 1 => cloud {
    let values ← Cloud.parallel #[deep ref n, pure 1]
    return values.foldl (· + ·) 0
  }

def tick (ref : Ref) : Cloud IO Nat := Cloud.exec (fun _ => do
  let n := (← ref.get).trace.size
  appendEvent ref "exec:tick" (toJson n)
  return n)

def idStorage : Storage (List (String × Json)) Id where
  get key := return (← get).lookup key
  put key value := do
    modify fun entries => (key, value) :: entries.filter (fun entry => entry.1 != key)
    return true
  putBlob _ := throw ⟨.unsupported, "This fixture has no blobs"⟩
  readBlob _ := throw ⟨.unsupported, "This fixture has no blobs"⟩
  resolveBlob _ := throw ⟨.unsupported, "This fixture has no blobs"⟩

def backendCases : Array TestCase := #[
  expect "parallel/depth-32" (fun ref => deep ref 32) (.ok 32),
  expect "exec/state-dependent-result" (fun ref => cloud {
    let width ← tick ref
    Cloud.parallel ((List.range (width + 2)).toArray.map fun _ => tick ref)
  }) (.ok #[1, 2]),
  ⟨"backend/id-state", do
    let program (input : Nat) : Cloud Id Nat := cloud {
      let value ← Cloud.exec (fun _ => input + 1)
      let values ← Cloud.parallel #[pure value, pure (value + 1)]
      return values.foldl (· + ·) 0
    }
    let (direct, unchanged) := (DirectInterpreter.interpret idStorage program 3).run []
    let (replayed, records) := (interpret idStorage replayFuel program 3).run []
    assertOutcome direct (.ok 9)
    assertOutcome replayed direct
    assertTrue unchanged.isEmpty "Direct Id interpretation changed the journal"
    assertTrue (!records.isEmpty) "Replay Id interpretation lost its state"
    let (again, _) := (interpret idStorage replayFuel program 3).run records
    assertOutcome again direct⟩,
  ⟨"backend/direct-never-accesses-journal", do
    let strict : Storage Ref IO := { storage with
      get := fun _ _ => throw (IO.userError "Unexpected journal read")
      put := fun _ _ _ => throw (IO.userError "Unexpected journal write") }
    let ref ← IO.mkRef initial
    let (result, _) ← (DirectInterpreter.interpret strict (fun ref => deep ref 8) ref).run ref
    assertOutcome result (.ok 8)⟩,
  ⟨"backend/returned-io-handle", do
    for direct in [true, false] do
      let ref ← IO.mkRef initial
      let program : Program Nat := fun ref => execValue ref "handle" 1
      let (result, returned) ← if direct then
        (DirectInterpreter.interpret storage program ref).run ref
      else (interpret storage replayFuel program ref).run ref
      assertOutcome result (.ok 1)
      returned.modify fun world => { world with nextBlob := 777 }
      assertEq (← ref.get).nextBlob 777 "Interpreter returned a different IO handle"⟩,
  ⟨"backend/native-io-exceptions", do
    let program : Program (Array Nat) := fun ref => Cloud.parallel #[cloud {
      let _ ← execValue ref "before-native-error" 1
      Cloud.exec (fun _ => do
        appendEvent ref "exec:native-error" Json.null
        throw (IO.userError "native failure"))
    }, execValue ref "must-not-run" 9]
    let directRef ← IO.mkRef initial
    let replayRef ← IO.mkRef initial
    let directError ← try
      let _ ← runDirect program directRef
      pure none
    catch error => pure (some error.toString)
    let replayError ← try
      let _ ← runReplay program replayRef
      pure none
    catch error => pure (some error.toString)
    assertEq directError (some "native failure")
    assertEq replayError directError
    assertObservations (← replayRef.get) (← directRef.get)
    assertEq ((← directRef.get).trace.map Prod.fst) #["exec:before-native-error", "exec:native-error"]⟩,
  ⟨"location/navigation", do
    let location : Location := #[(0, 2), (1, 5)]
    assertEq location.key "0:2/1:5"
    assertEq location.next.key "0:2/1:6"
    assertEq (location.child 2).key "0:2/1:5/2:0"
    assertEq location.parent? (some (#[(0, 2)], 1))
    assertEq Location.root.parent? none
    assertTrue (Location.entersChild #[(0, 2)] location) "Ancestor did not select child"⟩
]

end LeanCloudTests
