import LeanCloudTests.Support

namespace LeanCloudTests
open Lean LeanCloud

def nested (ref : Ref) : Cloud IO Nat := cloud {
  let captured ← execValue ref "capture" 10
  let values ← Cloud.parallel #[cloud {
    let inner ← Cloud.parallel #[execValue ref "a" captured, execValue ref "b" (captured + 1)]
    return inner.foldl (· + ·) 0
  }, execValue ref "c" 5]
  let later ← Cloud.parallel #[execValue ref "d" values[0]!, execValue ref "e" values[1]!]
  return later.foldl (· + ·) 0
}

def blobWorkflow (ref : Ref) : Cloud IO String := cloud {
  let input ← execValue ref "input" "hello"
  let own ← CloudBlob.putText input
  let named ← CloudBlob.resolve "seed"
  let values ← Cloud.parallel #[CloudBlob.readText own, CloudBlob.readText named]
  return values[0]! ++ "/" ++ values[1]!
}

def failingParallel (ref : Ref) : Cloud IO Nat := cloud {
  let values ← Cloud.parallel #[cloud {
    let _ ← execValue ref "first" 1
    Cloud.fail "first failure"
  }, cloud {
    let _ ← execValue ref "second" 2
    Cloud.fail "second failure"
  }, execValue ref "third" 3]
  let _ ← execValue ref "must-not-run" 99
  return values.foldl (· + ·) 0
}

def chain (ref : Ref) (count : Nat) : Cloud IO Nat :=
  (List.range count).foldl (fun accumulated index => do
    let value ← accumulated
    execValue ref s!"chain/{index}" (value + index)) (pure 0)

def differentialCases : Array TestCase := #[
  expect "pure/nat" (fun _ => pure (42 : Nat)) (.ok 42),
  expect "pure/large-nat" (fun _ => pure (2^100 + 17 : Nat)) (.ok (2^100 + 17)),
  expect "pure/unicode" (fun _ => pure "λ 🌍\n\u0000") (.ok "λ 🌍\n\u0000"),
  expect "pure/unit" (fun _ => pure ()) (.ok ()),
  expect "pure/option" (fun _ => pure (some (none : Option Nat))) (.ok (some none)),
  expect "delay/nested" (fun _ => Cloud.delay fun _ => Cloud.delay fun _ => pure (8 : Nat)) (.ok 8),
  expect "exec/nat" (fun ref => execValue ref "value" 17) (.ok 17),
  expect "exec/mixed-types" (fun ref => do
    let a ← execValue ref "a" (#[true, false] : Array Bool)
    let b ← execValue ref "b" (some "text")
    return (a, b)) (.ok (#[true, false], some "text")),
  expect "parallel/empty" (fun _ => Cloud.parallel (#[] : Array (Cloud IO Nat))) (.ok #[]),
  expect "parallel/single" (fun ref => Cloud.parallel #[execValue ref "only" 9]) (.ok #[9]),
  expect "parallel/order" (fun ref => Cloud.parallel #[execValue ref "a" 7, execValue ref "b" 3,
    execValue ref "c" 11]) (.ok #[7, 3, 11]),
  expect "parallel/empty-child" (fun ref => Cloud.parallel #[Cloud.parallel (#[] : Array (Cloud IO Nat)),
    Cloud.parallel #[execValue ref "child" 4]]) (.ok #[#[], #[4]]),
  expect "parallel/nested-and-successive" nested (.ok 26),
  expect "parallel/heterogeneous-pair" (fun ref =>
    cloud { execValue ref "left" 7 } || cloud { execValue ref "right" "seven" }) (.ok (7, "seven")),
  expect "parallel/wide" (fun ref => Cloud.parallel ((List.range 64).toArray.map fun n =>
    execValue ref s!"wide/{n}" n)) (.ok (List.range 64).toArray),
  expect "continuation/left-associated" (fun ref => chain ref 128) (.ok (127 * 128 / 2)),
  expect "continuation/data-dependent" (fun ref => cloud {
    let n ← execValue ref "branch" 4
    if n % 2 == 0 then
      let values ← Cloud.parallel #[pure (n + 1), execValue ref "even" (n * 2)]
      return values.foldl (· + ·) 0
    else execValue ref "must-not-run" 999
  }) (.ok 13),
  expect "failure/root" (fun _ => (Cloud.fail "root" : Cloud IO Nat)) (.error ⟨.application, "root"⟩),
  expect "failure/after-exec" (fun ref => do
    let _ ← execValue ref "before-failure" 2
    (Cloud.fail "after" : Cloud IO Nat)) (.error ⟨.application, "after"⟩),
  expect "failure/first-array-position" failingParallel (.error ⟨.application, "first failure"⟩),
  expect "failure/nested" (fun ref => Cloud.parallel #[cloud {
    let _ ← Cloud.parallel #[execValue ref "a" 1, (Cloud.fail "nested" : Cloud IO Nat)]
    execValue ref "must-not-run" 9
  }, execValue ref "sibling" 2]) (.error ⟨.application, "nested"⟩),
  expect "blob/put-ref" (fun _ => CloudBlob.putText "hello") (.ok (makeRef "blob/0" "hello".toUTF8)),
  expect "blob/roundtrip-parallel" blobWorkflow (.ok "hello/seed: λ 🌍"),
  expect "blob/all-bytes" (fun _ => do
    let bytes := ByteArray.mk ((List.range 256).toArray.map Nat.toUInt8)
    let blob ← CloudBlob.putBytes bytes
    return (← CloudBlob.readBytes blob).data.map UInt8.toNat) (.ok (List.range 256).toArray),
  expect "blob/empty" (fun _ => do
    let blob ← CloudBlob.putText ""
    CloudBlob.readText blob) (.ok ""),
  expect "blob/missing-name" (fun _ => CloudBlob.resolve "absent")
    (.error ⟨.missingBlob, "Missing name: absent"⟩),
  expect "blob/missing-ref" (fun _ => CloudBlob.readText (makeRef "absent" "".toUTF8))
    (.error ⟨.missingBlob, "Missing blob: absent"⟩),
  expect "blob/wrong-size" (fun _ => CloudBlob.readText { (makeRef "seed-bytes" "seed: λ 🌍".toUTF8) with size := 999 })
    (.error ⟨.integrity, "Blob reference does not match its bytes"⟩),
  expect "blob/wrong-checksum" (fun _ => CloudBlob.readText { (makeRef "seed-bytes" "seed: λ 🌍".toUTF8) with checksum := 0 })
    (.error ⟨.integrity, "Blob reference does not match its bytes"⟩),
  expect "blob/invalid-utf8" (fun _ => do
    let blob ← CloudBlob.putBytes (ByteArray.mk #[255])
    CloudBlob.readText blob) (.error ⟨.invalidUtf8, "Blob is not valid UTF-8"⟩),
  expect "blob/rejected-writes" (fun _ => Cloud.parallel #[CloudBlob.putText "a", CloudBlob.putText "b"])
    (.error ⟨.application, "blob write rejected"⟩) { initial with rejectBlobPuts := true },
  expect "choice/explicitly-unsupported" (fun _ => Cloud.choice (#[] : Array (Cloud IO (Option Nat))))
    (.error ⟨.unsupported, "Choice is not implemented yet"⟩),
  ⟨"oracle/known-effect-order", do
    let (result, world) ← differential nested
    assertOutcome result (.ok 26)
    assertEq (world.trace.map Prod.fst) #["exec:capture", "exec:a", "exec:b", "exec:c", "exec:d", "exec:e"]⟩,
  ⟨"oracle/all-children-after-failure", do
    let (_, world) ← differential failingParallel
    assertEq (world.trace.map Prod.fst) #["exec:first", "exec:second", "exec:third"]⟩,
  ⟨"oracle/nonserializable-result", do
    let ref ← IO.mkRef initial
    let result ← runDirect (fun _ => pure (fun n : Nat => n + 3)) ref
    match result with
    | .ok f => assertEq (f 4) 7
    | .error error => throw (IO.userError (reprStr error))⟩
]

end LeanCloudTests
