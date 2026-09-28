import LeanCloudTests.Backends

namespace LeanCloudTests
open Lean LeanCloud

def pureComputationCases : Array TestCase := #[
  expect "pure-compute/captured-input" (fun _ =>
    let input := 7
    Cloud.pure (fun _ => input * input + 1) "analyze") (.ok 50),
  expect "pure-compute/dependent-bind" (fun _ => do
    let input ← Cloud.pure (fun _ => 5)
    Cloud.pure (fun _ => input * 3)) (.ok 15),
  expect "pure-compute/parallel-pair" (fun _ =>
    cloud { Cloud.pure (fun _ => 3 * 4) } || cloud { Cloud.pure (fun _ => "result") })
    (.ok (12, "result")),
  expect "pure-compute/blob-input" (fun _ => do
    let text ← CloudBlob.readTextByName "seed"
    Cloud.pure (fun _ => text.length)) (.ok "seed: λ 🌍".length),
  ⟨"pure-compute/cached-value", do
    let ref ← IO.mkRef { initial with records := [
      (Location.root.key, toJson (Result.completed (.success (toJson (42 : Nat)))))] }
    let result ← runReplay (fun _ => Cloud.pure (fun _ => (99 : Nat))) ref
    assertOutcome result (.ok 42)
    assertTrue (← ref.get).trace.isEmpty "Pure computation performed a backend effect"⟩,
  ⟨"pure-compute/id-backend", do
    let program (input : Nat) : Cloud Id Nat := Cloud.pure (fun _ => input + 2)
    let (direct, _) := (DirectInterpreter.interpret idBlobs program 3).run {}
    let (replayed, _) := (interpret idDb idBlobs idQueue replayFuel program 3).run {}
    assertOutcome direct (.ok 5)
    assertOutcome replayed direct⟩
]

end LeanCloudTests
