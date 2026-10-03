import LeanCloudTests.Support

namespace LeanCloudTests.PureReplay
open Lean LeanCloud

private def simple (input : Nat) : Cloud Id Nat := do
  let values ← Cloud.parallel #[pure (input + 1), pure (input + 2)]
  return values.foldl (· + ·) 0

private def nested (input : Nat) : Cloud Id Nat := cloud {
  let values ← Cloud.parallel #[pure (input + 1), cloud {
    let inner ← Cloud.parallel #[pure (input * 2), pure (input * 3)]
    return inner.foldl (· + ·) 0
  }]
  let squares ← Cloud.parallel (values.map fun value => cloud { return value * value })
  return squares.foldl (· + ·) 0
}

private def compare [Codec α] [BEq α] [Repr α]
    (program : Nat → Cloud Id α) (input : Nat) (expected : Except CloudError α) : IO Unit := do
  assertOutcome (Pure.direct program input) expected
  let (actual, state) := Pure.resume 1000 program input Pure.initial
  assertOutcome actual expected
  let encoded := match expected with
    | .ok value => Exit.success (Codec.encode value)
    | .error error => .failure error
  assertEq state.completed (some encoded)
  assertTrue state.pending.isEmpty "Completed pure replay retained pending work"
  assertOutcome (Pure.resume 1 program input state).1 expected

def cases : Array TestCase := #[
  ⟨"pure-replay/value", compare (fun n => pure (n + 1)) 41 (.ok 42)⟩,
  ⟨"pure-replay/empty", compare (fun _ => Cloud.parallel (α := Nat) #[]) 0 (.ok #[])⟩,
  ⟨"pure-replay/nested-capture-and-dependent-bind", compare nested 3 (.ok 241)⟩,
  ⟨"pure-replay/heterogeneous-pair", compare (fun n =>
      cloud { return n + 1 } || cloud { return "right" }) 4 (.ok (5, "right"))⟩,
  ⟨"pure-replay/root-failure", compare (fun _ => Cloud.fail (α := Nat) "failed")
      0 (.error ⟨.application, "failed"⟩)⟩,
  ⟨"pure-replay/array-order-failure", compare (fun _ => Cloud.parallel #[
      cloud { Cloud.fail (α := Nat) "first" }, Cloud.fail "second"])
      0 (.error ⟨.application, "first"⟩)⟩,
  ⟨"pure-replay/saved-locations", do
    let (stopped, fork) := Pure.resume 1 simple 10 Pure.initial
    assertOutcome stopped (.error ⟨.protocol, "Interpreter fuel exhausted"⟩)
    assertEq (fork.pending.map Location.key) ["0:0/0:0", "0:0/1:0"]
    assertEq (fork.journal "0:0") (some (toJson (Result.suspended #[none, none])))
    let (stopped, child) := Pure.resume 2 simple 10 fork
    assertOutcome stopped (.error ⟨.protocol, "Interpreter fuel exhausted"⟩)
    assertEq (child.pending.map Location.key) ["0:0/1:0"]
    assertEq (child.journal "0:0/0:0")
      (some (toJson (Result.completed (.success (toJson (11 : Nat))))))
    assertOutcome (Pure.resume 1000 simple 10 child).1 (.ok 23)⟩,
  ⟨"pure-replay/resume-at-every-fuel-cut", do
    for fuel in [:41] do
      let (_, saved) := Pure.resume fuel nested 3 Pure.initial
      let (actual, finished) := Pure.resume 1000 nested 3 saved
      assertOutcome actual (.ok 241)
      assertEq finished.completed (some (.success (toJson (241 : Nat))))
      assertOutcome (Pure.resume 1 nested 3 finished).1 (.ok 241)⟩
]

end LeanCloudTests.PureReplay
