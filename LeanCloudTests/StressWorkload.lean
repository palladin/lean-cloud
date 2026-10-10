import LeanCloud.Core

/-! Pure, size-controlled workloads shared by model and deployed stress tests.
The result depends on child order, captures, and every recorded command. -/
namespace LeanCloudTests.StressWorkload
open Lean LeanCloud

inductive Shape where
  | wide | deep | chain
  deriving Repr, BEq, ToJson, FromJson

structure Input where
  shape : Shape
  size : Nat
  seed : Nat := 7
  deriving Repr, BEq, ToJson, FromJson

instance : Codec Input := jsonCodec Input "stress-input/v1"

private def combine (left right : Nat) : Nat := (left * 31 + right + 1) % 1000000007

private def chain [Pure m] : Nat → Nat → Cloud m Nat
  | 0, input => pure input
  | n + 1, input => do
      let value ← Cloud.pure (fun _ => combine input n) "chain"
      chain n value

private def deep [Pure m] : Nat → Nat → Cloud m Nat
  | 0, input => Cloud.pure (fun _ => input) "leaf"
  | n + 1, input => do
      let captured ← Cloud.pure (fun _ => combine input n) "capture"
      let values ← Cloud.parallel #[deep n captured, Cloud.pure (fun _ => captured + 1) "sibling"]
      return values.foldl combine input

def workflow [Pure m] (input : Input) : Cloud m Nat := do
  match input.shape with
  | .chain => chain input.size input.seed
  | .deep => deep input.size input.seed
  | .wide =>
      let captured ← Cloud.pure (fun _ => input.seed + 3) "capture"
      let values ← Cloud.parallel ((Array.range input.size).map fun i =>
        Cloud.pure (fun _ => combine captured i) "child")
      return values.foldl combine input.seed

def smoke : Array Input := #[⟨.wide, 64, 7⟩, ⟨.deep, 12, 7⟩, ⟨.chain, 256, 7⟩]
def large : Array Input := #[⟨.wide, 1024, 7⟩, ⟨.deep, 48, 7⟩, ⟨.chain, 4096, 7⟩]

end LeanCloudTests.StressWorkload
