import LeanCloudTests.GeneratedProgram
import LeanCloud.DirectInterpreter

/-! Shared by the host oracle and the deployed test application. No runtime IO,
sleep, or test hooks are added to the workflow or its interpreter. -/

namespace LeanCloudTests.PoolWorkload
open Lean LeanCloud

structure Input where
  seed : Nat
  failing : Bool := false
  deriving Repr, BEq, ToJson, FromJson, Inhabited

instance : Codec Input := jsonCodec Input "pool-chaos-input/v1"

mutual
  /-- Keep generated control flow, replacing external operations and early
  failures with recorded pure computations. Selected leaves fail explicitly. -/
  private def pureTree : Tree → Tree
    | .blob n | .fail n => .effect n
    | .delay child => .delay (pureTree child)
    | .bind first next => .bind (pureTree first) (pureTree next)
    | .branch even odd => .branch (pureTree even) (pureTree odd)
    | .parallel children => .parallel (pureChildren children)
    | other => other

  private def pureChildren : List Tree → List Tree
    | [] => []
    | child :: rest => pureTree child :: pureChildren rest
end

/-- Guarantee nested forks and enough assignments to overlap faults, while
generating the leaf programs, captured inputs, and dependent continuations. Two
failing siblings also exercise source-ordered errors under concurrent execution. -/
def tree (input : Input) : Tree :=
  .bind (.effect (input.seed % 23)) (.parallel ((List.range 6).map fun i =>
    .delay (.parallel ((List.range 4).map fun j =>
      let seed := nextSeed (input.seed + i * 101 + j * 7919)
      let child := pureTree (generate 3 seed).1
      .bind (.effect (seed % 23)) (.bind child
        (if input.failing && i == 2 && (j == 0 || j == 2) then
          .fail (seed % 1009) else .effect (j + 1)))))))

def workflow [Pure m] (input : Input) : Cloud m Nat :=
  lower (tree input) (input.seed % 17)

/-- Reject any accidental use of external effects in the reference program. -/
private def noBlobs : BlobStorage Id := {
  putBlob := fun _ => throw ⟨.unsupported, "Pure chaos workflow used blobs"⟩
  readBlob := fun _ => throw ⟨.unsupported, "Pure chaos workflow used blobs"⟩
  resolveBlob := fun _ => throw ⟨.unsupported, "Pure chaos workflow used blobs"⟩ }

def expected (input : Input) : Exit :=
  match (DirectInterpreter.interpret noBlobs workflow input).run with
  | .ok value => .success (toJson value)
  | .error error => .failure error

/-- Two successful runs and one failing run share the same deployed registry. -/
def inputs (seed : Nat) : Array Input :=
  #[⟨seed, false⟩, ⟨nextSeed seed, false⟩, ⟨nextSeed (nextSeed seed), true⟩]

structure Fault where
  scheduler : Bool
  workerOffset : Nat
  delayMs : Nat
  completedBranches : Nat
  deriving Repr, BEq, ToJson, Inhabited

/-- Fixed before execution. Worker offsets select among currently busy workers;
the event log records the actual victim and assignment. Both actor roles are
always exercised. The seed reproduces choices, not OS timing. -/
def plan (seed : Nat) : Array Fault := Id.run do
  let mut seed := seed
  let mut result := #[]
  for i in [:6] do
    seed := nextSeed seed
    result := result.push ⟨i == 0 || (i > 1 && seed / 65536 % 3 == 0),
      seed / 256, 100 + seed / 16 % 401, (i - 1) * 4⟩
  return result

end LeanCloudTests.PoolWorkload
