import LeanCloudTests.Support

namespace LeanCloudTests
open LeanCloud

def generatedCases : Array TestCase := (Array.range 256).flatMap fun seed =>
  #[false, true].map fun chaos =>
    let tree := (generate (3 + seed % 3) seed).1
    ⟨s!"generated/{if chaos then "chaos" else "clean"}/{seed}", do
      try
        let _ ← differential (fun _ => lower tree (seed % 17)) seed chaos
      catch error =>
        throw (IO.userError s!"seed={seed}, program={reprStr tree}\n{error}")⟩

def compositionCases : Array TestCase := Id.run do
  let leaves := #[Tree.value 0, Tree.effect 2, Tree.blob 3, Tree.fail 4]
  let mut cases := #[]
  for (a, i) in leaves.toList.zipIdx do
    for (b, j) in leaves.toList.zipIdx do
      for (tree, tag) in [(Tree.parallel [a, b], "parallel"), (Tree.bind a b, "bind")] do
        cases := cases.push ⟨s!"generated/composition/{tag}/{i}/{j}", do
          let _ ← differential (fun _ => lower tree 1) (i * 4 + j) true
          pure ()⟩
  return cases

/-- Blob failures must be durable workflow outcomes, unlike base-monad IO errors. -/
def blobFailureCases : Array TestCase :=
  let programs : Array (String × Cloud (SimM SimulationBackend.World) String × ErrorKind) := #[
    ("missing-name", CloudBlob.readTextByName "missing", .missingBlob),
    ("integrity", (do
      let ref ← CloudBlob.putText "content"
      CloudBlob.readText { ref with checksum := ref.checksum + 1 }), .integrity),
    ("invalid-utf8", (do
      let ref ← CloudBlob.putBytes (ByteArray.mk #[255])
      CloudBlob.readText ref), .invalidUtf8)]
  programs.flatMap fun (name, source, kind) => #[false, true].map fun chaos =>
    ⟨s!"blobs/{name}/{if chaos then "chaos" else "clean"}", do
      let world ← differential (fun _ => source) 71 chaos
      let some record := world.records.lookup (ReplayStore.returnKey Location.root)
        | throw (IO.userError "Missing durable blob failure")
      assertError (ReplayInterpreter.result (m := Id) (α := String) record.outcome).run kind⟩

end LeanCloudTests
