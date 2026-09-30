import LeanCloud.Core

namespace LeanCloudRuntime.Demo
open Lean LeanCloud

structure Input where
  files : Array String
  batchSize : Nat := 2
  pauseMs : Nat := 500
  deriving FromJson, ToJson

def batches {α : Type} (items : Array α) (size : Nat) : Array (Array α) :=
  let size := max 1 size
  (Array.range ((items.size + size - 1) / size)).map fun i =>
    items.extract (i * size) ((i + 1) * size)

/-- Ordinary captured variables and global blobs; workers run this same code.
The delay makes work distribution and interruption visible in the local demo. -/
def workflow (input : Input) : Cloud IO BlobRef := cloud {
  let counts ← Cloud.parallel ((batches input.files input.batchSize).map fun batch => cloud {
    let mut errors := 0
    for name in batch do
      let text ← CloudBlob.readTextByName name
      errors := errors + ((text.splitOn "\n").filter (·.startsWith "ERROR")).length
    Cloud.exec (fun _ => do
      IO.sleep input.pauseMs.toUInt32
      return errors) "analyze-batch"
  })
  let total := counts.foldl (· + ·) 0
  CloudBlob.putText s!"files={input.files.size}, errors={total}\n"
}

def sampleFiles : Array (String × String) := (Array.range 16).map fun i =>
  (s!"demo/log-{i}.txt", "INFO started\nERROR first\n" ++
    (if i % 2 == 0 then "ERROR second\n" else "INFO finished\n"))

def input : Input := ⟨sampleFiles.map Prod.fst, 2, 500⟩
def expected : String := "files=16, errors=24\n"

end LeanCloudRuntime.Demo
