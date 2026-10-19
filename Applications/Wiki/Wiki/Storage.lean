import Wiki.Workflow
import Wiki.Analysis
import Wiki.Native

namespace Wiki
open Lean LeanCloud LeanCloudRuntime LeanReducers

private def metadata [FromJson α] (store : ObjectStore) (ref : FileRef) : IO α := do
  IO.ofExcept (Json.parse (← Files.readText store ref (16 * MiB)) >>= fromJson?)

private def validParts (source : Source) : Except String Unit := do
  unless source.format == "wiki/source/v1" && !source.label.isEmpty && source.label.utf8ByteSize ≤ 1024 &&
      0 < source.parts.size && source.parts.size ≤ maxParts do throw "Invalid dump manifest"
  let mut inside := false
  let mut seen : Std.HashSet String := {}
  for part in source.parts do
    part.file.validate
    unless 0 < part.file.size && part.file.size ≤ maxPartBytes && part.first != inside do
      throw "Dump parts must cover complete XML documents in order"
    if seen.contains part.file.sha256 then throw "Duplicate dump part"
    seen := seen.insert part.file.sha256
    inside := !part.last
  if inside then throw "Missing last dump part"

private def validDataset (dataset : Dataset) : Except String Unit := do
  dataset.source.validate
  unless dataset.format == "wiki/dataset/v1" && !dataset.label.isEmpty &&
      dataset.label.utf8ByteSize ≤ 1024 && dataset.namespaceId ≤ 100000 &&
      dataset.shards.size ≤ maxParts do
    throw "Invalid or oversized dataset manifest"
  let mut seen : Std.HashSet String := {}
  for shard in dataset.shards do
    shard.file.validate
    unless 0 < shard.file.size && shard.file.size ≤ maxShardBytes && shard.articles > 0 do
      throw "Invalid article shard"
    if seen.contains shard.file.sha256 then throw "Duplicate dataset shard"
    seen := seen.insert shard.file.sha256

def preparePart (store : ObjectStore) (r : PrepareRequest) (part : Part) : IO (Array Shard) :=
  IO.FS.withTempDir fun directory => do
    IO.ofExcept r.validate
    let input := directory / "dump"
    Files.download store part.file input maxPartBytes
    let counts ← Native.normalize input.toString directory.toString part.compressed part.first part.last
      r.namespaceId.toUInt32 r.includeRedirects r.shardBytes.toUInt64
    counts.mapIdxM fun i count => do
      let file ← Files.upload store (directory / s!"{i}.jsonl") maxShardBytes
      return { file, articles := count }

private def checkDeadline (deadline : Nat) : IO Unit := do
  unless (← IO.monoMsNow) ≤ deadline do throw (IO.userError "Analysis time limit exceeded")

private def articleLines (store : IO ObjectStore) (ranges : Array (ByteRange FileRef))
    (timeoutMs : Nat := 300000) :
    ReducerParIO (String × Article) where
  run := fun cfg q => do
    let deadline := (← IO.monoMsNow) + timeoutMs
    let store ← store
    -- A finished IO request cannot start another one after the budget expires.
    -- Transport timeouts still bound each individual request.
    let bounded := { store with read := fun key => do
      checkDeadline deadline
      let bytes ← store.read key
      checkDeadline deadline
      return bytes }
    let source := (ReducerCloud.blobLines (pure bounded) ranges false).tryMap
      fun (file, line) => do return (file.sha256, ← parseArticle line)
    let result ← source.run cfg q
    checkDeadline deadline
    return result

private def excerpt (text : String) (offset : Nat) : String := Id.run do
  let bytes := text.toUTF8
  let stop := min bytes.size (offset + 240)
  -- Native regex offsets are bytes; keep the displayed excerpt valid UTF-8.
  for front in [:4] do
    for back in [:4] do
      if let some s := String.fromUTF8? (bytes.extract (offset + front) (stop - back)) then return s
  return ""

/-- A byte partition owns its matcher and output. Local IO tasks run these
partitions concurrently; the shared reducer handles seeks and line boundaries. -/
def grepRange (store : ObjectStore) (r : GrepRequest) (range : ByteRange FileRef)
    (timeoutMs : Nat := 300000) : IO Matches := do
  IO.ofExcept r.validate
  let matcher ← Native.matcher r.pattern r.regex r.ignoreCase
  let deadline := (← IO.monoMsNow) + timeoutMs
  let source := (articleLines (pure store) #[range] timeoutMs).map Prod.snd
  -- A range is bounded (8 MiB plus a boundary article), never an entire dump.
  -- The outer IO reducer already owns the local CPU budget.
  let articles ← source.reduceWithoutLaws ([] : List Article) (· ++ ·) (· :: ·) { maxDepth := 0 }
  IO.FS.withTempFile fun output path => do
    let mut matched := 0
    let mut bytes := 0
    for article in articles do
      checkDeadline deadline
      if let some (offset, length) ← Native.find matcher article.text then
        let hit : Hit := { id := article.id, revision := article.revision, title := article.title
                           offset, length, excerpt := excerpt article.text offset }
        let line := (toJson hit).compress ++ "\n"
        bytes := bytes + line.utf8ByteSize
        unless bytes ≤ r.maxOutputBytes do
          throw (IO.userError "Grep output limit exceeded; use smaller shards or a narrower pattern")
        output.putStr line
        matched := matched + 1
      checkDeadline deadline
    output.flush
    return { file := ← Files.upload store path r.maxOutputBytes, articles := articles.length, matched }

/-- Resolve the blob service only inside worker effects, never while the
scheduler reconstructs a workflow or lists its registered programs. -/
def backendWith (getStore : IO ObjectStore) (rangeBytes : Nat := 8 * MiB)
    (analysisTimeoutMs : Nat := 300000) : Backend IO where
  source ref := do
    let value : Source ← metadata (← getStore) ref
    IO.ofExcept (validParts value)
    return value
  parts r parts :=
    (ReducerCloud.ofArrayIO parts (fun _ part => do preparePart (← getStore) r part)
      (fun part => part.file.size)).flatMap ReducerSeq.ofArray
  publish value := do
    IO.ofExcept (validDataset value)
    Files.putJson (← getStore) value
  dataset ref := do
    let value : Dataset ← metadata (← getStore) ref
    IO.ofExcept (validDataset value)
    return value
  articles dataset :=
    ReducerCloud.ofPartitions (ReducerCloud.fileRanges (dataset.shards.map (·.file)) rangeBytes)
      (fun _ ranges => articleLines getStore ranges analysisTimeoutMs) (·.size)
  saveCounts counts := do Files.putJson (← getStore) counts
  sumCounts r dataset parts := do
    let store ← getStore
    let mut total := mergeCounts r #[]
    let mut perFile := #[]
    for part in parts do
      let table : CountPartial ← metadata store part
      unless table.total.counts.map (·.word) == r.vocabulary do
        throw (IO.userError "Count table does not match the requested vocabulary")
      total := mergeCounts r #[total, table.total]
      perFile := table.perFile.foldl (fun acc (key, n) => addFileCount acc key n) perFile
    IO.ofExcept (checkArticleCounts dataset perFile)
    return total
  search r dataset :=
    ReducerCloud.ofArrayIO (ReducerCloud.fileRanges (dataset.shards.map (·.file)) rangeBytes)
      (fun _ range => do return (range.source.sha256, ← grepRange (← getStore) r range analysisTimeoutMs)) (·.size)
  validateGrep r := do discard (Native.matcher r.pattern r.regex r.ignoreCase)
  publishMatches r dataset parts := do
    let perFile := parts.foldl (fun acc (key, part) => addFileCount acc key part.articles) #[]
    IO.ofExcept (checkArticleCounts dataset perFile)
    let sizes := parts.foldl (fun acc (key, part) => addFileCount acc key part.file.size) #[]
    unless sizes.all (fun (_, bytes) => bytes ≤ r.maxOutputBytes) do
      throw (IO.userError "Grep output limit exceeded; use smaller shards or a narrower pattern")
    Files.putJson (← getStore) ({ request := r, parts := parts.map Prod.snd } : MatchManifest)

def backend (store : ObjectStore) : Backend IO := backendWith (pure store)

end Wiki
