import Wiki.Workflow
import Wiki.Analysis
import Wiki.Native

namespace Wiki
open Lean LeanCloudRuntime

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

/-- Download one bounded shard, then stream one NDJSON article at a time. The
manifest checksum is verified before any analysis. No whole-dataset materialization. -/
def foldShard (store : ObjectStore) (shard : Shard) (initial : α)
    (step : α → Article → IO α) : IO α := IO.FS.withTempFile fun _ path => do
  Files.download store shard.file path maxShardBytes
  let input ← IO.FS.Handle.mk path .read
  let mut state := initial
  let mut count := 0
  let deadline := (← IO.monoMsNow) + 300000
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    unless line.utf8ByteSize ≤ 64 * MiB && (← IO.monoMsNow) ≤ deadline do
      throw (IO.userError "Article size or analysis time limit exceeded")
    let article : Article ← IO.ofExcept (Json.parse line >>= fromJson?)
    unless article.text.utf8ByteSize ≤ 8 * MiB && article.title.utf8ByteSize ≤ 8 * MiB &&
        !article.text.contains '\x00' do throw (IO.userError "Invalid article fields")
    state ← step state article
    unless (← IO.monoMsNow) ≤ deadline do
      throw (IO.userError "Analysis time limit exceeded")
    count := count + 1
  unless count == shard.articles do throw (IO.userError "Article count does not match manifest")
  return state

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

def countShard (store : ObjectStore) (r : CountRequest) (shard : Shard) : IO Counts := do
  IO.ofExcept r.validate
  let table := vocabulary r
  foldShard store shard { counts := r.vocabulary.map fun word => { word } } fun counts article =>
    pure (addArticle counts (wordHits table r.ignoreCase article.text))

private def excerpt (text : String) (offset : Nat) : String := Id.run do
  let bytes := text.toUTF8
  let stop := min bytes.size (offset + 240)
  -- Native regex offsets are bytes; keep the displayed excerpt valid UTF-8.
  for front in [:4] do
    for back in [:4] do
      if let some s := String.fromUTF8? (bytes.extract (offset + front) (stop - back)) then return s
  return ""

def grepShard (store : ObjectStore) (r : GrepRequest) (shard : Shard) : IO Matches := do
  IO.ofExcept r.validate
  let matcher ← Native.matcher r.pattern r.regex r.ignoreCase
  IO.FS.withTempFile fun output path => do
    let (matched, _) ← foldShard store shard (0, 0) fun (matched, bytes) article => do
      let some (offset, length) ← Native.find matcher article.text | return (matched, bytes)
      let hit : Hit := { id := article.id, revision := article.revision, title := article.title
                         offset, length, excerpt := excerpt article.text offset }
      let line := (toJson hit).compress ++ "\n"
      let bytes := bytes + line.utf8ByteSize
      unless bytes ≤ r.maxOutputBytes do throw (IO.userError "Grep output limit exceeded; use smaller shards or a narrower pattern")
      output.putStr line
      return (matched + 1, bytes)
    output.flush
    return { file := ← Files.upload store path r.maxOutputBytes, articles := shard.articles, matched }

def backend (store : ObjectStore) : Backend IO where
  source ref := do
    let value : Source ← metadata store ref
    IO.ofExcept (validParts value)
    return value
  prepare := preparePart store
  publish value := do
    IO.ofExcept (validDataset value)
    Files.putJson store value
  dataset ref := do
    let value : Dataset ← metadata store ref
    IO.ofExcept (validDataset value)
    return value
  count r shard := do Files.putJson store (← countShard store r shard)
  sumCounts r parts := do
    let mut total := mergeCounts r #[]
    for part in parts do
      let table : Counts ← metadata store part
      unless table.counts.map (·.word) == r.vocabulary do
        throw (IO.userError "Count table does not match the requested vocabulary")
      total := mergeCounts r #[total, table]
    return total
  grep := grepShard store
  validateGrep r := do discard (Native.matcher r.pattern r.regex r.ignoreCase)
  publishMatches := Files.putJson store

end Wiki
