import LeanCloudRuntime.Files

namespace Wiki
open Lean LeanCloud LeanCloudRuntime

abbrev FileRef := LeanCloudRuntime.FileRef

def MiB : Nat := 1024 * 1024
def maxPartBytes : Nat := 256 * MiB
def maxShardBytes : Nat := 128 * MiB
def maxParts : Nat := 10000

/-- A complete dump, or consecutive complete bzip2 streams from one dump.
Only the first and last pieces contain the original XML root boundaries. -/
structure Part where
  file : FileRef
  compressed : Bool
  first : Bool
  last : Bool
  deriving Repr, BEq, ToJson, FromJson

structure Source where
  format : String := "wiki/source/v1"
  label : String
  parts : Array Part
  deriving Repr, ToJson, FromJson

structure Article where
  id : Nat
  revision : Nat
  title : String
  ns : Nat
  text : String
  deriving Repr, BEq, ToJson, FromJson

structure Shard where
  file : FileRef
  articles : Nat
  deriving Repr, BEq, ToJson, FromJson

structure Dataset where
  format : String := "wiki/dataset/v1"
  label : String
  source : FileRef
  namespaceId : Nat
  includeRedirects : Bool
  shards : Array Shard
  deriving Repr, ToJson, FromJson

structure PrepareRequest where
  source : FileRef
  shardBytes : Nat := 32 * MiB
  namespaceId : Nat := 0
  includeRedirects : Bool := false
  deriving Repr, ToJson

structure Prepared where
  dataset : FileRef
  articles : Nat
  shards : Nat
  deriving Repr, BEq, ToJson, FromJson

structure CountRequest where
  dataset : FileRef
  vocabulary : Array String
  ignoreCase : Bool := true
  deriving Repr, ToJson

structure Count where
  word : String
  occurrences : Nat := 0
  articles : Nat := 0
  deriving Repr, BEq, ToJson, FromJson

structure Counts where
  articles : Nat := 0
  counts : Array Count
  deriving Repr, BEq, ToJson, FromJson

/-- Worker-local aggregate stored in blobs. Per-file totals validate manifests
even when one file is split across several workers. -/
structure CountPartial where
  total : Counts
  perFile : Array (String × Nat) := #[]
  deriving ToJson, FromJson

structure GrepRequest where
  dataset : FileRef
  pattern : String
  regex : Bool := false
  ignoreCase : Bool := false
  maxOutputBytes : Nat := 64 * MiB
  deriving Repr, ToJson

/-- One record per matching article: first match, UTF-8 byte position/length.
The excerpt starts at the match; it is not the entire article. -/
structure Hit where
  id : Nat
  revision : Nat
  title : String
  offset : Nat
  length : Nat
  excerpt : String
  deriving Repr, BEq, ToJson, FromJson

structure Matches where
  file : FileRef
  articles : Nat
  matched : Nat
  deriving Repr, BEq, ToJson, FromJson

structure GrepReport where
  results : FileRef
  articles : Nat
  matched : Nat
  deriving Repr, BEq, ToJson, FromJson

structure MatchManifest where
  format : String := "wiki/matches/v1"
  request : GrepRequest
  parts : Array Matches
  deriving Repr, ToJson

private def field [FromJson α] (j : Json) (key : String) (fallback : α) : Except String α := do
  match (← j.getObj?)[key]? with
  | none => pure fallback
  | some value => fromJson? value

instance : FromJson PrepareRequest where
  fromJson? j := do return {
    source := ← j.getObjValAs? _ "source"
    shardBytes := ← field j "shardBytes" (32 * MiB)
    namespaceId := ← field j "namespaceId" 0
    includeRedirects := ← field j "includeRedirects" false }
instance : FromJson CountRequest where
  fromJson? j := do return {
    dataset := ← j.getObjValAs? _ "dataset"
    vocabulary := ← j.getObjValAs? _ "vocabulary"
    ignoreCase := ← field j "ignoreCase" true }
instance : FromJson GrepRequest where
  fromJson? j := do return {
    dataset := ← j.getObjValAs? _ "dataset"
    pattern := ← j.getObjValAs? _ "pattern"
    regex := ← field j "regex" false
    ignoreCase := ← field j "ignoreCase" false
    maxOutputBytes := ← field j "maxOutputBytes" (64 * MiB) }
deriving instance FromJson for MatchManifest

/-- v1 vocabulary counts deliberately use ASCII words [A-Za-z]+. Grep handles
UTF-8 literals, including languages for which this tokenization is unsuitable. -/
def word (s : String) : Bool := !s.isEmpty && s.toList.all Char.isAlpha

def PrepareRequest.validate (r : PrepareRequest) : Except String Unit := do
  r.source.validate
  unless MiB ≤ r.shardBytes && r.shardBytes ≤ 64 * MiB && r.namespaceId ≤ 100000 do
    throw "shardBytes must be 1–64 MiB; namespace must be 0–100000"
def CountRequest.validate (r : CountRequest) : Except String Unit := do
  r.dataset.validate
  unless 0 < r.vocabulary.size && r.vocabulary.size ≤ 10000 &&
      r.vocabulary.all (fun s => word s && s.length ≤ 100) do
    throw "vocabulary must contain 1–10000 ASCII words, each at most 100 letters"
  let names := r.vocabulary.map fun s => if r.ignoreCase then s.toLower else s
  let mut seen : Std.HashSet String := {}
  for name in names do
    if seen.contains name then throw "Duplicate vocabulary entries after case normalization"
    seen := seen.insert name

private def hasBackReference (pattern : String) : Bool := Id.run do
  let mut escaped := false
  for char in pattern.toList do
    if escaped then
      if char.isDigit then return true
      escaped := false
    else
      escaped := char == '\\'
  return false

def GrepRequest.validate (r : GrepRequest) : Except String Unit := do
  r.dataset.validate
  unless !r.pattern.isEmpty && r.pattern.utf8ByteSize ≤ 4096 && !r.pattern.contains '\x00' &&
      0 < r.maxOutputBytes && r.maxOutputBytes ≤ maxShardBytes do
    throw "Invalid pattern or per-shard output limit"
  -- POSIX back references are not part of the supported extended-regexp subset.
  if r.regex && hasBackReference r.pattern then
    throw "Regex back references are unsupported"

instance : Codec FileRef := jsonCodec _ "lean-cloud/file-ref/v1"
deriving instance Inhabited for Count
deriving instance Inhabited for Matches
instance : Codec PrepareRequest := jsonCodec _ "wiki/prepare-request/v1"
instance : Codec CountRequest := jsonCodec _ "wiki/count-request/v1"
instance : Codec GrepRequest := jsonCodec _ "wiki/grep-request/v1"
instance : Codec Source := jsonCodec _ "wiki/source/v1"
instance : Codec Dataset := jsonCodec _ "wiki/dataset/v1"
instance : Codec Shard := jsonCodec _ "wiki/shard/v1"
instance : Codec Prepared := jsonCodec _ "wiki/prepared/v1"
instance : Codec Counts := jsonCodec _ "wiki/counts/v1"
instance : Codec Matches := jsonCodec _ "wiki/matches-part/v1"
instance : Codec GrepReport := jsonCodec _ "wiki/grep-report/v1"

end Wiki
