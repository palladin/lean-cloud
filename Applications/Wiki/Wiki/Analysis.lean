import Wiki.Model
import LeanReducers.FoldSpec

namespace Wiki
open Lean

abbrev Vocabulary := Std.HashMap String Nat

def vocabulary (r : CountRequest) : Vocabulary := Id.run do
  let mut table := {}
  for i in [:r.vocabulary.size] do
    let name := r.vocabulary[i]!
    table := table.insert (if r.ignoreCase then name.toLower else name) i
  return table

/-- One pass through UTF-8 bytes; ASCII words cannot cross a non-ASCII byte.
Only at most 100 bytes of a word are retained (the vocabulary's maximum length). -/
def wordHits (table : Vocabulary) (ignoreCase : Bool) (text : String) : Std.HashMap Nat Nat := Id.run do
  let mut counts : Std.HashMap Nat Nat := {}
  let mut token : ByteArray := {}
  let mut length := 0
  for byte in text.toUTF8 do
    let letter := (65 ≤ byte && byte ≤ 90) || (97 ≤ byte && byte ≤ 122)
    if letter then
      length := length + 1
      if length ≤ 100 then
        token := token.push (if ignoreCase && 65 ≤ byte && byte ≤ 90 then byte + 32 else byte)
    else
      if 0 < length && length ≤ 100 then
        if let some index := table[String.fromUTF8! token]? then
          counts := counts.insert index (counts.getD index 0 + 1)
      token := {}; length := 0
  if 0 < length && length ≤ 100 then
    if let some index := table[String.fromUTF8! token]? then
      counts := counts.insert index (counts.getD index 0 + 1)
  return counts

/-- Update only vocabulary entries present in this article. -/
def addArticle (counts : Counts) (hits : Std.HashMap Nat Nat) : Counts := Id.run do
  let mut entries := counts.counts
  for (index, n) in hits do
    entries := entries.modify index fun c => {
      c with occurrences := c.occurrences + n, articles := c.articles + 1 }
  return { articles := counts.articles + 1, counts := entries }

def mergeCounts (r : CountRequest) (parts : Array Counts) : Counts := {
  articles := parts.foldl (fun n p => n + p.articles) 0
  counts := r.vocabulary.mapIdx fun i name => {
    word := name
    occurrences := parts.foldl (fun n p => n + p.counts[i]!.occurrences) 0
    articles := parts.foldl (fun n p => n + p.counts[i]!.articles) 0 } }

def addFileCount (counts : Array (String × Nat)) (key : String) (value : Nat) : Array (String × Nat) :=
  match counts.findIdx? (·.1 == key) with
  | some i => counts.modify i fun (key, n) => (key, n + value)
  | none => counts.push (key, value)

def combineCounts (r : CountRequest) (left right : CountPartial) : CountPartial := {
  total := mergeCounts r #[left.total, right.total]
  perFile := right.perFile.foldl (fun acc (key, n) => addFileCount acc key n) left.perFile }

def countFold (r : CountRequest) : LeanReducers.FoldSpec (String × Article) CountPartial :=
  let table := vocabulary r
  { unit := { total := mergeCounts r #[] }
    combine := combineCounts r
    step := fun (key, article) acc => {
      total := addArticle acc.total (wordHits table r.ignoreCase article.text)
      perFile := acc.perFile.foldl (fun counts (key, n) => addFileCount counts key n) #[(key, 1)] } }

def checkArticleCounts (dataset : Dataset) (counts : Array (String × Nat)) : Except String Unit := do
  let totals := Std.HashMap.ofArray counts
  unless totals.size == dataset.shards.size && dataset.shards.all (fun shard =>
      totals[shard.file.sha256]? == some shard.articles) do
    throw "Article count does not match manifest"

/-- Checked parsing stays fused into the multicore reducer. -/
def parseArticle (line : String) : Except String Article := do
  unless line.utf8ByteSize ≤ 64 * MiB do throw "Article size limit exceeded"
  let article : Article ← Json.parse line >>= fromJson?
  unless article.text.utf8ByteSize ≤ 8 * MiB && article.title.utf8ByteSize ≤ 8 * MiB &&
      !article.text.contains '\x00' do throw "Invalid article fields"
  return article

end Wiki
