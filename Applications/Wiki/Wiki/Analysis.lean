import Wiki.Model

namespace Wiki

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

end Wiki
