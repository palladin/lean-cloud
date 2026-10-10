import LeanCloud.ReplayInterpreter

namespace LeanCloud.ReplayModel

/-- A pure model of global replay records. It has no user-effect world, scheduler,
or queue. Proofs run the ordinary replay interpreter against these ports. -/
abbrev Journal := List (String × ReplayRecord)
abbrev M := StateM Journal

/-- The pure reference model has no user blob effects. Pure evaluation never
calls these operations; rejecting them also makes accidental use explicit. -/
def noBlobs : BlobStorage M where
  putBlob _ := throw ⟨.unsupported, "User blobs are outside the pure replay model"⟩
  readBlob _ := throw ⟨.unsupported, "User blobs are outside the pure replay model"⟩
  resolveBlob _ := throw ⟨.unsupported, "User blobs are outside the pure replay model"⟩

def store : ReplayStore M where
  read key := fun journal => (journal.lookup key, journal)
  create key proposed := fun journal =>
    match journal.lookup key with
    | some existing => (existing, journal)
    | none => (proposed, (key, proposed) :: journal)

/-- `store` only prepends new records. The old journal remains its immutable
tail; a worker returns just the prefix it added, never the shared tail. -/
def newRecords (before after : Journal) : Journal :=
  after.take (after.length - before.length)

/-- Disjoint union. Any repeated key is an ownership error, even when the two
records have identical values. There is no reconciliation or deduplication. -/
def merge (journal records : Journal) : Except CloudError Journal :=
  if (records.map Prod.fst).Nodup ∧ ∀ entry ∈ records, journal.lookup entry.1 = none then
    .ok (records ++ journal)
  else .error ⟨.divergence, "Overlapping parallel replay writes"⟩

end LeanCloud.ReplayModel
