import LeanCloudReducers.Core
import LeanCloudRuntime.Files

namespace LeanCloud
open LeanReducers LeanCloudRuntime

namespace ReducerCloud

private instance : Inhabited (ByteRange FileRef) := ⟨⟨default, 0, 0⟩⟩

/-- Partition immutable file descriptors without downloading contents. This
uses lean-reducers' byte partitioner, also used by its local file reader. -/
def fileRanges (files : Array FileRef) (bytes : Nat := 8 * 1024 * 1024) : Array (ByteRange FileRef) :=
  ByteRange.partition (files.map fun file => ⟨file, 0, file.size⟩) bytes

/-- The adapter fetches and verifies only the blob chunks intersecting a read.
All seeking, UTF-8/newline boundary repair and multicore folding live in
lean-reducers. Manifest indexes and one-chunk caches are shared within a batch. -/
def blobLines (store : IO ObjectStore) (ranges : Array (ByteRange FileRef))
    (trailingEmpty : Bool := true) : ReducerParIO (FileRef × String) where
  run := fun cfg q => do
    let store ← store
    let mut result := q.unit
    -- Group adjacent ranges of a file so the library can share one task tree
    -- and chunk cache. Files themselves are kept in input order.
    let mut index := 0
    while index < ranges.size do
      let range := ranges[index]!
      let reader ← Files.openReader store range.source
      let source : ByteSource := { size := reader.size, read := reader.read, name := range.source.manifest.key }
      let mut batch := #[]
      while index < ranges.size && ranges[index]!.source == range.source do
        batch := batch.push ((ranges[index]!).map (fun _ => source))
        index := index + 1
      let value ← (ReducerPar.readSourceRanges batch trailingEmpty).run cfg {
        unit := q.unit, combine := q.combine, step := fun line acc => q.step (range.source, line) acc }
      result := q.combine result value
    return result

/-- Distributed line reduction, including files much larger than any worker's
memory. Only descriptors are replayed; a worker reads its assigned ranges. -/
def readLinesWithFile (store : IO ObjectStore) (files : Array FileRef)
    (rangeBytes : Nat := 8 * 1024 * 1024) (trailingEmpty : Bool := true) : ReducerCloudIO (FileRef × String) :=
  ofPartitions (fileRanges files rangeBytes)
    (fun _ ranges => blobLines store ranges trailingEmpty) (·.size)

def readLines (store : IO ObjectStore) (files : Array FileRef)
    (rangeBytes : Nat := 8 * 1024 * 1024) (trailingEmpty : Bool := true) : ReducerCloudIO String :=
  (readLinesWithFile store files rangeBytes trailingEmpty).map Prod.snd

end ReducerCloud
end LeanCloud
