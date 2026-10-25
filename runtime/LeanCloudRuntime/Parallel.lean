import Std.Sync.Mutex

namespace LeanCloudRuntime.Parallel

/-- A bounded pool for blocking IO and file processing. Results retain input
order. All started tasks are joined, including on failure, before the caller
can remove its temporary files. A failed action stops accepting new work. -/
def map (concurrency : Nat) (items : Array α) (action : α → IO β) : IO (Array β) := do
  let count := min (max 1 concurrency) items.size
  if count ≤ 1 then return ← items.mapM action
  let next ← Std.Mutex.new (0 : Nat)
  -- Keep started tasks across exceptions: local `let mut` updates inside `try`
  -- are not carried into `finally` when the body throws.
  let tasks ← IO.mkRef (#[] : Array (Task (Except IO.Error (Array (Nat × β)))))
  try
    for _ in [:count] do
      let task ← IO.asTask (do
        let mut results := #[]
        try
          repeat
            let index ← next.atomically do
              let index ← get
              set (index + 1)
              return index
            let some item := items[index]? | break
            results := results.push (index, ← action item)
          return results
        catch error =>
          next.atomically (set items.size)
          throw error) .dedicated
      tasks.modify (·.push task)
    let mut results := #[]
    for task in ← tasks.get do results := results ++ (← IO.ofExcept (← IO.wait task))
    return (results.qsort (fun a b => a.1 < b.1)).map (·.2)
  finally
    for task in ← tasks.get do discard <| IO.wait task

end LeanCloudRuntime.Parallel
