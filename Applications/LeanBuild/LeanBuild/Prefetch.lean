import LeanBuild.Prefetch.Program

namespace LeanBuild.Prefetch
open Lean LeanCloud

/-- IO owns the task scope. Failure or cancellation stops admission and joins
all started transfers before returning to the workspace owner. -/
def run (queue : WorkQueue IO) (stop : CancellationToken IO) (concurrency : Nat)
    (prepare : CancellationToken IO → Json → IO Unit) : IO Unit := do
  let stopped ← IO.mkRef false
  let stop : CancellationToken IO := ⟨do return (← stopped.get) || (← stop.isRequested)⟩
  let running ← IO.mkRef (#[] : Array (Nat × Task (Except IO.Error Unit)))
  let execute : {α : Type} → Operation α → IO α := fun {α} op =>
    match op with
    | .peek after => queue.peek after 100
    | .start item => do
      unless ← stop.isRequested do
        let task ← IO.asTask (prepare stop item.value) .dedicated
        running.modify (·.push (item.position.sequence, task))
    | .observe => do
      IO.sleep 10
      let mut active := #[]
      let mut completed := #[]
      for (id, task) in ← running.get do
        if ← IO.hasFinished task then
          IO.ofExcept (← IO.wait task)
          completed := completed.push id
        else active := active.push (id, task)
      running.set active
      return (← IO.monoMsNow, completed, ← stop.isRequested)
  let handle : {α : Type} → Operation α → IO (Except String α) := fun op => do
    try return .ok (← execute op) catch e => return .error e.toString

  try
    IO.ofExcept (← runWith handle (program concurrency))
  finally
    stopped.set true
    for (_, task) in ← running.get do discard <| IO.wait task

end LeanBuild.Prefetch
