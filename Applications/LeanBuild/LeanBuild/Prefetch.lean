import LeanBuild.Prefetch.Program
import LeanBuild.BuildIO

namespace LeanBuild.Prefetch
open Lean LeanCloud

/-- IO owns the task scope. Typed failures stop admission; all transfers are
joined, and later cleanup failures cannot replace the original cause. -/
def runTyped (queue : WorkQueue IO) (stop : CancellationToken IO) (concurrency : Nat)
    (prepare : CancellationToken IO → Json → BuildIO Unit) : BuildIO Unit := ExceptT.mk do
  let stopped ← IO.mkRef false
  let stop : CancellationToken IO := ⟨do return (← stopped.get) || (← stop.isRequested)⟩
  let running ← IO.mkRef (#[] : Array (Nat × Task (Except IO.Error (Except BuildError Unit))))
  let execute : {α : Type} → Operation α → BuildIO α := fun op =>
    match op with
    | .peek after => BuildIO.capture .network (queue.peek after 100)
    | .start item => do
      unless ← stop.isRequested do
        let task ← IO.asTask (BuildIO.outcome (prepare stop item.value)) .dedicated
        running.modify (·.push (item.position.sequence, task))
    | .observe => do
      IO.sleep 10
      let mut completed := #[]
      for (id, task) in ← running.get do
        if ← IO.hasFinished task then
          running.modify (·.filter (fun entry => entry.1 != id))
          let outcome ← liftExcept ((← IO.wait task).mapError (BuildError.tool ∘ toString))
          liftExcept outcome
          completed := completed.push id
      return (← IO.monoMsNow, completed, ← stop.isRequested)
  let result ← BuildIO.outcome (ExceptT.mk (runWith (fun op => (execute op).run) (program concurrency)))
  stopped.set true
  let mut result := result
  for (_, task) in ← running.get do
    let outcome := (← IO.wait task).mapError (BuildError.tool ∘ toString) |>.bind id
    if let .error error := outcome then
      unless error.isCancelled do result := BuildError.after result (.error error)
  return result

def run (queue : WorkQueue IO) (stop : CancellationToken IO) (concurrency : Nat)
    (prepare : CancellationToken IO → Json → IO Unit) : IO Unit :=
  (runTyped queue stop concurrency fun childStop value => BuildIO.capture .tool (prepare childStop value)).toIO

end LeanBuild.Prefetch
