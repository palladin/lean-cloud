import LeanCloud.ExecServices
import Std.Data.HashSet

namespace LeanBuild.Prefetch
open Lean LeanCloud

/-- Follow the available queue without claiming work. Downloads are admitted in
queue order and joined on exit. Completed candidates are skipped on later scans;
each page continues by position, not an offset into a shrinking queue.

Revisit the head every 200 ms so newly ready, higher-priority work overtakes the
unstarted lookahead. Once the head is warm, continue through the entire queue.
There is no page barrier: a free download slot immediately takes the next item. -/
def run (queue : WorkQueue IO) (stop : CancellationToken IO) (concurrency : Nat)
    (prepare : CancellationToken IO → Json → IO Unit) : IO Unit := do
  let stopped ← IO.mkRef false
  let stop : CancellationToken IO := ⟨do return (← stopped.get) || (← stop.isRequested)⟩
  let running ← IO.mkRef (#[] : Array (Nat × Task (Except IO.Error Unit)))
  try
    let mut warmed : Std.HashSet Nat := {}
    let mut pending : Array WorkPreview := #[]
    let mut after : Option WorkPosition := none
    let mut nextHead := 0
    let mut nextPage := 0
    repeat
      if ← stop.isRequested then break
      let mut active := #[]
      for (id, task) in ← running.get do
        if ← IO.hasFinished task then
          IO.ofExcept (← IO.wait task)
          warmed := warmed.insert id
        else active := active.push (id, task)
      running.set active
      let unseen := fun (item : WorkPreview) =>
        !warmed.contains item.position.sequence && !active.any (·.1 == item.position.sequence)
      pending := pending.filter unseen
      let now ← IO.monoMsNow
      if now ≥ nextHead then
        let head ← queue.peek none 100
        let candidates := head.filter unseen
        unless candidates.isEmpty do
          pending := candidates
          after := head.back?.map (·.position)
        nextHead := now + 200
      if pending.isEmpty && active.size < max 1 concurrency && now ≥ nextPage then
        let page ← queue.peek after 100
        after := page.back?.map (·.position)
        pending := page.filter unseen
        -- Advance quickly while there is useful work, but do not spin through
        -- already-warm pages and repeatedly load the queue service.
        if pending.isEmpty then nextPage := now + 200
      while (← running.get).size < max 1 concurrency && !pending.isEmpty do
        if ← stop.isRequested then break
        let some item := pending[0]? | break
        pending := pending.extract 1 pending.size
        let task ← IO.asTask (prepare stop item.value) .dedicated
        running.modify (·.push (item.position.sequence, task))
      IO.sleep 10
  finally
    stopped.set true
    for (_, task) in ← running.get do discard <| IO.wait task

end LeanBuild.Prefetch
