import LeanCloudCli.Monitor

namespace LeanCloudCli.SnapshotMetrics
open LeanCloud

/-- The last meter window in the saved view; no execution-history cursor. -/
def samples (observed : Array Trace.Step) (worker : String) : Array ResourceSample :=
  let values := observed.filterMap fun step =>
    if step.event.worker == worker then step.resources else none
  match values.back? with
  | none => #[]
  | some last =>
    let values := values.filter (·.incarnation == last.incarnation)
    values.extract (values.size - 30) values.size

def rate (before after : ResourceSample) (counter : ResourceSample → Option Nat)
    (scale := 1000000000) : Option Nat := do
  if before.incarnation != after.incarnation || after.timeNs ≤ before.timeNs then none else do
    let a ← counter before
    let b ← counter after
    if b < a then none else some ((b - a) * scale / (after.timeNs - before.timeNs))

def rates (points : Array ResourceSample) (counter : ResourceSample → Option Nat)
    (scale := 1000000000) : Array (Option Nat) :=
  (Array.range points.size).map fun i =>
    if i == 0 then none else rate points[i - 1]! points[i]! counter scale

private def value (format : Nat → String) (n : Option Nat) : String :=
  n.map format |>.getD "unavailable"

private def usage (label : String) (amount capacity : Option Nat) (detail : String) (width : Nat)
    (history : Array (Option Nat)) : Styled.Line :=
  let room := width - detail.length - label.length - 4
  Styled.text (label ++ " ") .cyan ++
    (if room ≥ 5 then
      (match amount, capacity with
       | some n, some c => meter n c (min 16 room) ++ Styled.text " "
       | _, _ => #[])
     else #[]) ++ Styled.text detail ++
    (if room ≥ 32 then Styled.text (" " ++ spark history 12 capacity) .green else #[])

/-- Raw container counters retain missing values. CPU and rates require two
samples in the same incarnation; a restart never turns them into false zeros. -/
def lines (points : Array ResourceSample) (width : Nat) : Array Styled.Line := Id.run do
  let some current := points.back? | return #[Styled.text "Stats: unavailable in last view" .muted]
  let cpu := rates points (·.cpuNs) 100000
  let cpuValue := cpu.back? >>= id
  let counter (label : String) (get : ResourceSample → Option Nat) :=
    let values := rates points get
    let detail := value (fun n => humanBytes n ++ "/s") (values.back? >>= id)
    Styled.text (pad 7 label) .cyan ++ Styled.text (spark values (min 16 (width - 9 - detail.length))) .green ++
      Styled.text (" " ++ detail)
  return #[
    usage "CPU" cpuValue (some 100000) (value percent cpuValue) width cpu,
    usage "Mem" current.memory current.memoryLimit
      (value humanBytes current.memory ++ " / " ++ value humanBytes current.memoryLimit) width (points.map (·.memory)),
    usage "Disk" current.diskUsed current.diskCapacity
      (value humanBytes current.diskUsed ++ " / " ++ value humanBytes current.diskCapacity) width (points.map (·.diskUsed)),
    counter "Net RX" (·.rx), counter "Net TX" (·.tx),
    counter "I/O R" (·.readBytes), counter "I/O W" (·.writeBytes)]

end LeanCloudCli.SnapshotMetrics
