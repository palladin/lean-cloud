import LeanCloudCli.Docker
import LeanCloudCli.Styled

namespace LeanCloudCli
open Lean LeanCloud

structure Node where
  name : String
  state : String
  started : String
  role : String := ""
  health : Option String := none
  deriving Inhabited

structure Sample where
  time : Nat
  session : String
  cpu : Nat
  memory : Nat
  limit : Nat
  rx : Nat
  tx : Nat
  readBytes : Nat
  writeBytes : Nat
  deriving Inhabited

/-- Decimal fixed-point parser (three places) for Docker's formatted counters. -/
def decimal (text : String) : Nat :=
  let parts := text.splitOn "."
  let whole := parts.head!.toNat?.getD 0
  let fraction := parts[1]?.getD ""
  whole * 1000 + ((fraction ++ "000").take 3 |>.toString.toNat?.getD 0)

def bytes (text : String) : Nat :=
  let text := text.trimAscii.toString
  let number := String.ofList (text.toList.takeWhile fun c => c.isDigit || c == '.')
  let unit := text.drop number.length |>.toString.trimAscii.toString
  let scale := match unit with
    | "kB" | "KB" => 1000 | "MB" => 1000000 | "GB" => 1000000000 | "TB" => 1000000000000
    | "KiB" => 1024 | "MiB" => 1048576 | "GiB" => 1073741824 | "TiB" => 1099511627776
    | _ => 1
  decimal number * scale / 1000

private def counters (text : String) : Nat × Nat :=
  let values := text.splitOn "/"
  (bytes values.head!, bytes (values[1]?.getD "0"))

private def field (json : Json) (key : String) : String :=
  (json.getObjValAs? String key).toOption.getD ""

def decodeSample (time : Nat) (session : String) (json : Json) : Sample :=
  let (memory, limit) := counters (field json "MemUsage")
  let (rx, tx) := counters (field json "NetIO")
  let (readBytes, writeBytes) := counters (field json "BlockIO")
  ⟨time, session, decimal ((field json "CPUPerc").replace "%" ""), memory, limit, rx, tx, readBytes, writeBytes⟩

/-- Restarted containers start a new counter series; missing samples are gaps. -/
def rate (before after : Sample) (counter : Sample → Nat) : Option Nat :=
  if before.session != after.session || after.time ≤ before.time || counter after < counter before then none
  else some ((counter after - counter before) * 1000 / (after.time - before.time))

def Context.nodes (ctx : Context) : Cli (Array Node) := do
  let actors ← docker #["ps", "-aq", "--filter", "label=lean-cloud.project=" ++ ctx.project]
  let services ← docker #["ps", "-aq", "--filter", "label=com.docker.compose.project=" ++ ctx.project]
  -- Compose build labels can be inherited by directly launched containers, so
  -- an actor may occur in both inventories. Inspect/sample each container once.
  let ids := ((actors.stdout ++ "\n" ++ services.stdout).splitOn "\n").foldl
    (fun (ids : Array String) id => if id.isEmpty || ids.contains id then ids else ids.push id) #[]
  if ids.isEmpty then return #[]
  let output ← docker (#["inspect"] ++ ids)
  let rows ← liftExcept (Json.parse output.stdout >>= Json.getArr?)
  return rows.map fun row =>
    let state := (row.getObjVal? "State").toOption.getD Json.null
    let labels := ((row.getObjVal? "Config") >>= (·.getObjVal? "Labels")).toOption.getD Json.null
    { name := (field row "Name").drop 1 |>.toString
      state := field state "Status", started := field state "StartedAt"
      role := (labels.getObjValAs? String "lean-cloud.role").toOption.getD (field labels "com.docker.compose.service")
      health := (state.getObjVal? "Health" >>= (·.getObjValAs? String "Status")).toOption }

structure DiskUsage where
  path : String
  used : Nat
  capacity : Nat

def decodeFilesystem (path output : String) : Option DiskUsage := do
  let fields := (output.trimAscii.toString.splitOn "\n").getLast!.splitOn " " |>.filter (!·.isEmpty)
  let capacity ← fields[1]? >>= String.toNat?
  let used ← fields[2]? >>= String.toNat?
  if capacity == 0 then none else some ⟨path, used * 1024, capacity * 1024⟩

/-- Filesystem capacity, not bytes attributed to a single container or volume. -/
def filesystem (node : Node) : Cli (Option DiskUsage) := do
  if node.state != "running" then return none
  let path := if node.role == "scheduler" || node.role == "blobs" then "/data"
    else if isActor node.role then "/mailbox" else "/"
  let output ← docker #["exec", node.name, "df", "-Pk", path] false
  if output.exitCode != 0 then return none
  return decodeFilesystem path output.stdout

def samples (nodes : Array Node) : Cli (Array (String × Sample)) := do
  let running := nodes.filter (·.state == "running")
  if running.isEmpty then return #[]
  let output ← docker (#["stats", "--no-stream", "--format", "{{json .}}"] ++ running.map (·.name))
  let now ← request .now
  let mut values := #[]
  for line in output.stdout.splitOn "\n" do
    if let .ok value := Json.parse line then
      let name := field value "Name"
      if let some node := running.find? (·.name == name) then
        let sample := decodeSample now node.started value
        -- Docker can race with container exit and return an all-zero row.
        if sample.limit > 0 then values := values.push (name, sample)
  return values

def humanBytes (value : Nat) : String :=
  if value ≥ 1073741824 then s!"{value / 1073741824}.{value % 1073741824 * 10 / 1073741824} GiB"
  else if value ≥ 1048576 then s!"{value / 1048576}.{value % 1048576 * 10 / 1048576} MiB"
  else if value ≥ 1024 then s!"{value / 1024}.{value % 1024 * 10 / 1024} KiB"
  else s!"{value} B"

def percent (value : Nat) : String :=
  let fraction := toString (value % 1000 / 10)
  s!"{value / 1000}.{if fraction.length == 1 then "0" ++ fraction else fraction}%"

def spark (values : Array (Option Nat)) (width : Nat := 24) (scale : Option Nat := none) : String := Id.run do
  let values := values.extract (values.size - width) values.size
  let peak := max 1 (scale.getD (values.foldl (fun n v => max n (v.getD 0)) 0))
  let marks := "▁▂▃▄▅▆▇█".toList.toArray
  let mut result := String.ofList (List.replicate (width - values.size) ' ')
  for value in values do
    result := result.push (match value with
      | none => '·'
      | some 0 => '_'
      | some n => marks[min 7 ((n * 8 + peak - 1) / peak - 1)]!)
  return result

structure History where
  name : String
  points : Array Sample := #[]
  fresh : Bool := true
  deriving Inhabited

def remember (histories : Array History) (values : Array (String × Sample)) : Array History :=
  values.foldl (fun history (name, sample) =>
    match history.findIdx? (·.name == name) with
    | none => history.push ⟨name, #[sample], true⟩
    | some i =>
      let points := if history[i]!.points.back?.map (·.session) == some sample.session then history[i]!.points else #[]
      let points := points.push sample
      history.set! i ⟨name, points.extract (points.size - 30) points.size, true⟩)
    (histories.map fun history => { history with fresh := false })

private def pressure (used capacity : Nat) : Styled.Color :=
  if used * 100 ≥ capacity * 90 then .red
  else if used * 100 ≥ capacity * 70 then .yellow else .green

/-- A fixed-capacity meter. Overflow stays visible as `+` and in the numeric
value; missing capacity is not rendered as an empty (zero-usage) meter. -/
def meter (used capacity width : Nat) : Styled.Line := Id.run do
  if capacity == 0 then return Styled.text "[unavailable]" .muted
  let filled := min width ((used * width + capacity - 1) / capacity)
  let color := pressure used capacity
  let bars := String.ofList (List.replicate filled '|')
  let bars := if used > capacity && width > 0 then
    String.ofList (bars.toList.take (width - 1)) ++ "+" else bars
  return Styled.text "[" .muted ++ Styled.text bars color ++
    Styled.text (String.ofList (List.replicate (width - filled) '·')) .muted ++ Styled.text "]" .muted

private def usageLine (label : String) (used capacity : Nat) (detail : String)
    (width : Nat) (history : Array (Option Nat) := #[]) : Styled.Line :=
  let room := width - 6 - detail.length - 3
  let historyWidth := if !history.isEmpty && room ≥ 26 then min 18 (room / 2) else 0
  let barWidth := min 24 (room - (if historyWidth > 0 then historyWidth + 1 else 0))
  Styled.text (pad 6 label) .cyan ++
    (if barWidth ≥ 4 then meter used capacity barWidth ++ Styled.text " " else #[]) ++
    Styled.text detail (if capacity == 0 then .muted else pressure used capacity) ++
    (if historyWidth > 0 then Styled.text (" " ++ spark history historyWidth (some capacity)) .green else #[])

def metricLines (points : Array Sample) (width : Nat := 56)
    (disk : Option DiskUsage := none) : Array Styled.Line := Id.run do
  let some current := points.back? | return #[Styled.text "No sample: node stopped or unavailable" .muted]
  let direct (select : Sample → Nat) := points.map (fun p => some (select p))
  let rates (select : Sample → Nat) := (Array.range points.size).map fun i =>
    if i == 0 then none else rate points[i - 1]! points[i]! select
  let rateLine (label : String) (color : Styled.Color) (select : Sample → Nat) :=
    let values := rates select
    let value := match (values.back? >>= id) with | some n => humanBytes n ++ "/s" | none => "—"
    let graphWidth := min 30 (width - 8 - value.length)
    Styled.text (pad 7 label) color ++ Styled.text (spark values graphWidth) color ++
      Styled.text (" " ++ value) (if (values.back? >>= id).isSome then color else .muted)
  let mut lines := #[
    usageLine "CPU" current.cpu 100000 (percent current.cpu) width (direct (·.cpu)),
    usageLine "Mem" current.memory current.limit
      s!"{humanBytes current.memory} / {humanBytes current.limit}" width (direct (·.memory))]
  lines := lines ++ (match disk with
    | some disk => #[usageLine "Disk" disk.used disk.capacity
        s!"{humanBytes disk.used} / {humanBytes disk.capacity}" width,
        Styled.text s!"      filesystem {disk.path}" .muted]
    | none => #[Styled.text "Disk  unavailable" .muted])
  return lines ++ #[rateLine "Net RX" .cyan (·.rx), rateLine "Net TX" .magenta (·.tx),
    rateLine "I/O R" .blue (·.readBytes), rateLine "I/O W" .yellow (·.writeBytes)]

end LeanCloudCli
