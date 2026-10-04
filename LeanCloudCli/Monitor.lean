import LeanCloudCli.Docker

namespace LeanCloudCli
open Lean LeanCloud

structure Node where
  name : String
  state : String
  started : String
  run : Option String := none
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
      run := (labels.getObjValAs? String "lean-cloud.run").toOption
      role := (labels.getObjValAs? String "lean-cloud.role").toOption.getD (field labels "com.docker.compose.service")
      health := (state.getObjVal? "Health" >>= (·.getObjValAs? String "Status")).toOption }

def runNodes (run : Run) (nodes : Array Node) : Array Node :=
  let order (node : Node) : Nat := match node.role with
    | "worker1" => 0 | "worker2" => 1 | "worker3" => 2 | "scheduler" => 3 | _ => 4
  (nodes.filter (fun n => n.run.isNone || n.run == some run.id)).qsort fun a b =>
    order a < order b || (order a == order b && a.name < b.name)

/-- Filesystem capacity, not bytes attributed to a single container or volume. -/
def filesystem (node : Node) : Cli (Option String) := do
  if node.state != "running" then return none
  let path := if node.role == "scheduler" then "/data"
    else if (node.role.splitOn "mailbox").length > 1 then "/var/lib/rabbitmq" else "/"
  let output ← docker #["exec", node.name, "df", "-Pk", path] false
  if output.exitCode != 0 then return none
  let lines := output.stdout.trimAscii.toString.splitOn "\n"
  let fields := (lines.getLast!).splitOn " " |>.filter (!·.isEmpty)
  let some capacity := fields[1]? >>= String.toNat? | return none
  let some used := fields[2]? >>= String.toNat? | return none
  return some s!"Filesystem {path}: {used / 1024} / {capacity / 1024} MiB used"

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

def Context.events (ctx : Context) (run : Run) (knownNodes : Array Node := #[]) : Cli (Array (String × Array ExecutionEvent)) := do
  let nodes ← if knownNodes.isEmpty then ctx.nodes else pure knownNodes
  let mut result := #[]
  for worker in ["worker1", "worker2", "worker3"] do
    let name := ctx.container run worker
    let since := match nodes.find? (·.name == name) with
      | some node => if node.started.isEmpty then #[] else #["--since", node.started]
      | none => #[]
    let output ← docker (#["logs", "--tail", "80"] ++ since ++ #[name]) false
    let events := output.stdout.splitOn "\n" |>.filterMap event? |>.toArray
    result := result.push (worker, events)
  return result

def humanBytes (value : Nat) : String :=
  if value ≥ 1073741824 then s!"{value / 1073741824}.{value % 1073741824 * 10 / 1073741824} GiB"
  else if value ≥ 1048576 then s!"{value / 1048576}.{value % 1048576 * 10 / 1048576} MiB"
  else if value ≥ 1024 then s!"{value / 1024}.{value % 1024 * 10 / 1024} KiB"
  else s!"{value} B"

def percent (value : Nat) : String :=
  let fraction := toString (value % 1000 / 10)
  s!"{value / 1000}.{if fraction.length == 1 then "0" ++ fraction else fraction}%"

def spark (values : Array (Option Nat)) (width : Nat := 24) : String := Id.run do
  let values := values.extract (values.size - width) values.size
  let peak := max 1 (values.foldl (fun n v => max n (v.getD 0)) 0)
  let marks := "▁▂▃▄▅▆▇█".toList.toArray
  let mut result := String.ofList (List.replicate (width - values.size) ' ')
  for value in values do
    result := result.push (match value with | none => '·' | some n => marks[min 7 (n * 7 / peak)]!)
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

def metricLines (points : Array Sample) : Array String := Id.run do
  let some current := points.back? | return #["No sample: node stopped or unavailable"]
  let direct (select : Sample → Nat) := points.map (fun p => some (select p))
  let rates (select : Sample → Nat) := (Array.range points.size).map fun i =>
    if i == 0 then none else rate points[i - 1]! points[i]! select
  let rateLine (label : String) (select : Sample → Nat) :=
    let values := rates select
    let value := match (values.back? >>= id) with | some n => humanBytes n ++ "/s" | none => "—"
    s!"{pad 8 label}{spark values} {value}"
  return #[s!"{pad 8 "CPU"}{spark (direct (·.cpu))} {percent current.cpu}",
    s!"{pad 8 "Memory"}{spark (direct (·.memory))} {humanBytes current.memory} / {humanBytes current.limit}",
    rateLine "Net RX" (·.rx), rateLine "Net TX" (·.tx),
    rateLine "Disk R" (·.readBytes), rateLine "Disk W" (·.writeBytes)]

end LeanCloudCli
