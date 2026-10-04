import LeanCloudCli.Docker
import LeanCloudCli.Help

namespace LeanCloudCli.Completion

structure Item where
  value : String
  description : String := ""
  deriving Inhabited, BEq, Repr

def commands : Array Item :=
  Help.commands.map (fun command => ⟨command.name, command.summary⟩)

structure Catalog where
  programs : Array Item := #[]
  runs : Array Item := #[]
  files : Array Item := #[]
  deployments : Array Item := #[]
  actors : Array Item := (#["scheduler"] ++ workerNames defaultWorkerCount).map (fun name => ⟨name, ""⟩)

/-- Completion reads the local catalog, never polling Docker while typing. -/
def load (ctx : Context) : Cli Catalog := do
  let programs ← try
    pure ((← ctx.deployment).programs.map fun p => Item.mk p.entry p.description)
    catch _ => pure #[]
  let runs ← try
    pure ((← ctx.allRuns).map fun r => Item.mk r.id r.program.entry)
    catch _ => pure #[]
  let deployments ← try
    pure ((← Deployments.load).entries.map fun e => Item.mk e.project e.root)
    catch _ => pure #[]
  let count ← try pure (← ctx.deployment).retainedCount catch _ => pure defaultWorkerCount
  let actors := (#["scheduler"] ++ workerNames count).map fun name => Item.mk name "Node logs"
  return { programs, runs, deployments, actors }

structure Token where
  value : String
  start : Nat
  stop : Nat
  deriving Inhabited, Repr

/-- Tolerant tokenization for partially typed quotes, with character offsets. -/
def tokens (line : String) : Array Token := Id.run do
  let mut result := #[]
  let mut value := ""
  let mut start : Option Nat := none
  let mut quote : Option Char := none
  let mut escaped := false
  for (c, index) in line.toList.zipIdx do
    if c.isWhitespace && quote.isNone && !escaped then
      if let some first := start then result := result.push ⟨value, first, index⟩
      start := none; value := ""
    else
      if start.isNone then start := some index
      if escaped then value := value.push c; escaped := false
      else if c == '\\' && quote != some '\'' then escaped := true
      else if let some q := quote then
        if c == q then quote := none else value := value.push c
      else if c == '\'' || c == '"' then quote := some c
      else value := value.push c
  if let some first := start then result := result.push ⟨value, first, line.length⟩
  return result

structure Context where
  before : Array String
  fragment : String
  start : Nat
  stop : Nat
  deriving Repr

def context (line : String) (cursor : Nat) : Context :=
  let all := tokens line
  let cursor := min cursor line.length
  let current := all.find? (fun t => t.start ≤ cursor && cursor ≤ t.stop)
  let start := current.map (·.start) |>.getD cursor
  let stop := current.map (·.stop) |>.getD cursor
  let prefixText := String.ofList (line.toList.take cursor)
  let fragment := if current.isSome then ((tokens prefixText).back?.map (·.value)).getD "" else ""
  ⟨(all.filter (·.stop < start)).map (·.value), fragment, start, stop⟩

def candidates (catalog : Catalog) (ctx : Context) : Array Item :=
  let available := match ctx.before.toList with
    | [] => commands
    | ["help"] => commands ++ (Help.commands.flatMap fun command =>
        command.aliases.map fun name => Item.mk name s!"Alias for {command.name}")
    | ["run"] => catalog.programs
    | ["use"] => catalog.deployments
    | ["inspect"] | ["result"] | ["watch"] | ["logs"] | ["resume"] | ["pause"] | ["kill"] => catalog.runs
    | ["logs", _] => catalog.actors
    | ["watch", _] => #[⟨"--once", "Print one frame"⟩]
    | ["top"] => #[⟨"--once", "Print a snapshot of all workers and schedulers"⟩]
    | "deploy" :: rest =>
      if rest.getLast? == some "--workers" then #[] else
      (if rest.contains "--workers" then #[] else #[⟨"--workers", "Initial worker count"⟩]) ++
      (if rest.contains "-v" || rest.contains "--verbose" then #[] else
        #[⟨"--verbose", "Stream full build/startup output (-v)"⟩, ⟨"-v", "Stream full build/startup output"⟩])
    | "up" :: rest =>
      if rest.contains "-v" || rest.contains "--verbose" then #[]
      else #[⟨"--verbose", "Stream full build/startup output (-v)"⟩, ⟨"-v", "Stream full build/startup output"⟩]
    | "run" :: _ :: rest =>
      if rest.getLast? == some "--input" then catalog.files
      else if rest.getLast? == some "--id" then #[]
      else (#[⟨"--input", "Read input from a JSON file"⟩, ⟨"--id", "Choose a run ID"⟩] : Array Item).filter
        (fun item => !rest.contains item.value)
    | _ => #[]
  let expectsValue := [some "--input", some "--id", some "--sdk", some "--workers"].contains ctx.before.back?
  let help := if ctx.fragment.startsWith "-" && !expectsValue &&
      (ctx.before[0]? >>= Help.find?).isSome && !ctx.before.any Help.isFlag then
    #[Item.mk "--help" "Show usage, options, and examples", Item.mk "-h" "Show command help"] else #[]
  (available ++ help).filter (fun item => item.value.startsWith ctx.fragment)

/-- File candidates follow the typed directory, including quoted paths. -/
def refreshFiles (ctx : LeanCloudCli.Context) (catalog : Catalog) (line : String) (cursor : Nat) : Cli Catalog := do
  let part := context line cursor
  unless part.before[0]? == some "run" && part.before.back? == some "--input" do return catalog
  let parent := String.intercalate "/" (part.fragment.splitOn "/").dropLast
  let directory := if (part.fragment.splitOn "/").length > 1 then parent ++ "/" else ""
  let path : System.FilePath := if directory == "/" then "/" else if parent.isEmpty then ctx.root else ctx.root / parent
  let files ← try
    let mut items := #[]
    for name in ← request (.readDir path) do
      let isDirectory ← request (.isDir (path / name))
      items := items.push (Item.mk (directory ++ name ++ (if isDirectory then "/" else ""))
        (if isDirectory then "Directory" else "Input file"))
    pure (items.qsort (fun a b => a.value < b.value))
    catch _ => pure #[]
  return { catalog with files }

private def quoted (value : String) : String :=
  String.ofList (value.toList.flatMap fun c =>
    if c.isWhitespace || c == '\\' || c == '\'' || c == '"' then ['\\', c] else [c])

/-- Replace the complete token and preserve arguments after the cursor. -/
def apply (line : String) (ctx : Context) (item : Item) : String × Nat :=
  let value := quoted item.value
  let before := String.ofList (line.toList.take ctx.start)
  let after := String.ofList (line.toList.drop ctx.stop)
  (before ++ value ++ after, before.length + value.length)

end LeanCloudCli.Completion
