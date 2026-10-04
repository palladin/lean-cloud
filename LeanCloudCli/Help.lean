import LeanCloudCli.Model

namespace LeanCloudCli.Help

structure Command where
  name : String
  arguments : String := ""
  summary : String
  details : String := ""
  options : Array (String × String) := #[]
  examples : Array String
  aliases : Array String := #[]

def Command.usage (command : Command) : String :=
  command.name ++ (if command.arguments.isEmpty then "" else " " ++ command.arguments)

/-- Shared by overview help, detailed help, and command-name completion. -/
def commands : Array Command := #[
  { name := "init", arguments := "DIRECTORY [--sdk PATH]"
    summary := "Create and select a cloud application."
    details := "Creates a Lean project in a new or empty directory. Edit Main.lean, then deploy."
    options := #[("--sdk PATH", "Use a local lean-cloud checkout as the SDK.")]
    examples := #["init my-app", "init my-app --sdk /path/to/lean-cloud"] },
  { name := "open", arguments := "DIRECTORY", summary := "Select an existing application directory."
    details := "Subsequent commands use that application's deployment."
    examples := #["open my-app", "open '/path/with spaces/my-app'"] },
  { name := "deploy", arguments := "[EXECUTABLE] [-v|--verbose]"
    summary := "Build the application and start its persistent node pool."
    details := "EXECUTABLE selects and remembers a Lake executable target. Omit it to reuse the saved target.\nBuild/startup output is saved under .lean-cloud/PROJECT/logs/; quiet failures show an error tail."
    options := #[("-v, --verbose", "Stream full build and startup output.")]
    examples := #["deploy", "deploy my_app --verbose"] },
  { name := "programs", summary := "List entry points compiled into the deployed image."
    examples := #["programs"] },
  { name := "down", summary := "Stop this deployment and preserve its data."
    details := "Stops actors and shared services. Use 'up' to recover active runs; paused runs stay paused."
    examples := #["down"] },
  { name := "deployments", summary := "List known deployments, including stopped ones."
    details := "Shows the selected deployment, directories, and observed service state."
    examples := #["deployments"] },
  { name := "use", arguments := "NAME", summary := "Select and remember a known deployment."
    details := "Use 'deployments' to find names. The selection persists across console sessions."
    examples := #["use my-app"] },
  { name := "status", summary := "Show the selected deployment's health."
    details := "Includes its image, program/run counts, services, and actors. Use 'ps' for workflow results."
    examples := #["status"] },
  { name := "up", arguments := "[-v|--verbose]", summary := "Start services without rebuilding the application."
    details := "Requires an existing deployment and its durable volumes. Starts the saved scheduler and worker pool; active runs recover automatically.\nStartup output is saved under .lean-cloud/PROJECT/logs/."
    options := #[("-v, --verbose", "Stream full service startup output.")]
    examples := #["up", "up -v"] },
  { name := "doctor", summary := "Diagnose local configuration and Docker."
    details := "Checks files, Docker/Compose, images, volumes, and container health without changing services."
    examples := #["doctor"] },
  { name := "run", arguments := "PROGRAM [--input FILE] [--id ID]", summary := "Launch a cloud program."
    details := "Submits to the deployed nodes without creating containers. Use 'programs' to list entry points. Without --input, uses the program's sample input if available."
    options := #[("--input FILE", "Read and validate input from a JSON file."),
      ("--id ID", "Choose a unique run ID; otherwise one is generated.")]
    examples := #["run squares/v1", "run squares/v1 --input numbers.json --id example-1"] },
  { name := "ps", summary := "List cloud runs and their current status."
    details := "Lists runs recorded for the selected application, including completed and stopped runs."
    examples := #["ps"] },
  { name := "inspect", arguments := "RUN", summary := "Inspect a run's jobs and worker assignments."
    details := "Shows its outcome or control status and, for an active run, scheduler locations and attempts."
    examples := #["inspect example-1"] },
  { name := "result", arguments := "RUN", summary := "Read a run's durable result."
    details := "Prints pending, a completed value, or the failure/cancellation reason. Blob results are read as text."
    examples := #["result example-1"] },
  { name := "watch", arguments := "RUN [--once]", summary := "Show live source positions and resource graphs for a run."
    details := "Keys: q returns; Tab cycles nodes; 1/2/3 select workers; j/k scroll source; a follows source.\nSource markers show the last observed operation."
    options := #[("--once", "Print one plain-text frame and return.")]
    examples := #["watch example-1", "watch example-1 --once"] },
  { name := "nodes", summary := "Show workers, schedulers, brokers, and blobs."
    details := "Prints container states and CPU/memory meters. Use 'top' for live actor graphs."
    examples := #["nodes"] },
  { name := "top", arguments := "[--once]", summary := "Show live worker and scheduler graphs across all runs."
    details := "Shows CPU, memory, filesystem, network, and I/O metrics for the selected deployment.\nKeys: q returns; PgUp/PgDn or left/right arrows change pages. Rates need two samples."
    options := #[("--once", "Print a plain-text snapshot of every page and return.")]
    examples := #["top", "top --once"] },
  { name := "logs", arguments := "RUN [worker1|worker2|worker3|scheduler]"
    summary := "Print recent events for a run."
    details := "Defaults to worker1. Filters the node's last 100 log lines by run ID without following new output."
    examples := #["logs example-1", "logs example-1 scheduler"] },
  { name := "resume", arguments := "RUN", summary := "Resume a paused run or repair an incomplete launch."
    details := "Reactivates the workflow on the existing pool using its input and replay records. Killed runs cannot resume."
    examples := #["resume example-1"] },
  { name := "pause", arguments := "RUN", summary := "Stop a run and preserve replay state for resume."
    details := "Revokes this run's assignments. Workers stop at record boundaries; an IO action already executing may finish. Shared nodes keep running."
    examples := #["pause example-1", "resume example-1"] },
  { name := "kill", arguments := "RUN", summary := "Permanently cancel a cloud run."
    details := "Revokes the run and records cancellation. Shared nodes keep running. Replay records remain, but the run cannot resume.\nAn already completed result is preserved."
    examples := #["kill example-1"] },
  { name := "help", arguments := "[COMMAND]", summary := "Show commands or help for one command."
    details := "COMMAND --help and COMMAND -h show the same detailed help."
    examples := #["help", "help deploy", "deploy --help"] },
  { name := "quit", summary := "Exit the console."
    details := "Cloud processes and deployment services keep running."
    examples := #["quit"], aliases := #["exit"] }
]

def find? (name : String) : Option Command :=
  commands.find? (fun command => command.name == name || command.aliases.contains name)

def isFlag (arg : String) : Bool := arg == "--help" || arg == "-h"

/-- Detect help before action parsing, context selection, or fullscreen handoff. -/
def requested : List String → Bool
  | "help" :: _ => true
  | [arg] => isFlag arg
  | _ :: rest => rest.any isFlag
  | [] => false

private def overview : Cli Unit := do
  printHeading "Commands:"
  for command in commands do
    printStyled (Styled.text ("  " ++ pad 44 command.usage ++ "  ") .cyan ++ Styled.text command.summary)
  printLine "Use 'help COMMAND' or 'COMMAND --help' for usage, options, and examples."

private def detail (name : String) : Cli Unit := do
  let some command := find? name | throw s!"Unknown command '{safe name}'. Use 'help' to list commands."
  printHeading s!"Usage: {command.usage}"
  printLine command.summary
  unless command.details.isEmpty do printLine command.details
  unless command.aliases.isEmpty do printLine ("Aliases: " ++ String.intercalate ", " command.aliases.toList)
  printHeading "Options:"
  for (option, description) in command.options.push ("-h, --help", "Show this help and return.") do
    printStyled (Styled.text ("  " ++ pad 20 option) .cyan ++ Styled.text description)
  printHeading "Examples:"
  for sample in command.examples do printStyled (Styled.text ("  " ++ sample) .cyan)

def display : List String → Cli Unit
  | ["help"] | ["--help"] | ["-h"] => overview
  | ["help", name] => detail (if isFlag name then "help" else name)
  | "help" :: _ => throw "Usage: help [COMMAND]"
  | name :: rest => if rest.any isFlag then detail name else throw "Usage: help [COMMAND]"
  | [] => overview

end LeanCloudCli.Help
