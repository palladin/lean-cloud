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
  { name := "connect", arguments := "NAME URL [--token-env ENV | --token-file FILE]"
    summary := "Connect to a scheduler's HTTP API."
    details := "Local and remote deployments use the same API. HTTPS is required except on loopback. The saved profile references a credential file or environment variable; it never copies the credential. Deployments are managed outside the console."
    options := #[("--token-env ENV", "Credential variable (default LEAN_CLOUD_TOKEN)."),
      ("--token-file FILE", "Read the credential from this file on each request.")]
    examples := #["connect local http://127.0.0.1:8080 --token-file .deployment/client.token", "connect production https://cloud.example.com"] },
  { name := "connections", summary := "List saved HTTP connections."
    examples := #["connections"] },
  { name := "programs", summary := "List entry points compiled into the deployed image."
    examples := #["programs"] },
  { name := "remove", arguments := "RUN", summary := "Remove a finished run and its replay records."
    details := "Only completed, failed, or killed runs can be removed after finalization. User blobs and other runs are preserved. The ID remains reserved so late messages cannot recreate the run. Cleanup visits every active worker; retry the same command if a node is unavailable. Scaled-down workers clear retired views when they return. Requires the scheduler and at least one worker."
    examples := #["remove example-1"] },
  { name := "use", arguments := "NAME", summary := "Select and remember a known deployment."
    details := "Use 'connections' to find names. The selection persists across console sessions."
    examples := #["use my-app"] },
  { name := "status", summary := "Show the selected deployment's health."
    details := "Includes its image, program/run counts, and node endpoints. Use 'ps' for workflow results."
    examples := #["status"] },
  { name := "doctor", summary := "Check authentication, catalogs, and node endpoints."
    details := "Read-only checks through the scheduler API. Does not submit a workflow or change the deployment."
    examples := #["doctor"] },
  { name := "run", arguments := "PROGRAM [--input FILE] [--id ID]", summary := "Launch a cloud program."
    details := "Submits to the deployed nodes without creating containers. Use 'programs' to list entry points. Without --input, uses the program's sample input if available."
    options := #[("--input FILE", "Read and validate input from a JSON file."),
      ("--id ID", "Choose a unique run ID; otherwise one is generated.")]
    examples := #["run squares/v1", "run squares/v1 --input numbers.json --id example-1"] },
  { name := "ps", summary := "List cloud runs, status, and elapsed time."
    details := "Shows start and finish timestamps in UTC and elapsed wall time, including waiting, pauses and retries. Completed durations stay fixed. Unavailable timestamps show —."
    examples := #["ps"] },
  { name := "inspect", arguments := "RUN", summary := "Inspect a run's jobs and worker assignments."
    details := "Shows its outcome or control status and, for an active run, scheduler locations and attempts."
    examples := #["inspect example-1"] },
  { name := "result", arguments := "RUN", summary := "Read a run's durable result."
    details := "Prints pending, a completed value, or the failure/cancellation reason. Blob results are read as text."
    examples := #["result example-1"] },
  { name := "watch", arguments := "RUN [--once]", summary := "Watch live branches, source, and workers; keep the final view."
    details := "Parallel groups start collapsed. Select a group to see all workers and their code; select a branch to see its executing worker. Up/down select visible rows and wrap at either end; left/right collapse or expand groups. Enter also expands. PgUp/PgDn page workers when space is limited. j/k scroll code; a follows its source line; q returns.\nCompleted runs show the last view with frozen statistics. Only the latest snapshot is saved; there is no execution history or timeline. Watching never resumes execution."
    options := #[("--once", "Print one plain-text frame and return.")]
    examples := #["watch example-1", "watch example-1 --once"] },
  { name := "top", arguments := "[--once]", summary := "Show live worker and scheduler graphs across all runs."
    details := "Shows CPU, memory, filesystem, network, and I/O metrics for the selected deployment.\nKeys: q returns; PgUp/PgDn or left/right arrows change pages. Rates need two samples."
    options := #[("--once", "Print a plain-text snapshot of every page and return.")]
    examples := #["top", "top --once"] },
  { name := "logs", arguments := "RUN [NODE]"
    summary := "Print recent events for a run."
    details := "Shows the latest retained workflow observations from the API, optionally filtered by node. This is a bounded view, not a complete log archive. Use your deployment tooling for raw container logs."
    examples := #["logs example-1", "logs example-1 scheduler"] },
  { name := "resume", arguments := "RUN", summary := "Resume a paused run or repair an incomplete launch."
    details := "Reactivates the workflow on the existing pool using its input and replay records. Killed runs cannot resume."
    examples := #["resume example-1"] },
  { name := "pause", arguments := "RUN", summary := "Stop a run and preserve replay state for resume."
    details := "Revokes this run's assignments. Workers stop at record boundaries; an IO action already executing may finish. Shared nodes keep running."
    examples := #["pause example-1", "resume example-1"] },
  { name := "kill", arguments := "RUN", summary := "Permanently cancel a cloud run."
    details := "Revokes the run; a worker records cancellation. With zero workers, that record waits for a worker. Shared nodes keep running. Replay records remain, but the run cannot resume.\nAn already completed result is preserved."
    examples := #["kill example-1"] },
  { name := "help", arguments := "[COMMAND]", summary := "Show commands or help for one command."
    details := "COMMAND --help and COMMAND -h show the same detailed help."
    examples := #["help", "help run", "run --help"] },
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
