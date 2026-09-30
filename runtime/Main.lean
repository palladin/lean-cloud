import LeanCloudRuntime

open Lean LeanCloud LeanCloudRuntime

private def definition (input : Demo.Input) : RunDefinition :=
  ⟨"log-summary/v1", toJson input, (inferInstance : Codec BlobRef).schema⟩

private def decodeInput (run : RunDefinition) : IO Demo.Input := do
  unless run.entry == "log-summary/v1" && run.resultSchema == (inferInstance : Codec BlobRef).schema do
    throw (IO.userError "This worker image does not support the run's entry point/version/codec")
  match fromJson? run.input with
  | .ok input => return input
  | .error _ => throw (IO.userError "Invalid log-summary input")

private def showResult (config : Config) (run : String) : IO UInt32 := do
  let some outcome ← completed config run | IO.println "pending"; return 2
  match outcome with
  | .success value =>
    let ref ← match Codec.decode (α := BlobRef) value with
      | .ok ref => pure ref
      | .error message => throw (IO.userError message)
    let .ok bytes ← (S3.readBytes config.blobs ref).run
      | throw (IO.userError "Cannot read report blob")
    let some text := String.fromUTF8? bytes | throw (IO.userError "Report is not UTF-8")
    IO.print text
    return 0
  | .failure error => IO.eprintln error.message; return 1
  | .cancelled reason => IO.eprintln reason; return 1

def main (args : List String) : IO UInt32 := do
  try
    let command :: path :: run :: rest := args
      | IO.eprintln "Usage: cloud-demo (submit|worker|result) CONFIG RUN [INPUT.json]"; return 2
    let config : Config ← WorkerConfig.load path
    validateRun run
    match command with
    | "submit" =>
      S3.initializeBucket config.blobs
      let input ← match rest with
        | [] =>
          for (name, text) in Demo.sampleFiles do
            let ref ← S3.putBytes config.blobs text.toUTF8
            S3.name config.blobs name ref
          pure Demo.input
        | [file] =>
          match Json.parse (← IO.FS.readFile file) >>= fromJson? with
          | .ok input => pure input
          | .error _ => throw (IO.userError "Invalid input file")
        | _ => throw (IO.userError "Expected at most one input file")
      submit config run (definition input)
      IO.println s!"submitted {run}"
      return 0
    | "worker" =>
      let input ← decodeInput (← loadRun config run)
      let result ← Worker.run (connectors run) config 100000 Demo.workflow input
      match result with
      | .ok ref => IO.println s!"completed {run}: {ref.key}"; return 0
      | .error error =>
        IO.eprintln error.message
        return if (← completed config run).isSome then 0 else 1
    | "result" => showResult config run
    | _ => throw (IO.userError "Unknown command")
  catch error => IO.eprintln error.toString; return 1
