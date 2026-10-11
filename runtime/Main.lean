import LeanCloudRuntime
import LeanCloudRuntime.Programs

open Lean LeanCloud LeanCloudRuntime

-- Sample input provisioning belongs to this example application.
private def prepare (config : Config) (entry : String) (_ : Json) : IO Unit := do
  if entry == logSummary.info.entry then
    for (name, text) in Demo.sampleFiles do
      let ref ← config.objects.putBytes text.toUTF8
      config.objects.name name ref

def main (args : List String) : IO UInt32 :=
  Application.main programs args prepare
