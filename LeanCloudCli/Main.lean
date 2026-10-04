import LeanCloudCli.Application
import LeanCloudCli.IO

def main (args : List String) : IO UInt32 := do
  return (← LeanCloudCli.Cli.runIO (LeanCloudCli.application args)).toOption.getD 1
