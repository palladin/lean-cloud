import Lake
open Lake DSL

package lean_cloud where
  version := v!"0.1.0"
  license := "MIT"

require lean_eff from git
  "https://github.com/palladin/lean-eff.git" @ "2ad33d532b3de9008a5b80f9b29732364209643c"

@[default_target]
lean_lib LeanCloud where
  globs := #[.one `LeanCloud, .one `LeanCloud.Proofs]

lean_lib LeanCloudTests

input_dir cliTemplates where
  path := "LeanCloudCli/Templates"
  text := true

input_dir deploymentDefaults where
  path := "deploy"
  text := true

input_file cliToolchain where
  path := "lean-toolchain"
  text := true

lean_lib LeanCloudCli where
  needs := #[.mk (.packageTarget .anonymous `cliTemplates),
    .mk (.packageTarget .anonymous `deploymentDefaults), .mk (.packageTarget .anonymous `cliToolchain)]

lean_exe lean_cloud where
  root := `LeanCloudCli.Main

extern_lib cloud_console_native pkg := do
  let includeArgs := #["-I", (← getLeanInstall).includeDir.toString]
  let terminal ← inputTextFile (pkg.dir / "native" / "terminal.c")
  let terminalObj ← buildO (pkg.buildDir / "native" / "terminal.o") terminal includeArgs #["-O2", "-Wall", "-Wextra"] "cc"
  let lock ← inputTextFile (pkg.dir / "runtime" / "native" / "process_lock.c")
  let lockObj ← buildO (pkg.buildDir / "native" / "process_lock.o") lock includeArgs #["-O2", "-Wall", "-Wextra"] "cc"
  let process ← inputTextFile (pkg.dir / "native" / "process.c")
  let processObj ← buildO (pkg.buildDir / "native" / "process.o") process includeArgs #["-O2", "-Wall", "-Wextra"] "cc"
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "cloud_console_native") #[terminalObj, lockObj, processObj]

@[test_driver]
lean_exe lean_cloud_tests where
  root := `LeanCloudTests.Main

lean_exe cloud_chaos where
  root := `LeanCloudTests.Chaos

lean_exe cloud_runtime_tests where
  root := `LeanCloudTests.Runtime

lean_exe cloud_console_tests where
  root := `LeanCloudTests.ConsoleRuntime

lean_exe cloud_process_tests where
  root := `LeanCloudTests.ProcessRuntime
