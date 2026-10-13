import Lake
open Lake DSL

package lean_cloud where
  version := v!"0.1.0"
  license := "MIT"

require lean_eff from git
  "https://github.com/palladin/lean-eff.git" @ "7adc93de965c30d02b8a8035c2c7efd0dcc75337"

@[default_target]
lean_lib LeanCloud where
  globs := #[.one `LeanCloud, .one `LeanCloud.Proofs]

lean_lib LeanCloudTests

lean_lib LeanCloudCli

lean_exe lean_cloud where
  root := `LeanCloudCli.Main

extern_lib cloud_console_native pkg := do
  let includeArgs := #["-I", (← getLeanInstall).includeDir.toString]
  let terminal ← inputTextFile (pkg.dir / "native" / "terminal.c")
  let terminalObj ← buildO (pkg.buildDir / "native" / "terminal.o") terminal includeArgs #["-O2", "-Wall", "-Wextra"] "cc"
  let lock ← inputTextFile (pkg.dir / "runtime" / "native" / "process_lock.c")
  let lockObj ← buildO (pkg.buildDir / "native" / "process_lock.o") lock includeArgs #["-O2", "-Wall", "-Wextra"] "cc"
  let http ← inputTextFile (pkg.dir / "native" / "http.c")
  let httpObj ← buildO (pkg.buildDir / "native" / "http.o") http includeArgs #["-O2", "-Wall", "-Wextra"] "cc"
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "cloud_console_native") #[terminalObj, lockObj, httpObj]

@[test_driver]
lean_exe lean_cloud_tests where
  root := `LeanCloudTests.Main

lean_exe cloud_console_tests where
  root := `LeanCloudTests.ConsoleRuntime

lean_exe cloud_stress_tests where
  root := `LeanCloudTests.StressMain
