import Lake
open Lake DSL

-- SQLite is linked statically by the pinned leansqlite dependency.
-- Only the SQLite shim is reachable; no external database services are used.

package lean_cloud_runtime where
  version := v!"0.1.0"
  license := "MIT"

require lean_cloud from ".."
require «lean-linq» from git
  "https://github.com/palladin/lean-linq.git" @ "46ad2efaf9682991eaf1e9b19213d026ad5c20f9"

@[default_target]
lean_lib LeanCloudRuntime

lean_lib ApplicationTests

lean_exe cloud_inbox_tests where
  root := `InboxTests
  moreLinkArgs := if System.Platform.isOSX then #[] else #["-Wl,--allow-shlib-undefined"]

lean_exe cloud_demo where
  root := `Main
  moreLinkArgs := if System.Platform.isOSX then #[] else #["-Wl,--allow-shlib-undefined"]

lean_exe cloud_integration_tests where
  root := `Integration
  moreLinkArgs := if System.Platform.isOSX then #[] else #["-Wl,--allow-shlib-undefined"]

extern_lib cloud_process_lock pkg := do
  let src ← inputTextFile (pkg.dir / "native" / "process_lock.c")
  let obj ← buildO (pkg.buildDir / "native" / "process_lock.o") src
    #["-I", (← getLeanInstall).includeDir.toString] #["-O2", "-Wall", "-Wextra"] "cc"
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "cloud_process_lock") #[obj]

extern_lib cloud_telemetry pkg := do
  let src ← inputTextFile (pkg.dir / "native" / "telemetry.c")
  let obj ← buildO (pkg.buildDir / "native" / "telemetry.o") src
    #["-I", (← getLeanInstall).includeDir.toString] #["-O2", "-Wall", "-Wextra"] "cc"
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "cloud_telemetry") #[obj]
