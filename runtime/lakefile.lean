import Lake
open Lake DSL

-- SQLite is linked statically by the pinned leansqlite dependency.
-- Only the SQLite shim is reachable; no external database services are used.

package lean_cloud_runtime where
  version := v!"0.1.0"
  license := "MIT"

require lean_cloud from ".."
require «lean-linq» from git
  "https://github.com/palladin/lean-linq.git" @ "463e34a331e0912170b3116b76b98b17ca3a67bd"

@[default_target]
lean_lib LeanCloudRuntime

lean_lib ApplicationTests
lean_lib TestServices
lean_lib PoolTests
lean_lib ReplyTests
lean_lib SchedulerTests
lean_lib MonitoringTests
lean_lib ObjectStoreTests
lean_lib StorageProviderTests
lean_lib ReplayCacheTests
lean_lib CleanupTests

lean_exe cloud_inbox_tests where
  root := `InboxTests
  moreLinkArgs := if System.Platform.isOSX then #[] else #["-Wl,--allow-shlib-undefined"]

lean_exe cloud_demo where
  root := `Main
  moreLinkArgs := if System.Platform.isOSX then #[] else #["-Wl,--allow-shlib-undefined"]

lean_exe cloud_integration_tests where
  root := `Integration
  moreLinkArgs := if System.Platform.isOSX then #[] else #["-Wl,--allow-shlib-undefined"]

lean_exe cloud_storage_tests where
  root := `StorageIntegration

extern_lib cloud_managed_process pkg := do
  let src ← inputTextFile (pkg.dir / "native" / "managed_process.c")
  let obj ← buildO (pkg.buildDir / "native" / "managed_process.o") src
    #["-I", (← getLeanInstall).includeDir.toString] #["-O2", "-Wall", "-Wextra", "-Werror"] "cc"
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "cloud_managed_process") #[obj]

extern_lib cloud_sha256 pkg := do
  let src ← inputTextFile (pkg.dir / "native" / "sha256.c")
  let obj ← buildO (pkg.buildDir / "native" / "sha256.o") src
    #["-I", (← getLeanInstall).includeDir.toString]
    #["-O2", "-Wall", "-Wextra", "-Werror", "-Wno-deprecated-declarations"] "cc"
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "cloud_sha256") #[obj]

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
