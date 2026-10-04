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

-- Pass the absolute library path: adding the system library directory with -L
-- can shadow the C runtime bundled with Lean's Linux compiler.
target rabbitmqLink _pkg : System.FilePath := do
  let output ← IO.Process.output (if System.Platform.isOSX then
    { cmd := "brew", args := #["--prefix", "rabbitmq-c"] }
    else { cmd := "pkg-config", args := #["--variable=libdir", "librabbitmq"] })
  unless output.exitCode == 0 do error "RabbitMQ client library is missing; use the CLI's Docker build"
  let directory := output.stdout.trimAscii.toString
  let path := if System.Platform.isOSX then directory ++ "/lib/librabbitmq.dylib" else directory ++ "/librabbitmq.so"
  return Job.pure (System.FilePath.mk path)

@[default_target]
lean_lib LeanCloudRuntime where
  moreLinkObjs := #[rabbitmqLink]

lean_lib ApplicationTests

lean_exe cloud_demo where
  root := `Main
  moreLinkArgs := if System.Platform.isOSX then #[] else #["-Wl,--allow-shlib-undefined"]

lean_exe cloud_integration_tests where
  root := `Integration
  moreLinkArgs := if System.Platform.isOSX then #[] else #["-Wl,--allow-shlib-undefined"]

extern_lib cloud_rabbitmq pkg := do
  let rabbitIncludes ← if System.Platform.isOSX then do
    let keg ← IO.Process.output { cmd := "brew", args := #["--prefix", "rabbitmq-c"] }
    unless keg.exitCode == 0 do error "RabbitMQ client headers are missing; use the CLI's Docker build"
    pure #["-I", keg.stdout.trimAscii.toString ++ "/include"]
    else pure #[]
  let src ← inputTextFile (pkg.dir / "native" / "rabbitmq.c")
  let obj ← buildO (pkg.buildDir / "native" / "rabbitmq.o") src
    (#["-I", (← getLeanInstall).includeDir.toString] ++ rabbitIncludes) #["-O2", "-Wall", "-Wextra"] "cc"
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "cloud_rabbitmq") #[obj]

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
