import Lake
open Lake DSL

-- SQLite is linked statically by the pinned leansqlite dependency.
-- Only the SQLite shim is reachable; no external database services are used.

open Lean Elab Term in
elab "rabbitLinkArgs%" : term => do
  if System.Platform.isOSX then
    let keg ← IO.Process.output { cmd := "brew", args := #["--prefix", "rabbitmq-c"] }
    return Lean.toExpr #["-L" ++ keg.stdout.trimAscii.toString ++ "/lib", "-lrabbitmq"]
  let result ← IO.Process.output { cmd := "pkg-config", args := #["--variable=libdir", "librabbitmq"] }
  unless result.exitCode == 0 do throwError "Install librabbitmq-dev and pkg-config"
  return Lean.toExpr #[result.stdout.trimAscii.toString ++ "/librabbitmq.so", "-Wl,--allow-shlib-undefined"]

open Lean Elab Term in
elab "rabbitIncludeArgs%" : term => do
  if System.Platform.isOSX then
    let keg ← IO.Process.output { cmd := "brew", args := #["--prefix", "rabbitmq-c"] }
    return Lean.toExpr #["-I", keg.stdout.trimAscii.toString ++ "/include"]
  return Lean.toExpr (#[] : Array String)

private def rabbitIncludes : Array String := rabbitIncludeArgs%

package lean_cloud_runtime where
  version := v!"0.1.0"

require lean_cloud from ".."
require «lean-linq» from git
  "https://github.com/palladin/lean-linq.git" @ "46ad2efaf9682991eaf1e9b19213d026ad5c20f9"

@[default_target]
lean_lib LeanCloudRuntime

lean_exe cloud_demo where
  root := `Main
  moreLinkArgs := rabbitLinkArgs%

lean_exe cloud_integration_tests where
  root := `Integration
  moreLinkArgs := rabbitLinkArgs%

extern_lib cloud_rabbitmq pkg := do
  let src ← inputTextFile (pkg.dir / "native" / "rabbitmq.c")
  let obj ← buildO (pkg.buildDir / "native" / "rabbitmq.o") src
    (#["-I", (← getLeanInstall).includeDir.toString] ++ rabbitIncludes) #["-O2", "-Wall", "-Wextra"] "cc"
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "cloud_rabbitmq") #[obj]

extern_lib cloud_process_lock pkg := do
  let src ← inputTextFile (pkg.dir / "native" / "process_lock.c")
  let obj ← buildO (pkg.buildDir / "native" / "process_lock.o") src
    #["-I", (← getLeanInstall).includeDir.toString] #["-O2", "-Wall", "-Wextra"] "cc"
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "cloud_process_lock") #[obj]
