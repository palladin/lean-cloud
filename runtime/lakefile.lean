import Lake
open Lake DSL

open Lean Elab Term in
elab "backendLinkArgs%" : term => do
  if System.Platform.isOSX then return Lean.toExpr (#["-lrabbitmq", "-lpq"] : Array String)
  let result ← IO.Process.output { cmd := "pkg-config", args := #["--variable=libdir", "librabbitmq"] }
  unless result.exitCode == 0 do throwError "Install librabbitmq-dev and pkg-config"
  let pg ← IO.Process.output { cmd := "pkg-config", args := #["--variable=libdir", "libpq"] }
  unless pg.exitCode == 0 do throwError "Install libpq-dev"
  return Lean.toExpr #[result.stdout.trimAscii.toString ++ "/librabbitmq.so",
    pg.stdout.trimAscii.toString ++ "/libpq.so", "-Wl,--allow-shlib-undefined"]

package lean_cloud_runtime where
  version := v!"0.1.0"

require lean_cloud from ".."
require «lean-linq» from git
  "https://github.com/palladin/lean-linq.git" @ "46ad2efaf9682991eaf1e9b19213d026ad5c20f9"

@[default_target]
lean_lib LeanCloudRuntime

lean_exe cloud_demo where
  root := `Main
  moreLinkArgs := backendLinkArgs%

lean_exe cloud_integration_tests where
  root := `Integration
  moreLinkArgs := backendLinkArgs%

extern_lib cloud_rabbitmq pkg := do
  let src ← inputTextFile (pkg.dir / "native" / "rabbitmq.c")
  let obj ← buildO (pkg.buildDir / "native" / "rabbitmq.o") src
    #["-I", (← getLeanInstall).includeDir.toString] #["-O2", "-Wall", "-Wextra"] "cc"
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "cloud_rabbitmq") #[obj]
