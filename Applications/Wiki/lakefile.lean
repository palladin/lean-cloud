import Lake
open Lake DSL

package wiki

@[package_dep] def lean_cloud_runtime : Dependency := {
  name := `lean_cloud_runtime, scope := "", version := .none, opts := {}
  src? := some (.path (match get_config? leanCloudSdk with
    | some root => System.FilePath.mk root / "runtime"
    | none => "../../runtime")) }

lean_lib Wiki

-- Lean's bundled linker does not search the host SDK/system library paths.
open Lean Elab Term in
elab "wikiLinkArgs%" : term => do
  let args ← if System.Platform.isOSX then do
    let sdk ← IO.Process.output { cmd := "xcrun", args := #["--show-sdk-path"] }
    unless sdk.exitCode == 0 do throwError "Install Xcode Command Line Tools"
    pure #["--ld-path=/usr/bin/ld", "-L" ++ sdk.stdout.trimAscii.toString ++ "/usr/lib", "-lexpat", "-lbz2"]
  else do
    let mut args := #["-Wl,--allow-shlib-undefined"]
    for library in ["libexpat.so", "libbz2.so"] do
      let mut found := false
      for dir in ["/usr/lib/x86_64-linux-gnu", "/usr/lib/aarch64-linux-gnu", "/usr/lib64", "/usr/lib"] do
        let path := dir ++ "/" ++ library
        if !found && (← System.FilePath.pathExists path) then
          args := args.push path
          found := true
      unless found do throwError "Install libexpat1-dev and libbz2-dev ({library} missing)"
    pure args
  return Lean.toExpr args

extern_lib wiki_native pkg := do
  let src ← inputTextFile (pkg.dir / "native" / "wiki.c")
  let obj ← buildO (pkg.buildDir / "native" / "wiki.o") src
    #["-I", (← getLeanInstall).includeDir.toString]
    #["-O2", "-std=c11", "-Wall", "-Wextra", "-Werror"] "cc"
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "wiki_native") #[obj]

@[default_target]
lean_exe cloud_app where
  root := `Main
  moreLinkArgs := wikiLinkArgs%

@[test_driver]
lean_exe wiki_tests where
  root := `Tests
  moreLinkArgs := wikiLinkArgs%

lean_exe wiki_files where
  root := `Local
  moreLinkArgs := wikiLinkArgs%
