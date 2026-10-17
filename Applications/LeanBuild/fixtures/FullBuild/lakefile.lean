import Lake
open Lake DSL System

package full_build_fixture

-- Generated source and a custom output outside .lake/build.
def configured : String := (get_config? greeting).getD "41"

target generate pkg : FilePath := do
  let output := pkg.dir / "Generated.lean"
  IO.FS.writeFile output s!"def generated : UInt32 := {configured}\n"
  return Job.pure output

lean_lib Generated where
  extraDepTargets := #[`generate]

extern_lib native pkg := do
  let source ← inputTextFile (pkg.dir / "native.c")
  let object ← buildO (pkg.buildDir / "native.o") source #[] #["-fPIC"]
  buildStaticLib (pkg.buildDir / "lib" / nameToStaticLib "native") #[object]

@[default_target]
lean_exe fixture_app where
  root := `Main

target receipt pkg : FilePath := do
  let output := pkg.dir / "receipt.txt"
  IO.FS.writeFile output s!"built {configured}\n"
  return Job.pure output
