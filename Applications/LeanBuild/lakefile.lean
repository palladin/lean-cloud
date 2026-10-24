import Lake
open Lake DSL

package lean_build

@[package_dep] def lean_cloud_runtime : Dependency := {
  name := `lean_cloud_runtime
  scope := ""
  version := .none
  opts := {}
  src? := some (.path (match get_config? leanCloudSdk with
    | some root => System.FilePath.mk root / "runtime"
    | none => "../../runtime"))
}

lean_lib LeanBuild

@[default_target]
lean_exe cloud_app where
  root := `Main
  moreLinkArgs := if System.Platform.isOSX then #[] else #["-Wl,--allow-shlib-undefined"]

@[test_driver]
lean_exe build_tests where
  root := `Tests

lean_exe build_local where
  root := `Local

-- Optional, offline planner benchmark; never linked into the cloud application.
lean_exe plan_bench where
  root := `Benchmarks.Planner
