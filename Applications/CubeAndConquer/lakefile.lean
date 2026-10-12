import Lake
open Lake DSL

package cube_and_conquer

@[package_dep] def lean_cloud_runtime : Dependency := {
  name := `lean_cloud_runtime
  scope := ""
  version := .none
  opts := {}
  src? := some (.path (match get_config? leanCloudSdk with
    | some root => System.FilePath.mk root / "runtime"
    | none => "../../runtime"))
}

lean_lib CubeAndConquer

@[default_target]
lean_exe cloud_app where
  root := `Main
  moreLinkArgs := if System.Platform.isOSX then #[] else #["-Wl,--allow-shlib-undefined"]

lean_exe sat_files where
  root := `Local

@[test_driver]
lean_exe sat_tests where
  root := `Tests
