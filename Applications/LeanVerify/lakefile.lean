import Lake
open Lake DSL

package lean_verify

@[package_dep] def lean_cloud_runtime : Dependency := {
  name := `lean_cloud_runtime
  scope := ""
  version := .none
  opts := {}
  src? := some (.path (match get_config? leanCloudSdk with
    | some root => System.FilePath.mk root / "runtime"
    | none => "../../runtime"))
}

lean_lib LeanVerify

@[default_target]
lean_exe cloud_app where
  root := `Main
  moreLinkArgs := if System.Platform.isOSX then #[] else #["-Wl,--allow-shlib-undefined"]

@[test_driver]
lean_exe verify_tests where
  root := `Tests

lean_exe verify_local where
  root := `Local
