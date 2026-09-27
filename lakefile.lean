import Lake
open Lake DSL

package lean_cloud where
  version := v!"0.1.0"

require lean_eff from git
  "https://github.com/palladin/lean-eff.git" @ "2ad33d532b3de9008a5b80f9b29732364209643c"

@[default_target]
lean_lib LeanCloud

lean_lib LeanCloudTests

@[test_driver]
lean_exe lean_cloud_tests where
  root := `LeanCloudTests.Main
