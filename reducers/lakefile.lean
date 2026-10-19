import Lake
open Lake DSL

package lean_cloud_reducers where
  version := v!"0.1.0"
  license := "MIT"

require lean_cloud_runtime from "../runtime"
require lean_reducers from git
  "https://github.com/palladin/lean-reducers.git" @ "8683e1d22fe80fc57de1586fc2fae4dc409e39c6"

@[default_target]
lean_lib LeanCloudReducers

@[test_driver]
lean_exe reducer_tests where
  root := `Tests
