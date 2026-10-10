import LeanCloudTests.Support
import LeanCloud.ExecutionConfig
import LeanCloud.Version

namespace LeanCloudTests.ExecutionConfig
open Lean LeanCloud

def cases : Array TestCase := #[
  ⟨"runtime-config/protocol-result-envelope", do
    for result in [Except.ok (ε := String) (toJson (7 : Nat)), .error "unsupported"] do
      let payload := toJson result
      let legacy := Version.response (Json.mkObj []) payload
      assertEq legacy payload
      let current := Version.response (Version.stamp "protocolVersion" (Json.mkObj [])) payload
      for response in [legacy, current] do
        let decoded ← unwrap (Version.responsePayload response >>= fromJson? (α := Except String Json))
        assertEq (toJson decoded) (toJson result)
    assertTrue (Version.responsePayload (Json.mkObj [("protocolVersion", toJson (999 : Nat)),
      ("result", toJson (Except.ok (ε := String) Json.null))])).toOption.isNone
      "Future response was accepted"⟩,
  ⟨"runtime-config/version-compatibility", do
    for json in [Json.mkObj [], Json.mkObj [("formatVersion", toJson (0 : Nat))],
        Version.stamp "formatVersion" (Json.mkObj [])] do
      discard (unwrap (Version.check "formatVersion" "test" json))
    for value in [toJson (2 : Nat), toJson "1", Json.null, toJson (-1 : Int)] do
      assertTrue (Version.check "formatVersion" "test" (Json.mkObj [("formatVersion", value)])).toOption.isNone
        "Unsupported or malformed version was accepted"⟩,
  ⟨"runtime-config/defaults-and-roundtrip", do
    let config : LeanCloud.ExecutionConfig ← unwrap (fromJson? (Json.mkObj []))
    assertEq config ({} : LeanCloud.ExecutionConfig)
    let custom : LeanCloud.ExecutionConfig := ⟨123, 10, 100⟩
    assertEq (← unwrap (fromJson? (toJson custom))) custom
    for bad in [Json.null, toJson "invalid", Json.mkObj [("interpreterFuel", toJson (0 : Nat))],
        Json.mkObj [("retryDelayMs", toJson (0 : Nat))],
        Json.mkObj [("retryDelayMs", toJson (6000 : Nat))],
        Json.mkObj [("retryMaxDelayMs", toJson (60001 : Nat))],
        Json.mkObj [("interpreterFuel", toJson "100")],
        Json.mkObj [("retryMaxDelayMs", Json.null)]] do
      assertTrue (fromJson? (α := LeanCloud.ExecutionConfig) bad).toOption.isNone
        s!"Accepted invalid limits: {bad.compress}"⟩,
  ⟨"runtime-config/bounded-retry-backoff", do
    let config : LeanCloud.ExecutionConfig := ⟨1000, 500, 5000⟩
    assertEq ((List.range 6).map fun retry => (config.retryWaitMs retry).toNat)
      [500, 1000, 2000, 4000, 5000, 5000]
    assertEq (config.retryWaitMs 1000000).toNat 5000⟩]

end LeanCloudTests.ExecutionConfig
