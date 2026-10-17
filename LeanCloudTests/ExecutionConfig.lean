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
    let custom : LeanCloud.ExecutionConfig := { interpreterFuel := 123 }
    assertEq (← unwrap (fromJson? (toJson custom))) custom
    let bounded := { custom with replayCacheBytes := 1024, replayCacheEntries := 8 }
    assertEq (← unwrap (fromJson? (toJson bounded))) bounded
    let disabled := { custom with replayCacheBytes := 0, replayCacheEntries := 0 }
    assertEq (← unwrap (fromJson? (toJson disabled))) disabled
    for bad in [Json.null, toJson "invalid", Json.mkObj [("interpreterFuel", toJson (0 : Nat))],
        Json.mkObj [("interpreterFuel", toJson "100")],
        Json.mkObj [("interpreterFuel", Json.null)],
        Json.mkObj [("replayCacheBytes", toJson (-1 : Int))],
        Json.mkObj [("replayCacheEntries", Json.null)]] do
      assertTrue (fromJson? (α := LeanCloud.ExecutionConfig) bad).toOption.isNone
        s!"Accepted invalid limits: {bad.compress}"
    -- Old deployment files remain readable; these fields no longer enable retries.
    let old : LeanCloud.ExecutionConfig ← unwrap (fromJson? (Json.mkObj [
      ("interpreterFuel", toJson (123 : Nat)), ("retryDelayMs", toJson (500 : Nat)),
      ("retryMaxDelayMs", toJson (5000 : Nat))]))
    assertEq old custom⟩]

end LeanCloudTests.ExecutionConfig
