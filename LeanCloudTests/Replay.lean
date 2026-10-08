import LeanCloudTests.Support

namespace LeanCloudTests
open Lean LeanCloud

private abbrev Records := List (String × ReplayRecord)

private def memoryStore (saved : IO.Ref Records) : ReplayStore IO where
  read key := return (← saved.get).lookup key
  create key proposed := saved.modifyGet fun records =>
    match records.lookup key with
    | some existing => (existing, records)
    | none => (proposed, (key, proposed) :: records)

private def noBlobs : BlobStorage IO where
  putBlob _ := throw ⟨.unsupported, "Unexpected blob operation"⟩
  readBlob _ := throw ⟨.unsupported, "Unexpected blob operation"⟩
  resolveBlob _ := throw ⟨.unsupported, "Unexpected blob operation"⟩

private def root : Assignment := ⟨0, Location.root⟩

private def resume [Codec α] (store : ReplayStore IO) (source : Cloud IO α)
    (assignment : Assignment := root) : IO (Except CloudError Progress) :=
  (ReplayInterpreter.step store noBlobs 1000 (fun _ : Unit => source) () assignment).run

private def rejectReplay [Codec α] (name : String) (source : Cloud IO α)
    (assignment : Assignment) (initial : Records) (kind : ErrorKind) : TestCase :=
  ⟨s!"replay/reject/{name}", do
    let saved ← IO.mkRef initial
    assertError (← resume (memoryStore saved) source assignment) kind
    assertEq (← saved.get) initial "Rejected replay wrote records"⟩

private def captured : Cloud IO Nat := Cloud.pure (fun _ => 7) "capture"
private def capturedRequest : Request := ⟨"exec", "nat/v1", toJson "capture"⟩
private def group : Cloud IO (Array Nat) := Cloud.parallel #[pure 10, pure 20]
private def groupRequest : Request := ⟨"parallel", "array(nat/v1)/v1", toJson (2 : Nat)⟩

private def invalidReplayCases : Array TestCase :=
  let valueKey := ReplayStore.valueKey Location.root
  let later := { root with branchStart := Location.root.next.child 0 }
  #[
    rejectReplay "empty-location" captured { root with branchStart := #[] } [] .protocol,
    rejectReplay "non-root-location" captured { root with branchStart := #[(1, 0)] } [] .protocol,
    rejectReplay "ended-before-assignment" (pure 7 : Cloud IO Nat) later [] .divergence,
    rejectReplay "failed-before-assignment" (Cloud.fail "failed" : Cloud IO Nat) later [] .divergence,
    rejectReplay "missing-prefix" captured later [] .divergence,
    rejectReplay "failed-prefix" captured later
      [(valueKey, ⟨capturedRequest, .failure ⟨.application, "failed"⟩⟩)] .divergence,
    rejectReplay "changed-operation" captured root
      [(valueKey, ⟨{ capturedRequest with kind := "readBlob" }, .success (toJson (7 : Nat))⟩)] .divergence,
    rejectReplay "changed-schema" captured root
      [(valueKey, ⟨{ capturedRequest with schema := "nat/v2" }, .success (toJson (7 : Nat))⟩)] .divergence,
    rejectReplay "changed-label" captured root
      [(valueKey, ⟨{ capturedRequest with payload := toJson "other" }, .success (toJson (7 : Nat))⟩)] .divergence,
    rejectReplay "invalid-command-value" captured root
      [(valueKey, ⟨capturedRequest, .success (toJson "not a nat")⟩)] .codec,
    rejectReplay "invalid-return-record" captured root
      [(ReplayStore.returnKey Location.root, ⟨capturedRequest, .success (toJson (7 : Nat))⟩)] .divergence,
    rejectReplay "child-outside-group" group
      ⟨0, Location.root.child 2⟩ [] .divergence,
    rejectReplay "missing-joined-prefix" group later [] .divergence,
    rejectReplay "changed-child-count" group root
      [(valueKey, ⟨{ groupRequest with payload := toJson (1 : Nat) }, .success (toJson (#[10] : Array Nat))⟩)] .divergence,
    rejectReplay "wrong-result-count" group root
      [(valueKey, ⟨groupRequest, .success (toJson (#[10] : Array Nat))⟩)] .divergence,
    rejectReplay "invalid-child-value" group root
      [(valueKey, ⟨groupRequest, .success (toJson #["ten", "twenty"])⟩)] .codec
  ]

/-- Exercise real worker steps in a chosen completion order, then compare with
both the direct interpreter and an explicit expected outcome. -/
private def reverseCompletion (fails : Bool) : TestCase :=
  ⟨s!"replay/reverse-completion/{if fails then "errors" else "values"}", do
    let source : Cloud IO (Array Nat) := Cloud.parallel <|
      if fails then #[Cloud.fail "first", Cloud.fail "second", pure 30]
      else #[pure 10, pure 20, pure 30]
    let expected : Except CloudError (Array Nat) :=
      if fails then .error ⟨.application, "first"⟩ else .ok #[10, 20, 30]
    assertOutcome (← (DirectInterpreter.interpret noBlobs (fun _ : Unit => source) ()).run) expected
    let saved ← IO.mkRef ([] : Records)
    let store := memoryStore saved
    assertOutcome (← resume store source) (.ok (.fork Location.root 3))
    for index in [2, 1, 0] do
      let child := Location.root.child index
      assertOutcome (← resume store source ⟨index + 1, child⟩) (.ok .done)
      assertTrue ((← saved.get).lookup (ReplayStore.returnKey child)).isSome "Child has no durable result"
      assertTrue ((← saved.get).lookup (ReplayStore.returnKey Location.root)).isNone "Child completed the parent"
    assertOutcome (← resume store source root) (.ok .done)
    let .ok (some outcome) ← store.outcome.run | throw (IO.userError "Missing root result")
    assertOutcome (ReplayInterpreter.result (m := Id) outcome).run expected⟩

def replayCases : Array TestCase := invalidReplayCases ++ #[
  ⟨"replay/assignment-wire-format-and-legacy-inbox", do
    let child := Location.root.next.child 1
    let assignment : Assignment := ⟨7, child⟩
    assertEq (toJson assignment) (Json.mkObj [("attempt", toJson (7 : Nat)), ("branchStart", toJson child)])
    let decoded : Assignment ← unwrap (fromJson? (toJson assignment))
    assertEq decoded assignment
    let legacy : Assignment ← unwrap (fromJson? (Json.mkObj [
      ("attempt", toJson (7 : Nat)), ("branch", toJson child),
      ("location", toJson child.next), ("joining", toJson true)]))
    assertEq legacy assignment "Legacy cursor changed the assigned branch"⟩,
  ⟨"replay/partial-group-suspends-until-all-children-return", do
    let saved ← IO.mkRef ([] : Records)
    let store := memoryStore saved
    assertOutcome (← resume store group) (.ok (.fork Location.root 2))
    assertEq (← saved.get) [] "Suspension created a group result"
    assertOutcome (← resume store group ⟨1, Location.root.child 1⟩) (.ok .done)
    let partialRecords ← saved.get
    assertOutcome (← resume store group) (.ok (.fork Location.root 2))
    assertEq (← saved.get) partialRecords "Partial join wrote a result"
    assertOutcome (← resume store group ⟨2, Location.root.child 0⟩) (.ok .done)
    -- Exactly the same assignment discovers the complete group and joins it.
    assertOutcome (← resume store group) (.ok .done)
    assertEq ((← saved.get).lookup (ReplayStore.valueKey Location.root))
      (some ⟨groupRequest, .success (toJson (#[10, 20] : Array Nat))⟩)
    assertOutcome (← store.outcome.run) (.ok (some (.success (toJson (#[10, 20] : Array Nat)))))⟩,
  ⟨"replay/empty-group-continues-without-suspension", do
    let saved ← IO.mkRef ([] : Records)
    let store := memoryStore saved
    let source : Cloud IO Nat := do
      let values ← Cloud.parallel (#[] : Array (Cloud IO Nat))
      return values.size + 42
    assertOutcome (← resume store source) (.ok .done)
    assertOutcome (← store.outcome.run) (.ok (some (.success (toJson (42 : Nat)))))
    assertEq (← saved.get).length 2 "Empty group created child records"⟩,
  ⟨"replay/reconstruction-fuel-and-observations", do
    let calls ← IO.mkRef (#[] : Array String)
    let counted (label : String) (value : Nat) : Cloud IO Nat := Cloud.exec (fun _ => do
      calls.modify (·.push label)
      return value) label
    let source : Cloud IO Nat := do
      let value ← counted "prefix" 7
      let values ← Cloud.parallel #[counted "child" (value + 1)]
      return values[0]!
    let saved ← IO.mkRef ([] : Records)
    let fork := Location.root.next
    assertOutcome (← resume (memoryStore saved) source) (.ok (.fork fork 1))
    let prefixRecords ← saved.get
    let child := fork.child 0
    let assignment : Assignment := ⟨1, child⟩
    -- Replay prefix command, descend at the fork, execute child command, return.
    let path := #[Location.root, fork, child, child.next]
    for fuel in [:6] do
      saved.set prefixRecords
      calls.set #[]
      let visits ← IO.mkRef (#[] : Array Location)
      let observer : ReplayInterpreter.Observer IO := fun location _ => visits.modify (·.push location)
      let outcome ← (ReplayInterpreter.step (memoryStore saved) noBlobs fuel
        (fun _ : Unit => source) () assignment (some observer)).run
      if fuel < 4 then assertError outcome .protocol
      else assertOutcome outcome (.ok .done)
      assertEq (← visits.get) (path.extract 0 fuel) "Phase transition changed source observations"
      assertEq (← calls.get) (if fuel < 3 then #[] else #["child"]) "Reconstruction executed user code"
      assertEq ((← saved.get).lookup (ReplayStore.returnKey child)).isSome (fuel ≥ 4)
        "Phase transition consumed extra fuel"
    -- An already completed assignment bypasses both phases, even without fuel.
    let visit : ReplayInterpreter.Observer IO := fun _ _ => throw (IO.userError "Observed a completed assignment")
    assertOutcome (← (ReplayInterpreter.step (memoryStore saved) noBlobs 0
      (fun _ : Unit => source) () assignment (some visit)).run) (.ok .done)⟩,
  ⟨"replay/cancelled-result-is-terminal", do
    let saved ← IO.mkRef ([] : Records)
    let store := memoryStore saved
    let cancelled := Exit.cancelled "Killed by user"
    assertOutcome (← (store.finish Location.root cancelled).run) (.ok ())
    let source : Cloud IO Nat := Cloud.exec (fun _ => throw (IO.userError "Cancelled run executed user code"))
    assertOutcome (← resume store source) (.ok .done)
    assertOutcome (← (store.finish Location.root (.success (toJson (42 : Nat)))).run) (.ok ())
    let .ok (some outcome) ← store.outcome.run | throw (IO.userError "Missing cancellation")
    assertEq outcome cancelled
    assertOutcome (ReplayInterpreter.result (m := Id) (α := Nat) outcome).run
      (.error ⟨.cancelled, "Killed by user"⟩)⟩,
  reverseCompletion false,
  reverseCompletion true,
  ⟨"replay/recorded-exec-is-not-reexecuted", do
    let calls ← IO.mkRef (#[] : Array String)
    let counted (label : String) (value : Nat) : Cloud IO Nat := Cloud.exec (fun _ => do
      calls.modify (·.push label)
      return value) label
    let source : Cloud IO (Array Nat) := do
      let value ← counted "prefix" 10
      let values ← Cloud.parallel #[counted "child-0" (value + 1), counted "child-1" (value + 2)]
      let _ ← counted "after" 0
      return values
    let saved ← IO.mkRef ([] : Records)
    let store := memoryStore saved
    let fork := Location.root.next
    for _ in [:2] do assertOutcome (← resume store source) (.ok (.fork fork 2))
    for index in [1, 0] do
      let child := fork.child index
      for attempt in [:2] do
        assertOutcome (← resume store source ⟨attempt, child⟩) (.ok .done)
    assertOutcome (← resume store source root) (.ok .done)
    assertEq (← calls.get) #["prefix", "child-1", "child-0", "after"]
    let before ← saved.get
    assertOutcome (← resume store source) (.ok .done)
    assertEq (← calls.get) #["prefix", "child-1", "child-0", "after"] "Warm replay executed user code"
    assertEq (← saved.get) before
    let .ok (some outcome) ← store.outcome.run | throw (IO.userError "Missing root result")
    assertEq outcome (.success (Codec.encode (#[11, 12] : Array Nat)))⟩,
  ⟨"replay/uses-canonical-create-result", do
    let saved ← IO.mkRef ([] : Records)
    let base := memoryStore saved
    -- Another attempt won publication with 42; this attempt computed 7.
    let store : ReplayStore IO := { base with
      create := fun key proposed =>
        base.create key (if key == ReplayStore.valueKey Location.root then
          { proposed with outcome := .success (toJson (42 : Nat)) } else proposed) }
    assertOutcome (← resume store captured) (.ok .done)
    let .ok (some outcome) ← store.outcome.run | throw (IO.userError "Missing root result")
    assertEq outcome (.success (toJson (42 : Nat)))⟩,
  ⟨"replay/io-failure-is-not-a-workflow-result", do
    let saved ← IO.mkRef ([] : Records)
    let store := memoryStore saved
    let calls ← IO.mkRef 0
    let source : Cloud IO Nat := Cloud.exec fun _ => do
      let previous ← calls.modifyGet fun n => (n, n + 1)
      if previous == 0 then throw (IO.userError "connection lost")
      return 7
    let failed ← try
      let _ ← resume store source
      pure false
    catch _ => pure true
    assertTrue failed "IO exception was swallowed as a workflow result"
    assertEq (← saved.get) [] "IO exception was persisted as a workflow result"
    assertOutcome (← resume store source) (.ok .done)
    assertEq (← calls.get) 2
    let .ok (some outcome) ← store.outcome.run | throw (IO.userError "Missing retried result")
    assertEq outcome (.success (toJson (7 : Nat)))⟩
]

end LeanCloudTests
