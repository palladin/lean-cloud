import LeanCloud.Proofs.Specification
import LeanCloud.Proofs.Worker
import LeanCloud.Proofs.OptionalResults

namespace LeanCloud.Proofs.Recording
open Lean LeanEff ReplayModel ReplayInterpreter

variable {info : Option SourceSiteId}

/-- Every child return is available and their ordered combination agrees with
the specified group. This is a proof fact, never an interpreter input. -/
def JoinReady (expected journal : Journal) (location : Location) : Prop :=
  ∀ (schema : String) (count : Nat) (outcome : Exit),
    expected.lookup (ReplayStore.valueKey location) =
      some ⟨⟨"parallel", s!"array({schema})/v1", toJson count⟩, outcome⟩ →
    ∃ children : Nat → Exit,
      (∀ index, index < count → journal.lookup (ReplayStore.returnKey (location.child index)) =
        some ⟨ReplayStore.returnRequest, children index⟩) ∧
      collect ((Array.range count).map children) = outcome

theorem JoinReady.extend {expected before after location}
    (ready : JoinReady expected before location) (extension : Extends before after) :
    JoinReady expected after location := by
  intro schema count outcome known
  obtain ⟨children, present, collected⟩ := ready schema count outcome known
  exact ⟨children, fun index inside => extension _ _ (present index inside), collected⟩

/-- Completed child records establish the join obligation. Source order, not
completion order, determines both the resulting array and the selected error. -/
theorem JoinReady.of_children (expected journal : Journal) (location : Location)
    (codec : Codec α) (count : Nat) (outcomes : Fin count → Except CloudError α)
    (known : expected.lookup (ReplayStore.valueKey location) =
      some ⟨⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩,
        Parallel.recorded (fun values => Json.arr (values.map codec.encode)) ((Array.ofFn outcomes).mapM id)⟩)
    (completed : ∀ index : Fin count, journal.lookup (ReplayStore.returnKey (location.child index)) =
      some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode (outcomes index)⟩) :
    JoinReady expected journal location := by
  intro schema size outcome stored
  have same := Option.some.inj (known.symm.trans stored)
  have counts := congrArg (fun record : ReplayRecord => record.request.payload.getNat?) same
  change (Except.ok count : Except String Nat) = .ok size at counts
  have sizes := Except.ok.inj counts
  subst size
  let children (index : Nat) : Exit :=
    if inside : index < count then Parallel.recorded codec.encode (outcomes ⟨index, inside⟩)
    else .success Json.null
  refine ⟨children, ?_, ?_⟩
  · intro index inside
    simpa [children, inside] using completed ⟨index, inside⟩
  · have ordered : (Array.range count).map children = (Array.ofFn outcomes).map (Parallel.recorded codec.encode) := by
      ext index inside
      · simp
      · have bound : index < count := by simpa using inside
        simp [children, bound]
    rw [ordered, Parallel.collect_matches_direct]
    exact congrArg ReplayRecord.outcome same

/-- For a specified group, knowing that every child returned is enough. Storage
agreement supplies the values; callers need not supply encoders or outcomes. -/
theorem JoinReady.of_group {expected journal : Journal} {location : Location} {count : Nat}
    (group : Specification.Group expected location count) (consistent : Extends journal expected)
    (completed : ∀ index : Fin count, ∃ outcome,
      journal.lookup (ReplayStore.returnKey (location.child index)) = some ⟨ReplayStore.returnRequest, outcome⟩) :
    JoinReady expected journal location := by
  obtain ⟨α, codec, outcomes, known, children⟩ := group
  apply JoinReady.of_children expected journal location codec count outcomes known
  intro index
  obtain ⟨outcome, present⟩ := completed index
  exact present.trans ((consistent _ _ present).symm.trans (children index))

/-- The complete specification already contains every child return. This is a
fact about the mathematical journal, not an assumption that storage is full. -/
theorem JoinReady.of_specification {expected : Journal} {location : Location} {count : Nat}
    (group : Specification.Group expected location count) : JoinReady expected expected location := by
  apply JoinReady.of_group group (.refl _)
  obtain ⟨α, codec, outcomes, _, children⟩ := group
  exact fun index => ⟨_, children index⟩

/-- An incomplete group suspends without writing or executing any child. -/
theorem tryJoin_incomplete (expected journal : Journal) (location : Location) (count : Nat)
    (group : Specification.Group expected location count) (consistent : Extends journal expected)
    (incomplete : ¬ JoinReady expected journal location) :
    (Internal.tryJoin store location count).run journal = (.ok none, journal) := by
  obtain ⟨α, codec, outcomes, known, children⟩ := group
  let found (index : Nat) := (journal.lookup (ReplayStore.returnKey (location.child index))).map (·.outcome)
  have reads : ∀ index ∈ List.range count,
      (store.outcome (location.child index)).run journal = (.ok (found index), journal) := by
    intro index member
    have inside := List.mem_range.mp member
    exact Worker.read_compatible journal expected _ _ consistent (children ⟨index, inside⟩)
  simp only [Internal.tryJoin, bind_run]
  rw [Worker.read_children_snapshot journal location (List.range count) found reads]
  cases completed : (List.range count).mapM found with
  | none => simp
  | some values =>
    exfalso
    apply incomplete
    apply JoinReady.of_group ⟨α, codec, outcomes, known, children⟩ consistent
    intro index
    have entry := OptionalResults.mapM_present completed index.val (List.mem_range.mpr index.isLt)
    dsimp [found] at entry
    cases record : journal.lookup (ReplayStore.returnKey (location.child index)) with
    | none => simp [record] at entry
    | some record =>
      have same := Option.some.inj ((consistent _ _ record).symm.trans (children index))
      exact ⟨_, congrArg some same⟩

private theorem catch_pure (value : α) (handle : CloudError → ExceptT CloudError M α) :
    (tryCatch (pure value) handle : ExceptT CloudError M α) = pure value := rfl

theorem finish_within (journal expected : Journal) (branch : Location) (outcome : Exit)
    (consistent : Extends journal expected)
    (known : expected.lookup (ReplayStore.returnKey branch) = some ⟨ReplayStore.returnRequest, outcome⟩) :
    ∃ after, Extends journal after ∧ Extends after expected ∧
      after.lookup (ReplayStore.returnKey branch) = some ⟨ReplayStore.returnRequest, outcome⟩ ∧
      ((Internal.finish store branch outcome).run journal) = (.ok .done, after) := by
  have accepted := create_within journal expected _ _ consistent known
  refine ⟨_, create_extends journal _ _, accepted.2, ?_, ?_⟩
  · exact (create_visible journal _ _).trans (congrArg some accepted.1)
  · simp only [Internal.finish, ReplayStore.finish, bind_assoc]
    erw [lift_bind_run]
    rw [accepted.1]
    simp

variable {β : Type} (encode : β → Json)

/-- Executing a previously unrecorded pure operation writes its value before
calling the same continuation used by direct evaluation. -/
theorem exec_missing (journal : Journal) (blobs : BlobStorage M) (branch : Location)
    (current : Location) (fuel : Nat) (codec : Codec α) (label : String) (body : Unit → α)
    (next : ArrsF (Control M) SourceSiteId α β)
    (missing : journal.lookup (ReplayStore.valueKey current) = none)
    (roundtrip : codec.decode (codec.encode (body ())) = .ok (body ())) :
    let operation : Operation M α := .exec label (fun _ => pure (body ()))
    let record : ReplayRecord := ⟨Internal.request codec operation, .success (codec.encode (body ()))⟩
    (replay store blobs branch (fuel + 1) encode (.impure info (.command codec operation) next) current).run journal =
      (replay store blobs branch fuel encode (next.apply (body ())) current.next).run
        ((ReplayStore.valueKey current, record) :: journal) := by
  dsimp only
  rw [replay]
  simp only [Internal.command, bind_assoc]
  erw [read_then]
  simp [missing, Internal.execute, BlobStorage.execute, catch_pure]
  erw [lift_bind_run]
  simp [store, StateT.run, missing, Internal.check, Internal.resume, Internal.decode, roundtrip]

/-- Reusing a correct record calls exactly the same continuation without adding
another write, including when another attempt created the record first. -/
theorem exec_present (journal : Journal) (blobs : BlobStorage M) (branch : Location)
    (current : Location) (fuel : Nat) (codec : Codec α) (label : String) (body : Unit → α)
    (next : ArrsF (Control M) SourceSiteId α β)
    (present : journal.lookup (ReplayStore.valueKey current) =
      some ⟨Internal.request codec (.exec label (fun _ => pure (body ()) : Unit → M α)),
        .success (codec.encode (body ()))⟩)
    (roundtrip : codec.decode (codec.encode (body ())) = .ok (body ())) :
    (replay store blobs branch (fuel + 1) encode
      (.impure info (.command codec (.exec label (fun _ => pure (body ())))) next) current).run journal =
      (replay store blobs branch fuel encode (next.apply (body ())) current.next).run journal := by
  rw [replay]
  simp only [Internal.command, bind_assoc]
  erw [read_then]
  simp [present, Internal.check, Internal.resume, Internal.decode, roundtrip]

/-- A pure computation either creates its specified record or reuses it. In
both cases its continuation sees the computed value and the journal stays valid. -/
theorem exec_within (journal expected : Journal) (blobs : BlobStorage M) (branch : Location)
    (current : Location) (codec : Codec α) (label : String) (body : Unit → α)
    (next : ArrsF (Control M) SourceSiteId α β)
    (roundtrip : codec.decode (codec.encode (body ())) = .ok (body ()))
    (consistent : Extends journal expected)
    (known : expected.lookup (ReplayStore.valueKey current) =
      some ⟨Internal.request codec (.exec label (fun _ => pure (body ()) : Unit → M α)),
        .success (codec.encode (body ()))⟩) :
    let operation : Operation M α := .exec label (fun _ => pure (body ()))
    let record : ReplayRecord := ⟨Internal.request codec operation, .success (codec.encode (body ()))⟩
    ∃ after, Extends journal after ∧ Extends after expected ∧
      after.lookup (ReplayStore.valueKey current) = some record ∧
      ∀ fuel, (replay store blobs branch (fuel + 1) encode (.impure info (.command codec operation) next) current).run journal =
        (replay store blobs branch fuel encode (next.apply (body ())) current.next).run after := by
  dsimp only
  have accepted := create_within journal expected _ _ consistent known
  refine ⟨_, create_extends journal _ _, accepted.2, ?_, ?_⟩
  · have visible := create_visible journal (ReplayStore.valueKey current)
      ⟨Internal.request codec (.exec label (fun _ => pure (body ()) : Unit → M α)),
        .success (codec.encode (body ()))⟩
    exact visible.trans (congrArg some accepted.1)
  · intro fuel
    cases found : journal.lookup (ReplayStore.valueKey current) with
    | none =>
      simpa [store, StateT.run, found] using
        exec_missing (encode := encode) journal blobs branch current fuel codec label body next found roundtrip
    | some record =>
      have same := Option.some.inj ((consistent _ _ found).symm.trans known)
      subst record
      simpa [store, StateT.run, found] using
        exec_present (encode := encode) journal blobs branch current fuel codec label body next found roundtrip

/-- Joining completed children creates their ordered result once, then behaves
exactly like replay from the newly cached join. This includes failed groups. -/
theorem join_missing_is_cached (journal : Journal) (blobs : BlobStorage M) (branch : Location)
    (current : Location) (fuel : Nat) (codec : Codec α) (count : Nat) (branches : Fin count → Cloud M α)
    (next : ArrsF (Control M) SourceSiteId (Array α) β) (outcomes : Nat → Exit)
    (missing : journal.lookup (ReplayStore.valueKey current) = none)
    (completed : ∀ index, index < count →
      journal.lookup (ReplayStore.returnKey (current.child index)) =
        some ⟨ReplayStore.returnRequest, outcomes index⟩) :
    let record : ReplayRecord :=
      ⟨⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩,
        collect ((Array.range count).map outcomes)⟩
    let after := (ReplayStore.valueKey current, record) :: journal
    let program := EffF.impure info (.parallel codec count branches) next
    (replay store blobs branch (fuel + 1) encode program current).run journal =
      (replay store blobs branch (fuel + 1) encode program current).run after := by
  dsimp only
  rw [replay]
  erw [read_then]
  simp [missing]
  rw [bind_run, Worker.join_reads_children journal current count outcomes completed]
  erw [lift_bind_run]
  simp [store, StateT.run, Internal.check]
  erw [lift_bind_run]
  simp [StateT.run, missing]

theorem group_success (journal : Journal) (blobs : BlobStorage M) (branch : Location)
    (current : Location) (fuel : Nat) (codec : Codec α) (count : Nat) (branches : Fin count → Cloud M α)
    (next : ArrsF (Control M) SourceSiteId (Array α) β) (values : Array α)
    (roundtrip : Pure.RoundTrips codec) (size : values.size = count)
    (present : journal.lookup (ReplayStore.valueKey current) =
      some ⟨⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩,
        .success (Json.arr (values.map codec.encode))⟩) :
    (replay store blobs branch (fuel + 1) encode (.impure info (.parallel codec count branches) next) current).run journal =
      (replay store blobs branch fuel encode (next.apply values) current.next).run journal := by
  rw [replay]
  erw [read_then]
  have decoded := roundtrip.array codec
  change ∀ values, (@instCodecArray _ codec).decode (Json.arr (values.map codec.encode)) = .ok values at decoded
  simp [present, Internal.check, Internal.resume, Internal.decodeGroup, Internal.decode, decoded, size]

theorem group_failure (journal : Journal) (blobs : BlobStorage M) (branch : Location)
    (current : Location) (fuel : Nat) (codec : Codec α) (count : Nat) (branches : Fin count → Cloud M α)
    (next : ArrsF (Control M) SourceSiteId (Array α) β) (error : CloudError)
    (present : journal.lookup (ReplayStore.valueKey current) =
      some ⟨⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩, .failure error⟩) :
    (replay store blobs branch (fuel + 1) encode (.impure info (.parallel codec count branches) next) current).run journal =
      (Internal.finish store branch (.failure error)).run journal := by
  rw [replay]
  erw [read_then]
  simp [present, Internal.check, Internal.resume]

end LeanCloud.Proofs.Recording
