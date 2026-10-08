import LeanCloud.Proofs.SequentialCursor
import LeanCloud.Proofs.SequentialExecution
import LeanCloud.Proofs.Recording

namespace LeanCloud.Proofs.SequentialReplay
open Lean LeanEff ReplayModel ReplayInterpreter Reconstruction SequentialCursor SequentialExecution

variable {info : Option SourceSiteId}

variable [rootCodec : Codec α] (blobs : BlobStorage M) (source : Cloud M α)

abbrev sourceSteps : Step := steps blobs (fun _ : Unit => source) ()

def Verified (expected : Journal) (branch : Location) (outcome : Exit) (action : Action) (before : Journal) : Prop :=
  ∃ after, Extends before after ∧ Extends after expected ∧
    after.lookup (ReplayStore.returnKey branch) = some ⟨ReplayStore.returnRequest, outcome⟩ ∧
    Execution (sourceSteps blobs source) branch action before after

theorem Verified.replace {expected branch outcome action replacement before}
    (verified : Verified blobs source expected branch outcome action before)
    (same : ∃ offset, ∀ fuel, (replacement (offset + fuel)).run before = (action fuel).run before) :
    Verified blobs source expected branch outcome replacement before := by
  obtain ⟨after, grows, consistent, returned, execution⟩ := verified
  obtain ⟨offset, same⟩ := same
  exact ⟨after, grows, consistent, returned, execution.replace ⟨offset, 0, fun fuel _ => same fuel⟩⟩

theorem Verified.extend_before {expected branch outcome action before middle}
    (verified : Verified blobs source expected branch outcome action middle)
    (grows : Extends before middle)
    (same : ∃ offset minimum, ∀ fuel, minimum ≤ fuel → (replacement (offset + fuel)).run before = (action fuel).run middle) :
    Verified blobs source expected branch outcome replacement before := by
  obtain ⟨after, extension, consistent, returned, execution⟩ := verified
  exact ⟨after, grows.trans extension, consistent, returned, execution.replace same⟩

theorem Verified.step {expected journal current} {encode : β → Json} {remaining : Cloud M β}
    (cursor : Cursor blobs source journal current encode remaining) (assignment : Assignment)
    (branch : assignment.branchStart = Location.branchStart current) (outcome : Exit)
    (consistent : Extends journal expected)
    (known : expected.lookup (ReplayStore.returnKey assignment.branchStart) = some ⟨ReplayStore.returnRequest, outcome⟩)
    (verified : Verified blobs source expected assignment.branchStart outcome
      (fun fuel => replay store blobs assignment.branchStart fuel encode remaining current) journal) :
    Verified blobs source expected assignment.branchStart outcome (sourceSteps blobs source assignment) journal := by
  let point : Checkpoint := ⟨assignment.attempt, assignment.branchStart, current, false⟩
  cases found : journal.lookup (ReplayStore.returnKey assignment.branchStart) with
  | none => exact verified.replace blobs source (cursor.step blobs source point branch rfl found)
  | some record =>
    have same := Option.some.inj ((consistent _ _ found).symm.trans known)
    subst record
    have route := cursor.follows
    have nonempty : 0 < current.size := Nat.lt_of_lt_of_le (by decide) route.depth
    have first : current[0]!.1 = 0 := by simpa [LeanCloud.Location.root] using (route.branch_at 0 (by decide)).symm
    have valid : (!point.branch.isEmpty && point.branch[0]!.1 == 0) = true := by
      simp [point, branch, Array.isEmpty, Nat.ne_of_gt nonempty, Location.branchStart_index _ 0 nonempty, first]
    exact ⟨journal, .refl _, consistent, found, .done ⟨0, fun fuel _ =>
      completed_step_reuses_record journal blobs point (fun _ : Unit => source) () fuel _ valid found (by simp)⟩⟩

private theorem run_list (expected initial : Journal) (items : List κ)
    (job : κ → Assignment) (outcome : κ → Exit) (consistent : Extends initial expected)
    (each : ∀ item ∈ items, ∀ journal, Extends initial journal → Extends journal expected →
      Verified blobs source expected (job item).branchStart (outcome item) (sourceSteps blobs source (job item)) journal) :
    ∃ after, Extends initial after ∧ Extends after expected ∧
      (∀ item ∈ items, after.lookup (ReplayStore.returnKey (job item).branchStart) =
        some ⟨ReplayStore.returnRequest, outcome item⟩) ∧
      Batch (sourceSteps blobs source) (items.map job) initial after := by
  induction items generalizing initial with
  | nil => exact ⟨initial, .refl _, consistent, by simp, .nil⟩
  | cons item rest ih =>
    obtain ⟨middle, grows, compatible, returned, first⟩ := each item (by simp) initial (.refl _) consistent
    obtain ⟨after, extension, compatibleAfter, returns, later⟩ := ih middle compatible (by
      intro other member journal more consistent
      exact each other (by simp [member]) journal (grows.trans more) consistent)
    refine ⟨after, grows.trans extension, compatibleAfter, ?_, .cons first later⟩
    intro other member
    rcases List.mem_cons.mp member with rfl | member
    · exact extension _ _ returned
    · exact returns other member

private theorem join_records (expected journal : Journal) (branch current : Location)
    (encode : β → Json) (codec : Codec γ) (count : Nat) (branches : Fin count → Cloud M γ)
    (next : ArrsF (Control M) SourceSiteId (Array γ) β) (outcome : Exit)
    (consistent : Extends journal expected)
    (known : expected.lookup (ReplayStore.valueKey current) =
      some ⟨⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩, outcome⟩)
    (ready : Recording.JoinReady expected journal current) :
    ∃ after, Extends journal after ∧ Extends after expected ∧
      after.lookup (ReplayStore.valueKey current) =
        some ⟨⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩, outcome⟩ ∧
      ∀ fuel, (replay store blobs branch (fuel + 1) encode (.impure info (.parallel codec count branches) next) current).run journal =
        (replay store blobs branch (fuel + 1) encode (.impure info (.parallel codec count branches) next) current).run after := by
  cases found : journal.lookup (ReplayStore.valueKey current) with
  | some record =>
    exact ⟨journal, .refl _, consistent, found.trans ((consistent _ _ found).symm.trans known), by intros; rfl⟩
  | none =>
    obtain ⟨children, completed, collected⟩ := ready codec.schema count outcome known
    have accepted := create_within journal expected _ _ consistent known
    refine ⟨_, create_extends journal _ _, accepted.2,
      (create_visible journal _ _).trans (congrArg some accepted.1), ?_⟩
    intro fuel
    simpa [collected, store, StateT.run, found] using
      Recording.join_missing_is_cached encode journal blobs branch current fuel codec count branches next children found completed

private theorem parallel_runs (expected journal : Journal) (branch current : Location)
    (sameBranch : branch = Location.branchStart current)
    (encode : β → Json) (codec : Codec γ) (count : Nat)
    (branches : Fin count → Cloud M γ) (next : ArrsF (Control M) SourceSiteId (Array γ) β)
    (outcomes : Fin count → Except CloudError γ) (outcome : Exit)
    (cursor : Cursor blobs source journal current encode (.impure info (.parallel codec count branches) next))
    (consistent : Extends journal expected)
    (known : expected.lookup (ReplayStore.returnKey branch) = some ⟨ReplayStore.returnRequest, outcome⟩)
    (group : expected.lookup (ReplayStore.valueKey current) =
      some ⟨⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩,
        Parallel.recorded (fun values => Json.arr (values.map codec.encode)) ((Array.ofFn outcomes).mapM id)⟩)
    (childKnown : ∀ index : Fin count, expected.lookup (ReplayStore.returnKey (current.child index)) =
      some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode (outcomes index)⟩)
    (children : ∀ index : Fin count, ∀ after, Extends journal after → Extends after expected →
      Verified blobs source expected (current.child index) (Parallel.recorded codec.encode (outcomes index))
        (sourceSteps blobs source ⟨0, current.child index⟩) after)
    (cached : ∀ after, Extends journal after → Extends after expected →
      after.lookup (ReplayStore.valueKey current) =
        some ⟨⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩,
          Parallel.recorded (fun values => Json.arr (values.map codec.encode)) ((Array.ofFn outcomes).mapM id)⟩ →
      Verified blobs source expected branch outcome
        (fun fuel => replay store blobs branch fuel encode (.impure info (.parallel codec count branches) next) current) after) :
    Verified blobs source expected branch outcome
      (fun fuel => replay store blobs branch fuel encode (.impure info (.parallel codec count branches) next) current) journal := by
  have joinRun : ∀ after, Extends journal after → Extends after expected →
      Recording.JoinReady expected after current →
      Verified blobs source expected branch outcome
        (fun fuel => replay store blobs branch fuel encode (.impure info (.parallel codec count branches) next) current) after := by
    intro after grows compatible ready
    obtain ⟨recorded, extension, consistentAfter, present, executes⟩ := join_records blobs expected after branch current encode codec count branches next _
      compatible group ready
    have complete := cached recorded (grows.trans extension) consistentAfter present
    apply complete.extend_before blobs source extension
    refine ⟨0, 1, fun fuel enough => ?_⟩
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show fuel ≠ 0 by omega)
    simpa only [Nat.zero_add] using executes n
  cases found : journal.lookup (ReplayStore.valueKey current) with
  | some record =>
    exact cached journal (.refl _) consistent (found.trans ((consistent _ _ found).symm.trans group))
  | none =>
    classical
    by_cases ready : Recording.JoinReady expected journal current
    · exact joinRun journal (.refl _) consistent ready
    · obtain ⟨joined, grows, compatible, returns, batch⟩ := run_list blobs source expected journal (List.finRange count)
        (fun index => ⟨0, current.child index⟩)
        (fun index => Parallel.recorded codec.encode (outcomes index)) consistent
        (fun index _ => children index)
      have childRecords := fun index => returns index (List.mem_finRange index)
      have joinReady := Recording.JoinReady.of_children expected joined current codec count outcomes group childRecords
      have active := joinRun joined grows compatible joinReady
      obtain ⟨after, extension, consistentAfter, returned, resumed⟩ := Verified.step blobs source
        (cursor.extend blobs source grows) ⟨0, branch⟩ sameBranch outcome compatible known active
      refine ⟨after, grows.trans extension, consistentAfter, returned, .fork (location := current) (count := count) (forked := journal) ?_ ?_ resumed⟩
      · refine ⟨1, fun fuel enough => ?_⟩
        obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show fuel ≠ 0 by omega)
        dsimp only
        rw [replay]
        erw [read_then]
        simp only [found]
        rw [bind_run, Recording.tryJoin_incomplete expected journal current count ⟨γ, codec, outcomes, group, childKnown⟩ consistent ready]
        rfl
      · have same : (List.finRange count).map (fun (index : Fin count) => Assignment.mk 0 (current.child index)) =
            (List.range count).map (fun index => Assignment.mk 0 (current.child index)) := by
          apply List.ext_getElem <;> simp [List.finRange]
        simpa only [same] using batch

private theorem finish_verified (expected journal : Journal) (branch : Location) (outcome : Exit)
    (consistent : Extends journal expected)
    (known : expected.lookup (ReplayStore.returnKey branch) = some ⟨ReplayStore.returnRequest, outcome⟩) :
    Verified blobs source expected branch outcome (fun _ => Internal.finish store branch outcome) journal := by
  obtain ⟨after, grows, compatible, returned, finishes⟩ := Recording.finish_within journal expected branch outcome consistent known
  exact ⟨after, grows, compatible, returned, .done ⟨0, fun _ _ => finishes⟩⟩

/-- Every pure source subtree has a finite execution through actual replay
steps. The journal may start empty; only records already written are replayed. -/
theorem complete_runs {expected current} {program : Cloud M β} {outcome}
    (meaning : Specification.Complete expected current program outcome) :
    ∀ (encode : β → Json) journal branch, Extends journal expected →
      branch = Location.branchStart current →
      Cursor blobs source journal current encode program →
      expected.lookup (ReplayStore.returnKey branch) =
        some ⟨ReplayStore.returnRequest, Parallel.recorded encode outcome⟩ →
      Verified blobs source expected branch (Parallel.recorded encode outcome)
        (fun fuel => replay store blobs branch fuel encode program current) journal := by
  induction meaning with
  | pure value =>
    intro encode journal branch consistent same cursor known
    apply (finish_verified blobs source expected journal branch _ consistent known).replace blobs source
    exact ⟨1, fun fuel => by simp [Nat.add_comm 1 fuel, replay, Parallel.recorded]⟩
  | fail error next =>
    intro encode journal branch consistent same cursor known
    apply (finish_verified blobs source expected journal branch _ consistent known).replace blobs source
    exact ⟨1, fun fuel => by simp [Nat.add_comm 1 fuel, replay, Parallel.recorded]⟩
  | delay next rest ih =>
    intro encode journal branch consistent same cursor known
    apply (ih encode journal branch consistent same (cursor.delay blobs source next) known).replace blobs source
    exact ⟨1, fun fuel => by simp [Nat.add_comm 1 fuel, replay]⟩
  | exec codec label body next roundtrip present rest ih =>
    intro encode journal branch consistent same cursor known
    obtain ⟨after, grows, compatible, recorded, executes⟩ := Recording.exec_within encode journal expected blobs branch _ codec label body next roundtrip consistent present
    have continues := ih encode after branch compatible (by simpa using same)
      ((cursor.extend blobs source grows).exec blobs source codec label body next recorded roundtrip) known
    exact continues.extend_before blobs source grows ⟨1, 0, fun fuel _ => by simpa [Nat.add_comm] using executes fuel⟩
  | parallelOk codec count branches next outcomes roundtrip children returned collected present rest ihChildren ih =>
    intro encode journal branch consistent same cursor known
    apply parallel_runs blobs source expected journal branch _ same encode codec count branches next outcomes _ cursor consistent known
      (by simpa [collected, Parallel.recorded] using present) returned
    · intro index after grows compatible
      have childCursor := (cursor.extend blobs source grows).child blobs source codec count branches next index
      exact Verified.step blobs source childCursor ⟨0, _⟩ (Location.branchStart_child _ _).symm _ compatible (returned index)
        (ihChildren index codec.encode after _ compatible (Location.branchStart_child _ _).symm childCursor (returned index))
    · intro after grows compatible recorded
      have presentAfter := recorded
      simp only [collected, Parallel.recorded] at presentAfter
      have size : _ := Parallel.sequence_size _ _ collected
      simp only [Array.size_ofFn] at size
      have continues := ih encode after branch compatible (by simpa using same)
        ((cursor.extend blobs source grows).joined blobs source codec count branches next _ presentAfter (roundtrip.array codec _) size)
        known
      apply continues.replace blobs source
      exact ⟨1, fun fuel => by simpa only [Nat.add_comm 1, Parallel.recorded] using
        Recording.group_success encode after blobs branch _ fuel codec count branches next _ roundtrip size presentAfter⟩
  | parallelError codec count branches next outcomes roundtrip children returned collected present ihChildren =>
    intro encode journal branch consistent same cursor known
    apply parallel_runs blobs source expected journal branch _ same encode codec count branches next outcomes _ cursor consistent known
      (by simpa [collected, Parallel.recorded] using present) returned
    · intro index after grows compatible
      have childCursor := (cursor.extend blobs source grows).child blobs source codec count branches next index
      exact Verified.step blobs source childCursor ⟨0, _⟩ (Location.branchStart_child _ _).symm _ compatible (returned index)
        (ihChildren index codec.encode after _ compatible (Location.branchStart_child _ _).symm childCursor (returned index))
    · intro after grows compatible recorded
      simp only [collected, Parallel.recorded] at recorded
      apply (finish_verified blobs source expected after branch _ compatible known).replace blobs source
      exact ⟨1, fun fuel => by simpa only [Nat.add_comm 1, Parallel.recorded] using
        Recording.group_failure encode after blobs branch _ fuel codec count branches next _ recorded⟩

/-- From empty storage, the reference driver finishes and durably records the
pure result. No correct cache, successful execution, or fairness is a premise. -/
theorem finishes_from_empty {outcome} (evaluation : Pure.Evaluation source outcome) :
    ∃ bound journal, ∀ fuel, bound ≤ fuel →
      (LeanCloud.SequentialReplay.run store blobs source fuel
        ⟨0, Location.root⟩).run [] = (.ok (), journal) ∧
      journal.lookup (ReplayStore.returnKey Location.root) =
        some ⟨ReplayStore.returnRequest, Parallel.recorded rootCodec.encode outcome⟩ := by
  obtain ⟨expected, meaning, known⟩ := Specification.workflow_journal_exists evaluation rootCodec.encode
  let assignment : Assignment := ⟨0, Location.root⟩
  have cursor := Cursor.root blobs source []
  have active := complete_runs blobs source meaning rootCodec.encode [] Location.root (.empty _) (by simp) cursor known
  obtain ⟨journal, _, _, returned, execution⟩ := Verified.step blobs source cursor assignment (by simp [assignment]) _ (.empty _) known active
  obtain ⟨bound, finishes⟩ := execution.runs
  refine ⟨bound + 1, journal, fun fuel enough => ⟨?_, returned⟩⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show fuel ≠ 0 by omega)
  exact finishes (n + 1) (by omega)

/-- The decoded final result is the pure source result for every sufficiently
large budget, including a recorded application error. -/
theorem evaluates_from_empty {outcome} (evaluation : Pure.Evaluation source outcome)
    (roundtrip : Pure.RoundTrips rootCodec) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      ((LeanCloud.SequentialReplay.interpret store blobs fuel (fun _ : Unit => source) ()).run []).1 = outcome := by
  obtain ⟨bound, journal, finishes⟩ := finishes_from_empty blobs source evaluation
  refine ⟨bound, fun fuel enough => ?_⟩
  obtain ⟨finished, returned⟩ := finishes fuel enough
  simp only [LeanCloud.SequentialReplay.interpret, bind_run, finished]
  rw [Worker.read_completed journal _ _ returned]
  cases outcome with
  | ok value => simp [result, Parallel.recorded, Internal.decode, roundtrip value]
  | error error => rfl

end LeanCloud.Proofs.SequentialReplay
