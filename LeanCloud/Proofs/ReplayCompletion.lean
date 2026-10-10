import LeanCloud.Proofs.ProgramCursor
import LeanCloud.Proofs.ReplayExecution
import LeanCloud.Proofs.Recording

namespace LeanCloud.Proofs.ReplayCompletion
open Lean LeanEff ReplayModel ReplayInterpreter ProgramCursor ReplayExecution JournalMerge JournalRegion

variable {info : Option SourceSiteId}

variable [rootCodec : Codec α] (blobs : BlobStorage M) (source : Cloud M α) (mode : Mode)

abbrev sourceSteps : Step := steps blobs (fun _ : Unit => source) ()

def Verified (expected : Journal) (branch : Location) (outcome : Exit) (action : Action) (before : Journal) : Prop :=
  ∃ after, Extends before after ∧ Extends after expected ∧
    after.lookup (ReplayStore.returnKey branch) = some ⟨ReplayStore.returnRequest, outcome⟩ ∧
    Writes (Owns branch) before after ∧
    Execution (sourceSteps blobs source) mode branch action before after

theorem Verified.replace {expected branch outcome action replacement before}
    (verified : Verified blobs source mode expected branch outcome action before)
    (same : ∃ offset, ∀ fuel, (replacement (offset + fuel)).run before = (action fuel).run before) :
    Verified blobs source mode expected branch outcome replacement before := by
  obtain ⟨after, grows, consistent, returned, writes, execution⟩ := verified
  obtain ⟨offset, same⟩ := same
  exact ⟨after, grows, consistent, returned, writes, execution.replace ⟨offset, 0, fun fuel _ => same fuel⟩⟩

theorem Verified.extend_before {expected branch outcome action before middle}
    (verified : Verified blobs source mode expected branch outcome action middle)
    (written : Writes (Owns branch) before middle)
    (same : ∃ offset minimum, ∀ fuel, minimum ≤ fuel → (replacement (offset + fuel)).run before = (action fuel).run middle) :
    Verified blobs source mode expected branch outcome replacement before := by
  obtain ⟨after, extension, consistent, returned, writes, execution⟩ := verified
  exact ⟨after, written.extends.trans extension, consistent, returned, written.trans writes, execution.replace same⟩

theorem Verified.step {expected journal current} {encode : β → Json} {remaining : Cloud M β}
    (cursor : Cursor blobs source journal current encode remaining) (assignment : Assignment)
    (branch : assignment.branchStart = Location.branchStart current) (outcome : Exit)
    (consistent : Extends journal expected)
    (known : expected.lookup (ReplayStore.returnKey assignment.branchStart) = some ⟨ReplayStore.returnRequest, outcome⟩)
    (verified : Verified blobs source mode expected assignment.branchStart outcome
      (fun fuel => replay store blobs assignment.branchStart fuel encode remaining current) journal) :
    Verified blobs source mode expected assignment.branchStart outcome (sourceSteps blobs source assignment) journal := by
  let point : ReplayTarget := ⟨assignment.branchStart, current⟩
  cases found : journal.lookup (ReplayStore.returnKey assignment.branchStart) with
  | none => exact verified.replace blobs source mode (cursor.step blobs source point branch rfl found)
  | some record =>
    have same := Option.some.inj ((consistent _ _ found).symm.trans known)
    subst record
    have route := cursor.follows
    have nonempty : 0 < current.size := Nat.lt_of_lt_of_le (by decide) route.depth
    have first : current[0]!.1 = 0 := by simpa [LeanCloud.Location.root] using (route.branch_at 0 (by decide)).symm
    have valid : (!point.branchStart.isEmpty && point.branchStart[0]!.1 == 0) = true := by
      simp [point, branch, Array.isEmpty, Nat.ne_of_gt nonempty, Location.branchStart_index _ 0 nonempty, first]
    exact ⟨journal, .refl _, consistent, found, .refl _ _, .done ⟨0, fun fuel _ =>
      completed_step_reuses_record journal blobs point (fun _ : Unit => source) () fuel _ valid found (by simp)⟩⟩

private theorem run_list {κ : Type} (expected initial : Journal) (items : List κ)
    (job : κ → Assignment) (outcome : κ → Exit) (region : String → Prop)
    (inside : ∀ item ∈ items, ∀ key, Owns (job item).branchStart key → region key)
    (separate : items.Pairwise (fun i j => ∀ key, Owns (job i).branchStart key → Owns (job j).branchStart key → False))
    (consistent : Extends initial expected)
    (each : ∀ item ∈ items, ∀ journal, Extends initial journal → Extends journal expected →
      Verified blobs source mode expected (job item).branchStart (outcome item) (sourceSteps blobs source (job item)) journal) :
    ∃ after, Extends initial after ∧ Extends after expected ∧
      (∀ item ∈ items, after.lookup (ReplayStore.returnKey (job item).branchStart) =
        some ⟨ReplayStore.returnRequest, outcome item⟩) ∧
      Writes region initial after ∧
      Batch (sourceSteps blobs source) mode (items.map job) initial after := by
  cases mode with
  | sequential =>
    induction items generalizing initial with
    | nil => exact ⟨initial, .refl _, consistent, by simp, .refl _ _, .nil⟩
    | cons item rest ih =>
      obtain ⟨middle, grows, compatible, returned, written, first⟩ := each item (by simp) initial (.refl _) consistent
      obtain ⟨after, extension, compatibleAfter, returns, restWrites, later⟩ := ih middle
        (fun other member => inside other (by simp [member])) (List.pairwise_cons.mp separate).2 compatible (by
          intro other member journal more consistent
          exact each other (by simp [member]) journal (grows.trans more) consistent)
      refine ⟨after, grows.trans extension, compatibleAfter, ?_,
        (written.mono (inside item (by simp))).trans restWrites, .cons first later⟩
      intro other member
      rcases List.mem_cons.mp member with rfl | member
      · exact extension _ _ returned
      · exact returns other member
  | parallel =>
    classical
    have witnesses : ∀ item, ∃ after, item ∈ items →
        Extends initial after ∧ Extends after expected ∧
        after.lookup (ReplayStore.returnKey (job item).branchStart) = some ⟨ReplayStore.returnRequest, outcome item⟩ ∧
        Writes (Owns (job item).branchStart) initial after ∧
        Execution (sourceSteps blobs source) .parallel (job item).branchStart (sourceSteps blobs source (job item)) initial after := by
      intro item
      by_cases member : item ∈ items
      · obtain ⟨after, valid⟩ := each item member initial (.refl _) consistent
        exact ⟨after, fun _ => valid⟩
      · exact ⟨initial, fun found => False.elim (member found)⟩
    let journals := fun item => Classical.choose (witnesses item)
    have valid := fun item member => Classical.choose_spec (witnesses item) member
    obtain ⟨after, merged, grows, compatible, preserved, written⟩ := JournalMerge.children_within items journals
      (fun item => Owns (job item).branchStart) initial expected consistent
      (fun item member => (valid item member).2.1) (fun item member => (valid item member).2.2.2.1) separate
    refine ⟨after, grows, compatible, fun item member => preserved item member _ _ (valid item member).2.2.1,
      written.mono ?_, .parallel items job journals (fun item member => (valid item member).2.2.2.2) merged⟩
    rintro key ⟨item, member, owned⟩
    exact inside item member key owned

private theorem join_records (expected journal : Journal) (branch current : Location)
    (encode : β → Json) (codec : Codec γ) (count : Nat) (branches : Fin count → Cloud M γ)
    (next : ArrsF (Control M) SourceSiteId (Array γ) β) (outcome : Exit)
    (consistent : Extends journal expected)
    (known : expected.lookup (ReplayStore.valueKey current) =
      some ⟨⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩, outcome⟩)
    (ready : Recording.JoinReady expected journal current) :
    ∃ after, Extends journal after ∧ Extends after expected ∧
      Writes (fun key => key = ReplayStore.valueKey current) journal after ∧
      after.lookup (ReplayStore.valueKey current) =
        some ⟨⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩, outcome⟩ ∧
      ∀ fuel, (replay store blobs branch (fuel + 1) encode (.impure info (.parallel codec count branches) next) current).run journal =
        (replay store blobs branch (fuel + 1) encode (.impure info (.parallel codec count branches) next) current).run after := by
  cases found : journal.lookup (ReplayStore.valueKey current) with
  | some record =>
    exact ⟨journal, .refl _, consistent, .refl _ _, found.trans ((consistent _ _ found).symm.trans known), by intros; rfl⟩
  | none =>
    obtain ⟨children, completed, collected⟩ := ready codec.schema count outcome known
    have accepted := create_within journal expected _ _ consistent known
    refine ⟨_, create_extends journal _ _, accepted.2, Writes.create _ _ _ _ rfl,
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
      Verified blobs source mode expected (current.child index) (Parallel.recorded codec.encode (outcomes index))
        (sourceSteps blobs source ⟨0, current.child index⟩) after)
    (cached : ∀ after, Extends journal after → Extends after expected →
      after.lookup (ReplayStore.valueKey current) =
        some ⟨⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩,
          Parallel.recorded (fun values => Json.arr (values.map codec.encode)) ((Array.ofFn outcomes).mapM id)⟩ →
      Verified blobs source mode expected branch outcome
        (fun fuel => replay store blobs branch fuel encode (.impure info (.parallel codec count branches) next) current) after) :
    Verified blobs source mode expected branch outcome
      (fun fuel => replay store blobs branch fuel encode (.impure info (.parallel codec count branches) next) current) journal := by
  have joinRun : ∀ after, Extends journal after → Extends after expected →
      Recording.JoinReady expected after current →
      Verified blobs source mode expected branch outcome
        (fun fuel => replay store blobs branch fuel encode (.impure info (.parallel codec count branches) next) current) after := by
    intro after grows compatible ready
    obtain ⟨recorded, extension, consistentAfter, written, present, executes⟩ := join_records blobs expected after branch current encode codec count branches next _
      compatible group ready
    have complete := cached recorded (grows.trans extension) consistentAfter present
    apply complete.extend_before blobs source mode (written.mono (fun key eq => eq ▸ Owns.value sameBranch))
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
    · obtain ⟨joined, grows, compatible, returns, childWrites, batch⟩ := run_list blobs source mode expected journal (List.finRange count)
        (fun index => ⟨0, current.child index⟩)
        (fun index => Parallel.recorded codec.encode (outcomes index)) (Owns branch)
        (fun _ _ _ owned => Owns.child sameBranch owned)
        (by
          apply (List.nodup_finRange count).imp
          intro i j different key first second
          exact Under.separate (by intro eq; exact different (Fin.ext eq))
            (first current i rfl) (second current j rfl)) consistent
        (fun index _ => children index)
      have childRecords := fun index => returns index (List.mem_finRange index)
      have joinReady := Recording.JoinReady.of_children expected joined current codec count outcomes group childRecords
      have active := joinRun joined grows compatible joinReady
      obtain ⟨after, extension, consistentAfter, returned, written, resumed⟩ := Verified.step blobs source mode
        (cursor.extend blobs source grows) ⟨0, branch⟩ sameBranch outcome compatible known active
      refine ⟨after, grows.trans extension, consistentAfter, returned, childWrites.trans written, .fork (location := current) (count := count) (forked := journal) ?_ ?_ resumed⟩
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
    Verified blobs source mode expected branch outcome (fun _ => Internal.finish store branch outcome) journal := by
  obtain ⟨after, grows, compatible, written, returned, finishes⟩ := Recording.finish_within journal expected branch outcome consistent known
  exact ⟨after, grows, compatible, returned, written, .done ⟨0, fun _ _ => finishes⟩⟩

/-- Every pure source subtree has a finite execution through actual replay
steps. The journal may start empty; only records already written are replayed. -/
theorem complete_runs {expected current} {program : Cloud M β} {outcome budget}
    (meaning : Specification.Complete expected current program outcome budget) :
    ∀ (encode : β → Json) journal branch, Extends journal expected →
      branch = Location.branchStart current →
      Cursor blobs source journal current encode program →
      expected.lookup (ReplayStore.returnKey branch) =
        some ⟨ReplayStore.returnRequest, Parallel.recorded encode outcome⟩ →
      Verified blobs source mode expected branch (Parallel.recorded encode outcome)
        (fun fuel => replay store blobs branch fuel encode program current) journal := by
  induction meaning with
  | pure value =>
    intro encode journal branch consistent same cursor known
    apply (finish_verified blobs source mode expected journal branch _ consistent known).replace blobs source mode
    exact ⟨1, fun fuel => by simp [Nat.add_comm 1 fuel, replay, Parallel.recorded]⟩
  | fail error next =>
    intro encode journal branch consistent same cursor known
    apply (finish_verified blobs source mode expected journal branch _ consistent known).replace blobs source mode
    exact ⟨1, fun fuel => by simp [Nat.add_comm 1 fuel, replay, Parallel.recorded]⟩
  | delay next rest ih =>
    intro encode journal branch consistent same cursor known
    apply (ih encode journal branch consistent same (cursor.delay blobs source next) known).replace blobs source mode
    exact ⟨1, fun fuel => by simp [Nat.add_comm 1 fuel, replay]⟩
  | exec codec label body next roundtrip present rest ih =>
    intro encode journal branch consistent same cursor known
    obtain ⟨after, grows, compatible, written, recorded, executes⟩ := Recording.exec_within encode journal expected blobs branch _ codec label body next roundtrip consistent present
    have continues := ih encode after branch compatible (by simpa using same)
      ((cursor.extend blobs source grows).exec blobs source codec label body next recorded roundtrip) known
    exact continues.extend_before blobs source mode (written.mono (fun key eq => eq ▸ Owns.value same)) ⟨1, 0, fun fuel _ => by simpa [Nat.add_comm] using executes fuel⟩
  | parallelOk codec count branches next outcomes roundtrip children returned collected present rest ihChildren ih =>
    intro encode journal branch consistent same cursor known
    apply parallel_runs blobs source mode expected journal branch _ same encode codec count branches next outcomes _ cursor consistent known
      (by simpa [collected, Parallel.recorded] using present) returned
    · intro index after grows compatible
      have childCursor := (cursor.extend blobs source grows).child blobs source codec count branches next index
      exact Verified.step blobs source mode childCursor ⟨0, _⟩ (Location.branchStart_child _ _).symm _ compatible (returned index)
        (ihChildren index codec.encode after _ compatible (Location.branchStart_child _ _).symm childCursor (returned index))
    · intro after grows compatible recorded
      have presentAfter := recorded
      simp only [collected, Parallel.recorded] at presentAfter
      have size : _ := Parallel.sequence_size _ _ collected
      simp only [Array.size_ofFn] at size
      have continues := ih encode after branch compatible (by simpa using same)
        ((cursor.extend blobs source grows).joined blobs source codec count branches next _ presentAfter (roundtrip.array codec _) size)
        known
      apply continues.replace blobs source mode
      exact ⟨1, fun fuel => by simpa only [Nat.add_comm 1, Parallel.recorded] using
        Recording.group_success encode after blobs branch _ fuel codec count branches next _ roundtrip size presentAfter⟩
  | parallelError codec count branches next outcomes roundtrip children returned collected present ihChildren =>
    intro encode journal branch consistent same cursor known
    apply parallel_runs blobs source mode expected journal branch _ same encode codec count branches next outcomes _ cursor consistent known
      (by simpa [collected, Parallel.recorded] using present) returned
    · intro index after grows compatible
      have childCursor := (cursor.extend blobs source grows).child blobs source codec count branches next index
      exact Verified.step blobs source mode childCursor ⟨0, _⟩ (Location.branchStart_child _ _).symm _ compatible (returned index)
        (ihChildren index codec.encode after _ compatible (Location.branchStart_child _ _).symm childCursor (returned index))
    · intro after grows compatible recorded
      simp only [collected, Parallel.recorded] at recorded
      apply (finish_verified blobs source mode expected after branch _ compatible known).replace blobs source mode
      exact ⟨1, fun fuel => by simpa only [Nat.add_comm 1, Parallel.recorded] using
        Recording.group_failure encode after blobs branch _ fuel codec count branches next _ recorded⟩
  | weaken complete enough ih => exact ih

/-- From empty storage, the reference driver finishes and durably records the
pure result. No correct cache, successful execution, or fairness is a premise. -/
theorem finishes_from_empty {outcome} (evaluation : Pure.Evaluation source outcome) :
    ∃ bound journal, ∀ fuel, bound ≤ fuel →
      (ReplayExecution.run blobs (fun _ : Unit => source) () mode fuel
        ⟨0, Location.root⟩).run [] = (.ok (), journal) ∧
      journal.lookup (ReplayStore.returnKey Location.root) =
        some ⟨ReplayStore.returnRequest, Parallel.recorded rootCodec.encode outcome⟩ := by
  obtain ⟨expected, budget, meaning, known⟩ := Specification.workflow_journal_exists evaluation rootCodec.encode
  let assignment : Assignment := ⟨0, Location.root⟩
  have cursor := Cursor.root blobs source []
  have active := complete_runs blobs source mode meaning rootCodec.encode [] Location.root (.empty _) (by simp) cursor known
  obtain ⟨journal, _, _, returned, _, execution⟩ := Verified.step blobs source mode cursor assignment (by simp [assignment]) _ (.empty _) known active
  obtain ⟨bound, finishes⟩ := execution.runs
  refine ⟨bound + 1, journal, fun fuel enough => ⟨?_, returned⟩⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show fuel ≠ 0 by omega)
  simpa only [ReplayExecution.run_succ] using finishes (n + 1) (by omega)

/-- Sufficient fuel returns the pure result, including application failures. -/
theorem evaluates_from_empty {outcome} (evaluation : Pure.Evaluation source outcome)
    (roundtrip : Pure.RoundTrips rootCodec) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      let replay := match mode with
        | .sequential => SequentialReplay.interpret store noBlobs fuel (fun _ : Unit => source) ()
        | .parallel => ParallelReplay.interpret fuel (fun _ : Unit => source) ()
      (replay.run []).1 = outcome := by
  obtain ⟨bound, journal, finishes⟩ := finishes_from_empty noBlobs source mode evaluation
  refine ⟨bound, fun fuel enough => ?_⟩
  obtain ⟨finished, returned⟩ := finishes fuel enough
  cases mode <;>
    simp only [ReplayExecution.run] at finished <;>
    simp only [SequentialReplay.interpret, ParallelReplay.interpret, bind_run, finished] <;>
    rw [Results.read_completed journal _ _ returned] <;>
    cases outcome with
    | ok value => simp [result, Parallel.recorded, Internal.decode, roundtrip value]
    | error error => rfl

end LeanCloud.Proofs.ReplayCompletion
