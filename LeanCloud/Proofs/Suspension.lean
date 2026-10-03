import LeanCloud.Proofs.Resumption
import LeanCloud.Proofs.Segment
import LeanCloud.Worker

namespace LeanCloud.Proofs.Suspension
open Lean LeanEff ReplayModel ReplayInterpreter Reconstruction

/-- After suspension the parent can resume at its fork, and every child can be
reconstructed from the same source using the durable records already present. -/
def Paths {m : Type → Type u} (journal : Journal) (encode : α → Json) (program : Cloud m α)
    (current location : Location) (count : Nat) : Prop :=
  Resumable journal encode program current location ∧
    ∀ index : Fin count, Resumable journal encode program current (location.child index)

theorem Paths.lift {m : Type → Type u} {journal current source location count}
    {encode : α → Json} {program : Cloud m α} {sourceEncode : β → Json} {sourceProgram : Cloud m β}
    (paths : Paths journal encode program current location count)
    (lift : ∀ target, Resumable journal encode program current target →
      Resumable journal sourceEncode sourceProgram source target) :
    Paths journal sourceEncode sourceProgram source location count :=
  ⟨lift _ paths.1, fun index => lift _ (paths.2 index)⟩

theorem Paths.extend {m : Type → Type u} {before after current location count}
    {encode : α → Json} {program : Cloud m α} (paths : Paths before encode program current location count)
    (extension : Extends before after) : Paths after encode program current location count :=
  ⟨paths.1.extend extension, fun index => (paths.2 index).extend extension⟩

theorem Paths.prepend {m : Type → Type u} {journal source current location count steps}
    {encode : α → Json} {program : Cloud m α} {sourceEncode : β → Json} {sourceProgram : Cloud m β}
    (paths : Paths journal encode program current location count)
    (witness : Prefix journal current sourceEncode sourceProgram source steps encode program)
    (nonempty : 0 < source.size) : Paths journal sourceEncode sourceProgram source location count :=
  paths.lift (fun _ resumable => resumable.prepend witness nonempty)

/-- The paths carried by a fork report are mathematical certificates of the
existing message; no continuation or program is added to its wire format. -/
def ReportPaths {m : Type → Type u} (journal : Journal) (encode : α → Json) (program : Cloud m α)
    (report : Report) : Prop :=
  ∀ location count, report.progress = .ok (.fork location count) →
    Paths journal encode program Location.root location count

theorem ReportPaths.extend {m : Type → Type u} {before after} {encode : α → Json} {program : Cloud m α} {report}
    (paths : ReportPaths before encode program report) (extension : Extends before after) :
    ReportPaths after encode program report :=
  fun location count forked => (paths location count forked).extend extension

theorem immediate {m : Type → Type u} (journal : Journal) (encode : β → Json) (current : Location)
    (codec : Codec α) (count : Nat) (branches : Fin count → Cloud m α) (next : ArrsF (Control m) (Array α) β) :
    Paths journal encode (.impure (.parallel codec count branches) next) current current count :=
  ⟨.here .., fun index => .child journal encode current codec count branches next index⟩

/-- An actual worker suspension produces reconstructible paths for the fork and
all its children. The proof includes missing pure effects and newly stored joins,
not only replay through a prepopulated journal. -/
theorem segment_fork_paths (expected : Journal) (blobs : BlobStorage M)
    (assignment : Assignment) (encode : α → Json)
    (journal : Journal) (consistent : Extends journal expected) (fuel : Nat)
    (ready : assignment.joining = true → Recording.JoinReady expected journal assignment.location)
    {current : Location} {program : Cloud M α} {outcome}
    (meaning : Specification.Complete expected current program outcome)
    (nonempty : 0 < current.size) (branch : assignment.branch = Location.branchStart current)
    (known : expected.lookup (ReplayStore.returnKey assignment.branch) =
      some ⟨ReplayStore.returnRequest, Parallel.recorded encode outcome⟩)
    {location count after} (suspended :
      (walk store blobs assignment fuel encode program current true).run journal = (.ok (.fork location count), after)) :
    Paths after encode program current location count := by
  cases fuel with
  | zero => cases suspended
  | succ fuel =>
    cases meaning with
    | pure value =>
      obtain ⟨_, _, _, _, finished⟩ := Recording.finish_within journal expected assignment.branch
        (.success (encode value)) consistent known
      have same : (Internal.finish store assignment.branch (.success (encode value))).run journal =
          (.ok (.fork location count), after) := by simpa [walk] using suspended
      rw [finished] at same
      cases same
    | fail error next =>
      obtain ⟨_, _, _, _, finished⟩ := Recording.finish_within journal expected assignment.branch
        (.failure error) consistent known
      have same : (Internal.finish store assignment.branch (.failure error)).run journal =
          (.ok (.fork location count), after) := by simpa [walk] using suspended
      rw [finished] at same
      cases same
    | delay next rest =>
      have continued : (walk store blobs assignment fuel encode (next.apply ()) current true).run journal =
          (.ok (.fork location count), after) := by simpa [walk] using suspended
      have paths := segment_fork_paths expected blobs assignment encode journal consistent fuel ready
        rest nonempty branch known continued
      exact paths.lift (fun _ resumable => resumable.delay next)
    | exec codec label body next roundtrip present rest =>
      obtain ⟨recordedJournal, grows, remains, recorded, continues⟩ :=
        Recording.exec_within encode journal expected blobs assignment current fuel codec label body next roundtrip consistent present
      have continued := continues.symm.trans suspended
      have nonemptyNext : 0 < current.next.size := by simpa [LeanCloud.Location.next] using nonempty
      have branchNext : assignment.branch = Location.branchStart current.next := by simpa using branch
      have readyAfter := fun joining => (ready joining).extend grows
      have safe := Segment.segment_preserves_results expected blobs assignment encode recordedJournal remains fuel
        readyAfter rest branchNext known
      have extension : Extends recordedJournal after := by simpa only [continued] using safe.grows
      have paths := segment_fork_paths expected blobs assignment encode recordedJournal remains fuel readyAfter
        rest nonemptyNext branchNext known continued
      apply paths.lift
      intro target resumable
      exact Resumable.sequential codec (.exec label (fun _ => pure (body ()))) next _ _ _ nonempty
        (extension _ _ recorded) (by simp) rfl roundtrip resumable
    | parallelOk codec size branches next outcomes roundtrip children returned collected present rest =>
      rename_i childType values
      rcases Recording.group_record_or_suspend encode journal expected blobs assignment current fuel codec size branches next _
          consistent present ready with stopped | ⟨recordedJournal, grows, remains, recorded, continues⟩
      · rw [stopped] at suspended
        cases suspended
        exact immediate journal encode current codec _ branches next
      · have continued := (continues.trans (Recording.group_success encode recordedJournal blobs assignment current fuel
          codec size branches next values roundtrip (by simpa using Parallel.sequence_size _ _ collected) recorded)).symm.trans suspended
        have nonemptyNext : 0 < current.next.size := by simpa [LeanCloud.Location.next] using nonempty
        have branchNext : assignment.branch = Location.branchStart current.next := by simpa using branch
        have readyAfter := fun joining => (ready joining).extend grows
        have safe := Segment.segment_preserves_results expected blobs assignment encode recordedJournal remains fuel
          readyAfter rest branchNext known
        have extension : Extends recordedJournal after := by simpa only [continued] using safe.grows
        have paths := segment_fork_paths expected blobs assignment encode recordedJournal remains fuel readyAfter
          rest nonemptyNext branchNext known continued
        apply paths.lift
        intro target resumable
        exact Resumable.joined codec size branches next _ _ values nonempty (extension _ _ recorded)
          (by simp) rfl (roundtrip.array codec values) (by simpa using Parallel.sequence_size _ _ collected) resumable
    | parallelError codec size branches next outcomes roundtrip children returned collected present =>
      rcases Recording.group_record_or_suspend encode journal expected blobs assignment current fuel codec size branches next _
          consistent present ready with stopped | ⟨recordedJournal, grows, remains, recorded, continues⟩
      · rw [stopped] at suspended
        cases suspended
        exact immediate journal encode current codec _ branches next
      · rw [continues, Recording.group_failure encode recordedJournal blobs assignment current fuel codec size branches next _ recorded]
          at suspended
        obtain ⟨_, _, _, _, finished⟩ := Recording.finish_within recordedJournal expected assignment.branch _ remains known
        simp only [Parallel.recorded] at finished
        rw [finished] at suspended
        cases suspended
termination_by fuel

/-- A fork returned by the deployed worker entry point supplies paths from the
original workflow to the parent join and every child. The original prefix may
cross nested branches and successful earlier groups. -/
theorem worker_fork_paths [codec : Codec α] (expected journal : Journal) (blobs : BlobStorage M)
    (assignment : Assignment) (program : ι → Cloud M α) (input : ι) (fuel : Nat)
    {β : Type} {remainingEncode : β → Json} {remaining : Cloud M β} {prefixSteps outcome}
    (meaning : Specification.Complete expected Location.root (program input) outcome)
    (known : expected.lookup (ReplayStore.returnKey Location.root) =
      some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode outcome⟩)
    (consistent : Extends journal expected)
    (branch : assignment.branch = Location.branchStart assignment.location)
    (witness : Prefix journal assignment.location codec.encode (program input)
      Location.root prefixSteps remainingEncode remaining)
    (ready : assignment.joining = true → Recording.JoinReady expected journal assignment.location)
    {location count after} (suspended :
      (step store blobs (prefixSteps + fuel) program input assignment).run journal = (.ok (.fork location count), after)) :
    Paths after codec.encode (program input) Location.root location count := by
  have resumable : Resumable journal codec.encode (program input) Location.root assignment.location :=
    ⟨β, remainingEncode, remaining, prefixSteps, witness⟩
  have nonempty := Nat.lt_of_lt_of_le (by decide : 0 < Location.root.size) (witness.follows (by decide)).depth
  obtain ⟨result, resumed, returned⟩ := meaning.resume (by simpa using known) witness consistent
  rw [← branch] at returned
  cases found : journal.lookup (ReplayStore.returnKey assignment.branch) with
  | none =>
    rw [step_resumes_at_location journal blobs assignment program input fuel resumable.valid_root found witness,
      walk_at_assignment] at suspended
    have paths := segment_fork_paths expected blobs assignment remainingEncode journal consistent fuel ready
      resumed nonempty branch returned suspended
    have safe := Segment.segment_preserves_results expected blobs assignment remainingEncode journal consistent fuel
      ready resumed branch returned
    have grows : Extends journal after := by simpa only [suspended] using safe.grows
    exact paths.prepend (witness.extend grows) (by decide)
  | some record =>
    have same := Option.some.inj ((consistent _ _ found).symm.trans returned)
    subst record
    rw [completed_step_reuses_record journal blobs assignment program input (prefixSteps + fuel) _
      resumable.valid_root found (by simp)] at suspended
    cases suspended

/-- The actual worker report retains the paths established by its replay step.
Observing record keys does not change the durable journal. -/
theorem execute_report_paths [codec : Codec α] (journal : Journal) (blobs : BlobStorage M)
    (worker : WorkerId) (assignment : Assignment) (fuel : Nat) (program : ι → Cloud M α) (input : ι)
    (confirmed : M (Array String)) (readOnly : ∀ records, (confirmed.run records).2 = records)
    (paths : ∀ location count after,
      (step store blobs fuel program input assignment).run journal = (.ok (.fork location count), after) →
      Paths after codec.encode (program input) Location.root location count) :
    let observed : LeanCloud.Worker.ObservedStore M := ⟨store, confirmed⟩
    let (report, after) := (LeanCloud.Worker.execute worker observed blobs fuel program input assignment).run journal
    ReportPaths after codec.encode (program input) report := by
  let execution := (step store blobs fuel program input assignment).run journal
  change ReportPaths (confirmed.run execution.2).2 codec.encode (program input)
    ⟨worker, assignment.attempt, execution.1, (confirmed.run execution.2).1⟩
  rw [readOnly]
  intro location count forked
  exact paths location count execution.2 (Prod.ext forked rfl)

end LeanCloud.Proofs.Suspension
