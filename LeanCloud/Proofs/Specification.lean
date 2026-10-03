import LeanCloud.Proofs.Pure
import LeanCloud.Proofs.Parallel
import LeanCloud.Proofs.Reconstruction
import LeanCloud.Proofs.JournalRegion

namespace LeanCloud.Proofs.Specification
open Lean LeanEff ReplayModel JournalRegion

/-- A real parallel group in the pure specification: its children have known
returns, and their ordered reduction is the expected group result. -/
def Group (journal : Journal) (location : LeanCloud.Location) (count : Nat) : Prop :=
  ∃ (α : Type) (codec : Codec α) (outcomes : Fin count → Except CloudError α),
    journal.lookup (ReplayStore.valueKey location) =
      some ⟨⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩,
        Parallel.recorded (fun values => Json.arr (values.map codec.encode)) ((Array.ofFn outcomes).mapM id)⟩ ∧
    ∀ index : Fin count, journal.lookup (ReplayStore.returnKey (location.child index)) =
      some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode (outcomes index)⟩

/-- A complete pure specification includes every evaluated child, its return
record, and the ordered join result. The branch's own return record is separate.
This relation describes the program; it does not execute another interpreter. -/
inductive Complete {m : Type → Type u} [Monad m] (journal : Journal) :
    {α : Type} → LeanCloud.Location → Cloud m α → Except CloudError α → Prop where
  | pure (value : α) : Complete journal current (EffF.pure value) (.ok value)
  | fail (error : CloudError) (next : ArrsF (Control m) α β) :
      Complete journal current (.impure (.fail error) next) (.error error)
  | delay (next : ArrsF (Control m) Unit α)
      (rest : Complete journal current (next.apply ()) outcome) :
      Complete journal current (.impure .delay next) outcome
  | exec (codec : Codec α) (label : String) (body : Unit → α) (next : ArrsF (Control m) α β)
      (roundtrip : codec.decode (codec.encode (body ())) = .ok (body ()))
      (present : journal.lookup (ReplayStore.valueKey current) =
        some ⟨ReplayInterpreter.Internal.request codec (.exec label (fun _ => pure (body ()) : Unit → m _)),
          .success (codec.encode (body ()))⟩)
      (rest : Complete journal current.next (next.apply (body ())) outcome) :
      Complete journal current
        (.impure (.sequential codec (.exec label (fun _ => pure (body ())))) next) outcome
  | parallelOk (codec : Codec α) (count : Nat) (branches : Fin count → Cloud m α)
      (next : ArrsF (Control m) (Array α) β) (outcomes : Fin count → Except CloudError α)
      (roundtrip : Pure.RoundTrips codec)
      (children : ∀ index : Fin count, Complete journal (current.child index) (branches index) (outcomes index))
      (returned : ∀ index : Fin count, journal.lookup (ReplayStore.returnKey (current.child index)) =
        some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode (outcomes index)⟩)
      (collected : (Array.ofFn outcomes).mapM id = .ok values)
      (present : journal.lookup (ReplayStore.valueKey current) =
        some ⟨⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩,
          .success (Json.arr (values.map codec.encode))⟩)
      (rest : Complete journal current.next (next.apply values) outcome) :
      Complete journal current (.impure (.parallel codec count branches) next) outcome
  | parallelError (codec : Codec α) (count : Nat) (branches : Fin count → Cloud m α)
      (next : ArrsF (Control m) (Array α) β) (outcomes : Fin count → Except CloudError α)
      (roundtrip : Pure.RoundTrips codec)
      (children : ∀ index : Fin count, Complete journal (current.child index) (branches index) (outcomes index))
      (returned : ∀ index : Fin count, journal.lookup (ReplayStore.returnKey (current.child index)) =
        some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode (outcomes index)⟩)
      (collected : (Array.ofFn outcomes).mapM id = .error error)
      (present : journal.lookup (ReplayStore.valueKey current) =
        some ⟨⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩, .failure error⟩) :
      Complete journal current (.impure (.parallel codec count branches) next) (.error error)

/-- Forget recorded values to recover the original pure source meaning. -/
theorem Complete.evaluation {m : Type → Type u} [Monad m] {α : Type}
    {journal current} {program : Cloud m α} {outcome}
    (complete : Complete journal current program outcome) :
    Pure.Evaluation program outcome := by
  induction complete with
  | pure value => exact .pure value
  | fail error next => exact .fail error next
  | delay next rest ih => exact .delay next ih
  | exec codec label body next roundtrip present rest ih =>
    exact .exec codec label body next roundtrip ih
  | parallelOk codec count branches next outcomes roundtrip children returned collected present rest ihChildren ih =>
    exact .parallelOk codec count branches next outcomes roundtrip ihChildren collected ih
  | parallelError codec count branches next outcomes roundtrip children returned collected present ihChildren =>
    exact .parallelError codec count branches next outcomes roundtrip ihChildren collected

theorem Complete.extend {m : Type → Type u} [Monad m] {α : Type}
    {before after current} {program : Cloud m α} {outcome}
    (complete : Complete before current program outcome) (extension : Extends before after) :
    Complete after current program outcome := by
  induction complete with
  | pure value => exact .pure value
  | fail error next => exact .fail error next
  | delay next rest ih => exact .delay next ih
  | exec codec label body next roundtrip present rest ih =>
    exact .exec codec label body next roundtrip (extension _ _ present) ih
  | parallelOk codec count branches next outcomes roundtrip children returned collected present rest ihChildren ih =>
    exact .parallelOk codec count branches next outcomes roundtrip ihChildren
      (fun index => extension _ _ (returned index)) collected (extension _ _ present) ih
  | parallelError codec count branches next outcomes roundtrip children returned collected present ihChildren =>
    exact .parallelError codec count branches next outcomes roundtrip ihChildren
      (fun index => extension _ _ (returned index)) collected (extension _ _ present)

/-- Extract only the continuations that can actually be resumed. Matching the
program before its control keeps the hidden request and child types aligned. -/
private theorem continuation_meanings {m : Type → Type u} [Monad m] {α : Type}
    {journal current} {program : Cloud m α} {outcome}
    (complete : Complete journal current program outcome) :
    match program with
    | EffF.pure _ => True
    | .impure control next =>
      match control with
      | .delay => Complete journal current (next.apply ()) outcome
      | .sequential codec _ =>
        ∀ record wire value,
          journal.lookup (ReplayStore.valueKey current) = some record →
          record.outcome = .success wire → codec.decode wire = .ok value →
          Complete journal current.next (next.apply value) outcome
      | .parallel codec count branches =>
        (∀ index : Fin count, ∃ result, Complete journal (current.child index) (branches index) result ∧
          journal.lookup (ReplayStore.returnKey (current.child index)) =
            some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode result⟩) ∧
        (∀ record wire values,
          journal.lookup (ReplayStore.valueKey current) = some record →
          record.outcome = .success wire →
          (@instCodecArray _ codec).decode wire = .ok values →
          Complete journal current.next (next.apply values) outcome)
      | _ => True := by
  cases complete with
  | pure => trivial
  | fail => trivial
  | delay next rest => exact rest
  | exec codec label body next roundtrip present rest =>
    intro record wire value found success decoded
    have same := Option.some.inj (found.symm.trans present)
    subst record
    cases success
    have sameValue := Except.ok.inj (decoded.symm.trans roundtrip)
    subst value
    exact rest
  | parallelOk codec count branches next outcomes roundtrip children returned collected present rest =>
    rename_i valueType expectedValues
    refine ⟨fun index => ⟨outcomes index, children index, returned index⟩, ?_⟩
    intro record wire values found success decoded
    have same := Option.some.inj (found.symm.trans present)
    subst record
    cases success
    have sameValue := Except.ok.inj (decoded.symm.trans (roundtrip.array codec expectedValues))
    subst values
    exact rest
  | parallelError codec count branches next outcomes roundtrip children returned collected present =>
    refine ⟨fun index => ⟨outcomes index, children index, returned index⟩, ?_⟩
    intro record wire values found success decoded
    have same := Option.some.inj (found.symm.trans present)
    subst record
    cases success

/-- A recorded prefix resumes a continuation from the same complete pure
workflow, with the expected result for its branch. Child descent changes both
result type and encoder; successful replay retains the branch's result. -/
theorem Complete.resume {m : Type → Type u} [Monad m] {α β : Type}
    {journal expected : Journal} {current target steps} {encode : α → Json}
    {program : Cloud m α} {outcome} {remainingEncode : β → Json} {remaining : Cloud m β}
    (complete : Complete expected current program outcome)
    (returned : expected.lookup (ReplayStore.returnKey (Location.branchStart current)) =
      some ⟨ReplayStore.returnRequest, Parallel.recorded encode outcome⟩)
    (witness : Reconstruction.Prefix journal target encode program current steps remainingEncode remaining)
    (consistent : Extends journal expected) :
    ∃ result, Complete expected target remaining result ∧
      expected.lookup (ReplayStore.returnKey (Location.branchStart target)) =
        some ⟨ReplayStore.returnRequest, Parallel.recorded remainingEncode result⟩ := by
  induction witness with
  | here encode program => exact ⟨outcome, complete, returned⟩
  | delay next before rest ih =>
    exact ih (continuation_meanings complete) returned
  | sequential codec operation next record wire value before present checked success decoded rest ih =>
    exact ih (continuation_meanings complete record wire value (consistent _ _ present) success decoded)
      (by simpa using returned)
  | joined codec count branches next record wire values before skip present checked success decoded size rest ih =>
    exact ih ((continuation_meanings complete).2 record wire values (consistent _ _ present) success decoded)
      (by simpa using returned)
  | child codec count branches next index before enters selected rest ih =>
    obtain ⟨result, child, childReturned⟩ := (continuation_meanings complete).1 index
    exact ih child (by simpa using childReturned)

private theorem children_exist {m : Type → Type u} [Monad m] (current : LeanCloud.Location)
    (codec : Codec α) (count : Nat) (branches : Fin count → Cloud m α)
    (outcomes : Fin count → Except CloudError α)
    (each : ∀ index : Fin count, ∃ journal, Complete journal (current.child index) (branches index) (outcomes index) ∧
      Covers (After current index 0) journal) :
    ∃ journal,
      (∀ index : Fin count, Complete journal (current.child index) (branches index) (outcomes index)) ∧
      (∀ index : Fin count, journal.lookup (ReplayStore.returnKey (current.child index)) =
        some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode (outcomes index)⟩) ∧
      Covers (fun key => ∃ child, Under current child key) journal := by
  classical
  have full : ∀ index : Fin count, ∃ journal,
      Complete journal (current.child index) (branches index) (outcomes index) ∧
      journal.lookup (ReplayStore.returnKey (current.child index)) =
        some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode (outcomes index)⟩ ∧
      Covers (Under current index) journal := by
    intro index
    obtain ⟨journal, complete, covered⟩ := each index
    let record : ReplayRecord := ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode (outcomes index)⟩
    obtain ⟨extension, coverage⟩ := covered.add_return (start := 0) record
    exact ⟨_, complete.extend extension, by simp [LeanCloud.Location.child, record], coverage⟩
  let journals := fun index => Classical.choose (full index)
  have evidence := fun index => Classical.choose_spec (full index)
  obtain ⟨merged, extension, coverage⟩ := merge_family count journals (fun index => Under current index)
    (fun index => (evidence index).2.2)
    (fun i j different _ first second => Under.separate (by intro same; exact different (Fin.ext same)) first second)
  exact ⟨merged, fun index => (evidence index).1.extend (extension index),
    fun index => extension index _ _ (evidence index).2.1,
    fun entry member => let ⟨index, inside⟩ := coverage entry member; ⟨index, inside⟩⟩

/-- Every supported pure evaluation has a finite complete expected journal,
including every nested child and its return record. Location separation makes
this construction consistent without assuming any records already exist. -/
theorem complete_journal_exists {m : Type → Type u} [Monad m] {α : Type}
    {program : Cloud m α} {outcome} (evaluation : Pure.Evaluation program outcome)
    (parent : LeanCloud.Location) (branch command : Nat) :
    ∃ journal, Complete journal (parent.push (branch, command)) program outcome ∧
      Covers (After parent branch command) journal := by
  induction evaluation generalizing parent branch command with
  | pure value => exact ⟨[], .pure value, by simp [Covers]⟩
  | fail error next => exact ⟨[], .fail error next, by simp [Covers]⟩
  | delay next rest ih =>
    obtain ⟨journal, complete, coverage⟩ := ih parent branch command
    exact ⟨journal, .delay next complete, coverage⟩
  | exec codec label body next roundtrip rest ih =>
    obtain ⟨journal, complete, coverage⟩ := ih parent branch (command + 1)
    let record : ReplayRecord :=
      ⟨ReplayInterpreter.Internal.request codec (.exec label (fun _ => pure (body ()) : Unit → m _)),
        .success (codec.encode (body ()))⟩
    obtain ⟨_, extension, present, coverage⟩ := assemble parent branch command [] journal record (by simp [Covers]) coverage
    refine ⟨_, .exec codec label body next roundtrip present ?_, coverage⟩
    simpa only [Location.next_push] using complete.extend extension
  | parallelOk codec count branches next outcomes roundtrip children collected rest ihChildren ih =>
    rename_i valueType resultType values result
    obtain ⟨descendants, childSpecs, returned, childRegion⟩ :=
      children_exist (parent.push (branch, command)) codec count branches outcomes
        (fun index => ihChildren index (parent.push (branch, command)) index 0)
    obtain ⟨journal, complete, coverage⟩ := ih parent branch (command + 1)
    let record : ReplayRecord :=
      ⟨⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩, .success (Json.arr (values.map codec.encode))⟩
    obtain ⟨childExtension, extension, present, coverage⟩ :=
      assemble parent branch command descendants journal record childRegion coverage
    refine ⟨_, .parallelOk codec count branches next outcomes roundtrip
      (fun index => (childSpecs index).extend childExtension)
      (fun index => childExtension _ _ (returned index)) collected present ?_, coverage⟩
    simpa only [Location.next_push] using complete.extend extension
  | parallelError codec count branches next outcomes roundtrip children collected ihChildren =>
    rename_i valueType resultType error
    obtain ⟨descendants, childSpecs, returned, childRegion⟩ :=
      children_exist (parent.push (branch, command)) codec count branches outcomes
        (fun index => ihChildren index (parent.push (branch, command)) index 0)
    let record : ReplayRecord := ⟨⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩, .failure error⟩
    obtain ⟨extension, _, present, coverage⟩ :=
      assemble parent branch command descendants [] record childRegion (by simp [Covers])
    exact ⟨_, .parallelError codec count branches next outcomes roundtrip
      (fun index => (childSpecs index).extend extension)
      (fun index => extension _ _ (returned index)) collected present, coverage⟩

/-- The complete workflow specification also contains its final root result.
The caller supplies a pure program and its meaning, not a prebuilt journal. -/
theorem workflow_journal_exists {m : Type → Type u} [Monad m] {α : Type}
    {program : Cloud m α} {outcome} (evaluation : Pure.Evaluation program outcome) (encode : α → Json) :
    ∃ journal, Complete journal LeanCloud.Location.root program outcome ∧
      journal.lookup (ReplayStore.returnKey LeanCloud.Location.root) =
        some ⟨ReplayStore.returnRequest, Parallel.recorded encode outcome⟩ := by
  obtain ⟨journal, complete, coverage⟩ := complete_journal_exists evaluation #[] 0 0
  let record : ReplayRecord := ⟨ReplayStore.returnRequest, Parallel.recorded encode outcome⟩
  obtain ⟨extension, _⟩ := coverage.add_return (start := 0) record
  exact ⟨_, complete.extend extension, by simp [LeanCloud.Location.root, record]⟩

end LeanCloud.Proofs.Specification
