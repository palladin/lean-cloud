import LeanCloud.Proofs.Pure
import LeanCloud.Proofs.Parallel
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
The budget bounds a path through the finite evaluation, including children.
This relation describes the program; it does not execute another interpreter. -/
inductive Complete {m : Type → Type u} [Monad m] (expected : Journal) :
    {α : Type} → Location → Cloud m α → Except CloudError α → Nat → Prop where
  | pure {info : Option SourceSiteId} (value : α) : Complete expected current (EffF.pure info value) (.ok value) 1
  | fail {info : Option SourceSiteId} (error : CloudError) (next : ArrsF (Control m) SourceSiteId α β) :
      Complete expected current (.impure info (.fail error) next) (.error error) 1
  | delay {info : Option SourceSiteId} (next : ArrsF (Control m) SourceSiteId Unit α)
      (rest : Complete expected current (next.apply ()) outcome budget) :
      Complete expected current (.impure info .delay next) outcome (budget + 1)
  | exec {info : Option SourceSiteId} (codec : Codec α) (label : String) (body : Unit → α)
      (next : ArrsF (Control m) SourceSiteId α β)
      (roundtrip : codec.decode (codec.encode (body ())) = .ok (body ()))
      (present : expected.lookup (ReplayStore.valueKey current) =
        some ⟨ReplayInterpreter.Internal.request codec (.exec label (fun _ => pure (body ()) : Unit → m α)),
          .success (codec.encode (body ()))⟩)
      (rest : Complete expected current.next (next.apply (body ())) outcome budget) :
      Complete expected current (.impure info (.command codec (.exec label (fun _ => pure (body ())))) next)
        outcome (budget + 1)
  | parallelOk {info : Option SourceSiteId} (codec : Codec α) (count : Nat) (branches : Fin count → Cloud m α)
      (next : ArrsF (Control m) SourceSiteId (Array α) β) (outcomes : Fin count → Except CloudError α)
      (roundtrip : Pure.RoundTrips codec)
      (children : ∀ index, Complete expected (current.child index) (branches index) (outcomes index) childBudget)
      (returned : ∀ index, expected.lookup (ReplayStore.returnKey (current.child index)) =
        some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode (outcomes index)⟩)
      (collected : (Array.ofFn outcomes).mapM id = .ok values)
      (present : expected.lookup (ReplayStore.valueKey current) =
        some ⟨⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩, .success (Json.arr (values.map codec.encode))⟩)
      (rest : Complete expected current.next (next.apply values) outcome budget) :
      Complete expected current (.impure info (.parallel codec count branches) next) outcome
        (childBudget + budget + 1)
  | parallelError {info : Option SourceSiteId} (codec : Codec α) (count : Nat) (branches : Fin count → Cloud m α)
      (next : ArrsF (Control m) SourceSiteId (Array α) β) (outcomes : Fin count → Except CloudError α)
      (roundtrip : Pure.RoundTrips codec)
      (children : ∀ index, Complete expected (current.child index) (branches index) (outcomes index) childBudget)
      (returned : ∀ index, expected.lookup (ReplayStore.returnKey (current.child index)) =
        some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode (outcomes index)⟩)
      (collected : (Array.ofFn outcomes).mapM id = .error error)
      (present : expected.lookup (ReplayStore.valueKey current) =
        some ⟨⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩, .failure error⟩) :
      Complete expected current (.impure info (.parallel codec count branches) next) (.error error) (childBudget + 1)
  | weaken (meaning : Complete expected current program outcome budget) (enough : budget ≤ larger) :
      Complete expected current program outcome larger

private theorem common_bound (count : Nat) (property : Fin count → Nat → Prop)
    (each : ∀ index, ∃ bound, property index bound)
    (increase : ∀ index small large, small ≤ large → property index small → property index large) :
    ∃ bound, ∀ index, property index bound := by
  induction count with
  | zero => exact ⟨0, fun i => Fin.elim0 i⟩
  | succ count ih =>
    obtain ⟨first, hf⟩ := each 0
    obtain ⟨rest, hr⟩ := ih (fun i => property i.succ) (fun i => each i.succ) (fun i => increase i.succ)
    refine ⟨max first rest, ?_⟩
    intro index
    exact Fin.cases (increase 0 _ _ (Nat.le_max_left _ _) hf)
      (fun i => increase i.succ _ _ (Nat.le_max_right _ _) (hr i)) index

theorem Complete.extend {m : Type → Type u} [Monad m] {α : Type}
    {before after current} {program : Cloud m α} {outcome budget}
    (complete : Complete before current program outcome budget) (extension : Extends before after) :
    Complete after current program outcome budget := by
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
  | weaken complete enough ih => exact .weaken ih enough

private theorem children_exist {m : Type → Type u} [Monad m] (current : LeanCloud.Location)
    (codec : Codec α) (count : Nat) (branches : Fin count → Cloud m α)
    (outcomes : Fin count → Except CloudError α)
    (each : ∀ index : Fin count, ∃ journal budget, Complete journal (current.child index) (branches index) (outcomes index) budget ∧
      Covers (After current index 0) journal) :
    ∃ journal budget,
      (∀ index : Fin count, Complete journal (current.child index) (branches index) (outcomes index) budget) ∧
      (∀ index : Fin count, journal.lookup (ReplayStore.returnKey (current.child index)) =
        some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode (outcomes index)⟩) ∧
      Covers (fun key => ∃ child, Under current child key) journal := by
  classical
  have full : ∀ index : Fin count, ∃ journal budget,
      Complete journal (current.child index) (branches index) (outcomes index) budget ∧
      journal.lookup (ReplayStore.returnKey (current.child index)) =
        some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode (outcomes index)⟩ ∧
      Covers (Under current index) journal := by
    intro index
    obtain ⟨journal, budget, complete, covered⟩ := each index
    let record : ReplayRecord := ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode (outcomes index)⟩
    obtain ⟨extension, coverage⟩ := covered.add_return (start := 0) record
    exact ⟨_, budget, complete.extend extension, by simp [LeanCloud.Location.child, record], coverage⟩
  let journals := fun index => Classical.choose (full index)
  let budgets := fun index => Classical.choose (Classical.choose_spec (full index))
  have evidence := fun index => Classical.choose_spec (Classical.choose_spec (full index))
  obtain ⟨merged, extension, coverage⟩ := merge_family count journals (fun index => Under current index)
    (fun index => (evidence index).2.2)
    (fun i j different _ first second => Under.separate (by intro same; exact different (Fin.ext same)) first second)
  obtain ⟨budget, bounded⟩ := common_bound count
    (fun index budget => Complete merged (current.child index) (branches index) (outcomes index) budget)
    (fun index => ⟨budgets index, (evidence index).1.extend (extension index)⟩)
    (fun _ _ _ enough complete => .weaken complete enough)
  exact ⟨merged, budget, bounded,
    fun index => extension index _ _ (evidence index).2.1,
    fun entry member => let ⟨index, inside⟩ := coverage entry member; ⟨index, inside⟩⟩

/-- Every supported pure evaluation has a finite complete expected journal,
including every nested child and its return record. Location separation makes
this construction consistent without assuming any records already exist. -/
theorem complete_journal_exists {m : Type → Type u} [Monad m] {α : Type}
    {program : Cloud m α} {outcome} (evaluation : Pure.Evaluation program outcome)
    (parent : LeanCloud.Location) (branch command : Nat) :
    ∃ journal budget, Complete journal (parent.push (branch, command)) program outcome budget ∧
      Covers (After parent branch command) journal := by
  induction evaluation generalizing parent branch command with
  | pure value => exact ⟨[], 1, .pure value, by simp [Covers]⟩
  | fail error next => exact ⟨[], 1, .fail error next, by simp [Covers]⟩
  | delay next rest ih =>
    obtain ⟨journal, budget, complete, coverage⟩ := ih parent branch command
    exact ⟨journal, budget + 1, .delay next complete, coverage⟩
  | exec codec label body next roundtrip rest ih =>
    obtain ⟨journal, budget, complete, coverage⟩ := ih parent branch (command + 1)
    let record : ReplayRecord :=
      ⟨ReplayInterpreter.Internal.request codec (.exec label (fun _ => pure (body ()) : Unit → m _)),
        .success (codec.encode (body ()))⟩
    obtain ⟨_, extension, present, coverage⟩ := assemble parent branch command [] journal record (by simp [Covers]) coverage
    refine ⟨_, budget + 1, .exec codec label body next roundtrip present ?_, coverage⟩
    simpa only [Location.next_push] using complete.extend extension
  | parallelOk codec count branches next outcomes roundtrip children collected rest ihChildren ih =>
    rename_i valueType resultType values result sourceInfo
    obtain ⟨descendants, childBudget, childSpecs, returned, childRegion⟩ :=
      children_exist (parent.push (branch, command)) codec count branches outcomes
        (fun index => ihChildren index (parent.push (branch, command)) index 0)
    obtain ⟨journal, budget, complete, coverage⟩ := ih parent branch (command + 1)
    let record : ReplayRecord :=
      ⟨⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩, .success (Json.arr (values.map codec.encode))⟩
    obtain ⟨childExtension, extension, present, coverage⟩ :=
      assemble parent branch command descendants journal record childRegion coverage
    refine ⟨_, childBudget + budget + 1, .parallelOk codec count branches next outcomes roundtrip
      (fun index => (childSpecs index).extend childExtension)
      (fun index => childExtension _ _ (returned index)) collected present ?_, coverage⟩
    simpa only [Location.next_push] using complete.extend extension
  | parallelError codec count branches next outcomes roundtrip children collected ihChildren =>
    rename_i valueType resultType error sourceInfo
    obtain ⟨descendants, childBudget, childSpecs, returned, childRegion⟩ :=
      children_exist (parent.push (branch, command)) codec count branches outcomes
        (fun index => ihChildren index (parent.push (branch, command)) index 0)
    let record : ReplayRecord := ⟨⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩, .failure error⟩
    obtain ⟨extension, _, present, coverage⟩ :=
      assemble parent branch command descendants [] record childRegion (by simp [Covers])
    exact ⟨_, childBudget + 1, .parallelError codec count branches next outcomes roundtrip
      (fun index => (childSpecs index).extend extension)
      (fun index => extension _ _ (returned index)) collected present, coverage⟩

/-- The complete workflow specification also contains its final root result.
The caller supplies a pure program and its meaning, not a prebuilt journal. -/
theorem workflow_journal_exists {m : Type → Type u} [Monad m] {α : Type}
    {program : Cloud m α} {outcome} (evaluation : Pure.Evaluation program outcome) (encode : α → Json) :
    ∃ journal budget, Complete journal LeanCloud.Location.root program outcome budget ∧
      journal.lookup (ReplayStore.returnKey LeanCloud.Location.root) =
        some ⟨ReplayStore.returnRequest, Parallel.recorded encode outcome⟩ := by
  obtain ⟨journal, budget, complete, coverage⟩ := complete_journal_exists evaluation #[] 0 0
  let record : ReplayRecord := ⟨ReplayStore.returnRequest, Parallel.recorded encode outcome⟩
  obtain ⟨extension, _⟩ := coverage.add_return (start := 0) record
  exact ⟨_, budget, complete.extend extension, by simp [LeanCloud.Location.root, record]⟩

end LeanCloud.Proofs.Specification
