import LeanCloud.Proofs.WorkerRecovery
import LeanCloud.Proofs.ReplayCursor

namespace LeanCloud.Proofs.RecoveryMeaning
open Lean LeanEff ReplayFaults ReplayModel ReplayInterpreter JournalRegion

/-- The existing pure specification with an explicit bound on a path through
its finite evaluation. This bound includes the paths into parallel children. -/
inductive Meaning (expected : Journal) :
    {α : Type} → Location → Cloud WorkerM α → Except CloudError α → Nat → Prop where
  | pure {info} (value : α) : Meaning expected current (EffF.pure info value) (.ok value) 1
  | fail {info} (error : CloudError) (next : ArrsF (Control WorkerM) SourceSiteId α β) :
      Meaning expected current (.impure info (.fail error) next) (.error error) 1
  | delay {info} (next : ArrsF (Control WorkerM) SourceSiteId Unit α)
      (rest : Meaning expected current (next.apply ()) outcome budget) :
      Meaning expected current (.impure info .delay next) outcome (budget + 1)
  | exec {info} (codec : Codec α) (label : String) (body : Unit → α)
      (next : ArrsF (Control WorkerM) SourceSiteId α β)
      (roundtrip : codec.decode (codec.encode (body ())) = .ok (body ()))
      (present : expected.lookup (ReplayStore.valueKey current) =
        some ⟨Internal.request codec (.exec label (fun _ => pure (body ()) : Unit → WorkerM α)),
          .success (codec.encode (body ()))⟩)
      (rest : Meaning expected current.next (next.apply (body ())) outcome budget) :
      Meaning expected current (.impure info (.command codec (.exec label (fun _ => pure (body ())))) next)
        outcome (budget + 1)
  | parallelOk {info} (codec : Codec α) (count : Nat) (branches : Fin count → Cloud WorkerM α)
      (next : ArrsF (Control WorkerM) SourceSiteId (Array α) β) (outcomes : Fin count → Except CloudError α)
      (roundtrip : Pure.RoundTrips codec)
      (children : ∀ index, Meaning expected (current.child index) (branches index) (outcomes index) childBudget)
      (returned : ∀ index, expected.lookup (ReplayStore.returnKey (current.child index)) =
        some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode (outcomes index)⟩)
      (collected : (Array.ofFn outcomes).mapM id = .ok values)
      (present : expected.lookup (ReplayStore.valueKey current) =
        some ⟨⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩, .success (Json.arr (values.map codec.encode))⟩)
      (rest : Meaning expected current.next (next.apply values) outcome budget) :
      Meaning expected current (.impure info (.parallel codec count branches) next) outcome
        (childBudget + budget + 1)
  | parallelError {info} (codec : Codec α) (count : Nat) (branches : Fin count → Cloud WorkerM α)
      (next : ArrsF (Control WorkerM) SourceSiteId (Array α) β) (outcomes : Fin count → Except CloudError α)
      (roundtrip : Pure.RoundTrips codec)
      (children : ∀ index, Meaning expected (current.child index) (branches index) (outcomes index) childBudget)
      (returned : ∀ index, expected.lookup (ReplayStore.returnKey (current.child index)) =
        some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode (outcomes index)⟩)
      (collected : (Array.ofFn outcomes).mapM id = .error error)
      (present : expected.lookup (ReplayStore.valueKey current) =
        some ⟨⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩, .failure error⟩) :
      Meaning expected current (.impure info (.parallel codec count branches) next) (.error error) (childBudget + 1)
  | weaken (meaning : Meaning expected current program outcome budget) (enough : budget ≤ larger) :
      Meaning expected current program outcome larger

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

/-- Adding a bound introduces no new assumption on the original program. -/
theorem of_complete {expected current} {program : Cloud WorkerM α} {outcome}
    (complete : Specification.Complete expected current program outcome) :
    ∃ bound, Meaning expected current program outcome bound := by
  induction complete with
  | pure value => exact ⟨1, .pure value⟩
  | fail error next => exact ⟨1, .fail error next⟩
  | delay next rest ih =>
    obtain ⟨bound, proof⟩ := ih
    exact ⟨bound + 1, .delay next proof⟩
  | exec codec label body next roundtrip present rest ih =>
    obtain ⟨bound, proof⟩ := ih
    exact ⟨bound + 1, .exec codec label body next roundtrip present proof⟩
  | parallelOk codec count branches next outcomes roundtrip children returned collected present rest ihChildren ih =>
    obtain ⟨bound, proof⟩ := ih
    obtain ⟨childBound, childProof⟩ := common_bound count _ ihChildren (fun _ _ _ h p => .weaken p h)
    exact ⟨_, .parallelOk codec count branches next outcomes roundtrip childProof returned collected present proof⟩
  | parallelError codec count branches next outcomes roundtrip children returned collected present ihChildren =>
    obtain ⟨childBound, childProof⟩ := common_bound count _ ihChildren (fun _ _ _ h p => .weaken p h)
    exact ⟨_, .parallelError codec count branches next outcomes roundtrip childProof returned collected present⟩

end LeanCloud.Proofs.RecoveryMeaning
