import LeanCloud.Proofs.RecoveryReplay

namespace LeanCloud.Proofs.RecoveryStep
open Lean LeanEff ReplayFaults ReplayModel ReplayInterpreter JournalMerge JournalRegion WorkerRecovery
open RecoveryMeaning RecoveryCursor

variable [rootCodec : Codec α] (source : Cloud WorkerM α)

/-- The actual step entry point is safe from any surviving, consistent prefix. -/
theorem step_safe {expected base branch budget fuel}
    (ready : Ready source expected budget base branch) (enough : budget ≤ fuel) :
    Attempt (Valid expected base branch) (ProgressValid source expected budget branch)
      (ReplayInterpreter.step ReplayFaults.store ReplayFaults.noBlobs fuel (fun _ : Unit => source) () ⟨0, branch⟩) := by
  obtain ⟨β, encode, program, result, current, cost, remaining, same, bounded, cursor, meaning, known⟩ := ready
  have route := (cursor.route source).1
  have nonempty : 0 < current.size := Nat.lt_of_lt_of_le (by decide) route.depth
  have first : current[0]!.1 = 0 := by simpa [LeanCloud.Location.root] using (route.branch_at 0 (by decide)).symm
  have valid : (!branch.isEmpty && branch[0]!.1 == 0) = true := by
    simp [same, Array.isEmpty, Nat.ne_of_gt nonempty, Proofs.Location.branchStart_index _ 0 nonempty, first]
  simp only [ReplayInterpreter.step, valid, ↓reduceIte]
  apply (RecoveryReads.outcome expected branch _ known
    (fun _ (h : Valid expected base branch _) => ⟨h, h.2⟩)).bind
  intro found
  cases found with
  | some value =>
    apply Ensures.pure Progress.done
    intro journal ⟨valid, _, found⟩
    cases present : journal.lookup (ReplayStore.returnKey branch) with
    | none => simp [present] at found
    | some record =>
      have canonical := Option.some.inj ((valid.2 _ _ present).symm.trans known)
      subst record
      exact ⟨valid, _, present, known⟩
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    let point : ReplayTarget := ⟨branch, current⟩
    have atBoundary := ReplayCursor.boundary ReplayFaults.store ReplayFaults.noBlobs point same fuel
      rootCodec.encode source Location.root route (by simp)
    rw [← atBoundary]
    obtain ⟨spare, eq⟩ := Nat.exists_eq_add_of_le (show cost ≤ fuel by omega)
    rw [eq]
    apply RecoveryPrefix.transport source cursor point same (.refl _ nonempty) spare
      (fun _ h => h.1) (fun _ h => h.1.1.extends)
    rw [ReplayCursor.at_target]
    exact (replay_safe source meaning encode base branch cost budget spare same bounded (by omega) known).consequence
      (fun _ h => ⟨h.1, cursor.extend source h.1.1.extends⟩) (fun _ _ h => h)

/-- Worker replies include the canonical durable outcome, or a valid suspension. -/
def ReportValid (expected : Journal) (budget : Nat) (branch : Location) : ReplayFaults.Report → Journal → Prop
  | .done value, journal => journal.lookup (ReplayStore.returnKey branch) = some ⟨ReplayStore.returnRequest, value⟩ ∧
      expected.lookup (ReplayStore.returnKey branch) = some ⟨ReplayStore.returnRequest, value⟩
  | .fork location count, journal => ProgressValid source expected budget branch (.fork location count) journal

/-- The worker also reads its completed result inside the restart boundary. -/
theorem attempt_safe {expected base branch budget fuel}
    (ready : Ready source expected budget base branch) (enough : budget ≤ fuel) :
    Attempt (Valid expected base branch) (ReportValid source expected budget branch)
      (ReplayFaults.attempt fuel (fun _ : Unit => source) () ⟨0, branch⟩) := by
  unfold ReplayFaults.attempt
  apply (step_safe source ready enough).bind
  intro progress
  cases progress with
  | fork location count => exact Ensures.pure (ReplayFaults.Report.fork location count) (fun _ h => ⟨h.1, h.2⟩)
  | done =>
    obtain ⟨value, known⟩ := ready.known
    apply (RecoveryReads.outcome expected branch value known
      (fun j (h : Valid expected base branch j ∧ ProgressValid source expected budget branch .done j) => ⟨h.1, h.1.2⟩)).bind
    intro found saved ⟨valid, ⟨_, returned⟩, got⟩
    obtain ⟨actual, present, canonical⟩ := returned
    have foundEq : found = some actual := by simpa only [present, Option.map_some] using got
    simp only [foundEq]
    exact ⟨valid, Nat.le_refl _, present, canonical⟩

/-- Retrying the full interpreter step consumes finite faults, retains every
committed record, and returns a correct reply with fresh, owned writes. -/
theorem worker_recovers {expected base branch budget fuel retries}
    (ready : Ready source expected budget base branch) (consistent : Extends base expected)
    (faults : Faults) (enoughFuel : budget ≤ fuel) (enoughRetries : faults.remaining.length < retries) :
    let (result, finished) := (worker retries fuel (fun _ : Unit => source) () ⟨0, branch⟩).run ⟨base, faults⟩
    Writes (Owns branch) base finished.durable ∧ Extends finished.durable expected ∧
      finished.faults.remaining.length ≤ faults.remaining.length ∧
      ∃ reply, result = .ok reply ∧ ReportValid source expected budget branch reply finished.durable := by
  have recovered := (attempt_safe source ready enoughFuel).restarts retries ⟨base, faults⟩ ⟨.refl _ _, consistent⟩ enoughRetries
  exact ⟨recovered.1.1, recovered.1.2, recovered.2⟩

end LeanCloud.Proofs.RecoveryStep
