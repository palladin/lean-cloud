import LeanCloud.Proofs.SharedLoop

/-! Observations of actual serialized worker attempts. Each attempt starts with
a fresh local handle, retains durable state and the remaining fault script, and
allows the environment to advance time. No successful completion is assumed. -/

namespace LeanCloud.Proofs.SharedRecovery
open Lean CrashModel CrashRecovery JournalAdapter

/-- Time passes without resetting the journal, messages, or fault script. -/
def advanceState (elapsed : Nat) (state : State Durable) : State Durable :=
  { state with durable := advance elapsed state.durable }

/-- One observation is the actual loop body, with a fresh worker after either
a normal return or a crash. The trace records no alternate interpreter. -/
structure Trace (source : Cloud (CrashModel.M Journal) Json) (blobs : BlobStorage Worker M) where
  states : Nat → State Durable
  elapsed : Nat → Nat
  fuel : Nat → Nat
  follows : ∀ n, states (n + 1) =
    (((iteration workerDb blobs queue (fuel n) (journalMap.program source)).run ⟨(), none⟩).run
      (advanceState (elapsed n) (states n))).2

def Trace.result {source blobs} (trace : Trace source blobs) (n : Nat) :=
  (((iteration workerDb blobs queue (trace.fuel n) (journalMap.program source)).run ⟨(), none⟩).run
    (advanceState (trace.elapsed n) (trace.states n))).1

theorem Trace.execution {source blobs} (trace : Trace source blobs) (n : Nat) :
    (((iteration workerDb blobs queue (trace.fuel n) (journalMap.program source)).run ⟨(), none⟩).run
      (advanceState (trace.elapsed n) (trace.states n))) = (trace.result n, trace.states (n + 1)) :=
  Prod.ext rfl (trace.follows n).symm

/-- A finite set of immutable fields cannot keep changing forever. A field
may remain absent forever; stabilization does not assume that all work finishes. -/
private theorem finite_journal_stable (journals : Nat → Journal) (keys : List String)
    (grows : ∀ start stop, start ≤ stop → Extends (journals start) (journals stop))
    (supported : ∀ n key value, journals n key = some value → key ∈ keys) :
    ∃ cut, ∀ n, cut ≤ n → journals n = journals cut := by
  classical
  have absent (key : String) (missing : ¬ ∃ n value, journals n key = some value) (n : Nat) :
      journals n key = none := by
    cases recorded : journals n key with
    | none => rfl
    | some value => exact False.elim (missing ⟨n, value, recorded⟩)
  have fields (fields : List String) :
      ∃ cut, ∀ n, cut ≤ n → ∀ key ∈ fields, journals n key = journals cut key := by
    induction fields with
    | nil => exact ⟨0, by simp⟩
    | cons key rest ih =>
      obtain ⟨tailCut, tailFixed⟩ := ih
      by_cases present : ∃ n value, journals n key = some value
      · obtain ⟨headCut, value, recorded⟩ := present
        refine ⟨max headCut tailCut, ?_⟩
        intro n later field member
        rcases List.mem_cons.mp member with rfl | member
        · exact (grows headCut n (by omega) field value recorded).trans
            (grows headCut (max headCut tailCut) (by omega) field value recorded).symm
        · exact (tailFixed n (by omega) field member).trans
            (tailFixed (max headCut tailCut) (by omega) field member).symm
      · refine ⟨tailCut, ?_⟩
        intro n later field member
        rcases List.mem_cons.mp member with rfl | member
        · rw [absent field present n, absent field present tailCut]
        · exact tailFixed n later field member
  obtain ⟨cut, stable⟩ := fields keys
  refine ⟨cut, ?_⟩
  intro n later
  funext key
  by_cases member : key ∈ keys
  · exact stable n later key member
  · have missing : ¬ ∃ n value, journals n key = some value := by
      rintro ⟨n, value, recorded⟩
      exact member (supported n key value recorded)
    rw [absent key missing n, absent key missing cut]

section
variable {source tree blobs} (trace : Trace source blobs)
    (expansion : Expansion source tree) (supported : PureProgram source)
    (comparable : ReplayRecovery.Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
include expansion supported comparable sameExit

/-- Each observed attempt retains validity, coverage, and committed journal records.
A crash consumes a fault; an ordinary return is unfinished or the program's outcome. -/
theorem Trace.round
    (n : Nat) (enough : sizeOf tree ≤ trace.fuel n)
    (valid : Valid tree (trace.states n).durable) (covered : Covered tree (trace.states n).durable) :
    (trace.states (n + 1)).faults.script.length ≤ (trace.states n).faults.script.length ∧
      (Valid tree (trace.states (n + 1)).durable ∧ Covered tree (trace.states (n + 1)).durable) ∧
      Extends (trace.states n).durable.1 (trace.states (n + 1)).durable.1 ∧
      match trace.result n with
      | .error _ => (trace.states (n + 1)).faults.script.length < (trace.states n).faults.script.length
      | .ok returned => ∃ completed, returned = (.ok completed, (⟨(), none⟩ : Worker)) ∧
          ∀ outcome, completed = some outcome → outcome = tree.exit := by
  have checked := iteration_covered expansion supported comparable sameExit blobs
    ⟨(), none⟩ (trace.fuel n) enough (trace.states n).durable.1 (advanceState (trace.elapsed n) (trace.states n))
    ⟨Extends.refl _, valid_advance valid _, covered.advance _⟩
  rw [trace.execution n] at checked
  refine ⟨checked.1, ?_⟩
  cases observed : trace.result n with
  | error crash =>
    rw [observed] at checked
    exact ⟨checked.2.1.2, checked.2.1.1, checked.2.2⟩
  | ok returned =>
    rw [observed] at checked
    obtain ⟨completed, same, kept, correct⟩ := checked.2
    exact ⟨kept.2, kept.1, completed, same, correct⟩

/-- Coverage is now global: any number of attempts and crashes retains every
unfinished workflow obligation, with explicit time advancement between attempts. -/
theorem Trace.invariants
    (enough : ∀ n, sizeOf tree ≤ trace.fuel n)
    (valid : Valid tree (trace.states 0).durable) (covered : Covered tree (trace.states 0).durable) (n : Nat) :
    Valid tree (trace.states n).durable ∧ Covered tree (trace.states n).durable := by
  induction n with
  | zero => exact ⟨valid, covered⟩
  | succ n ih =>
    exact (trace.round expansion supported comparable sameExit n (enough n) ih.1 ih.2).2.1

theorem Trace.journal_grows
    (enough : ∀ n, sizeOf tree ≤ trace.fuel n)
    (valid : Valid tree (trace.states 0).durable) (covered : Covered tree (trace.states 0).durable)
    (start stop : Nat) (later : start ≤ stop) :
    Extends (trace.states start).durable.1 (trace.states stop).durable.1 := by
  have grows n : Extends (trace.states n).durable.1 (trace.states (n + 1)).durable.1 := by
    have kept := trace.invariants expansion supported comparable sameExit enough valid covered n
    exact (trace.round expansion supported comparable sameExit n (enough n) kept.1 kept.2).2.2.1
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le later
  induction offset with
  | zero => exact Extends.refl _
  | succ offset ih => exact (ih (by omega)).trans (grows (start + offset))

/-- Every actual trace eventually has a fixed journal, since the pure program
has finitely many possible records and attempts never remove a committed one.
The fixed journal need not yet contain the workflow's final result. -/
theorem Trace.journal_stable
    (enough : ∀ n, sizeOf tree ≤ trace.fuel n)
    (valid : Valid tree (trace.states 0).durable) (covered : Covered tree (trace.states 0).durable) :
    ∃ cut, ∀ n, cut ≤ n → (trace.states n).durable.1 = (trace.states cut).durable.1 := by
  apply finite_journal_stable (fun n => (trace.states n).durable.1) ((tree.records Location.root).map Prod.fst)
    (trace.journal_grows expansion supported comparable sameExit enough valid covered)
  intro n key value recorded
  have bound := (trace.invariants expansion supported comparable sameExit enough valid covered n).1.1
  have member := (tree.journal_read_iff Location.root (by simp [Location.root]) key value).mp (bound key value recorded)
  exact List.mem_map.mpr ⟨(key, value), member, rfl⟩

/-- The actual finite fault script yields a suffix of successful attempts.
Those attempts may still return unfinished; this does not assume workflow
termination, fair delivery, or automatic lease expiry. -/
theorem Trace.after_last_crash
    (enough : ∀ n, sizeOf tree ≤ trace.fuel n)
    (valid : Valid tree (trace.states 0).durable) (covered : Covered tree (trace.states 0).durable) :
    ∃ cut, ∀ n, cut ≤ n → ∃ completed,
      trace.result n = .ok (.ok completed, (⟨(), none⟩ : Worker)) ∧
      ∀ outcome, completed = some outcome → outcome = tree.exit := by
  classical
  have checked n := trace.round expansion supported comparable sameExit n (enough n)
    (trace.invariants expansion supported comparable sameExit enough valid covered n).1
    (trace.invariants expansion supported comparable sameExit enough valid covered n).2
  have monotone (start stop : Nat) (later : start ≤ stop) :
      (trace.states stop).faults.script.length ≤ (trace.states start).faults.script.length := by
    obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le later
    induction offset with
    | zero => exact Nat.le_refl _
    | succ offset ih =>
      exact Nat.le_trans (checked (start + offset)).1 (ih (by omega))
  have suffix (start : Nat) : ∃ cut, start ≤ cut ∧ ∀ n, cut ≤ n → ∃ completed,
      trace.result n = .ok (.ok completed, (⟨(), none⟩ : Worker)) ∧
        ∀ outcome, completed = some outcome → outcome = tree.exit := by
    generalize measure : (trace.states start).faults.script.length = count
    induction count using Nat.strongRecOn generalizing start with
    | ind count ih =>
      by_cases fails : ∃ n, start ≤ n ∧ ∃ crash, trace.result n = .error crash
      · obtain ⟨n, later, crash, returned⟩ := fails
        have decrease := (checked n).2.2.2
        rw [returned] at decrease
        have bounded := monotone start n later
        obtain ⟨cut, after, finished⟩ := ih _ (by omega) (n + 1) rfl
        exact ⟨cut, by omega, finished⟩
      · refine ⟨start, Nat.le_refl _, ?_⟩
        intro n later
        have observed := (checked n).2.2.2
        cases returned : trace.result n with
        | error crash => exact False.elim (fails ⟨n, later, crash, returned⟩)
        | ok value =>
          rw [returned] at observed
          obtain ⟨completed, same, correct⟩ := observed
          exact ⟨completed, congrArg Except.ok same, correct⟩
  obtain ⟨cut, _, finished⟩ := suffix 0
  exact ⟨cut, finished⟩

end

end LeanCloud.Proofs.SharedRecovery
