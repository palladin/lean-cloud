import LeanCloud.Proofs.MainTheorems

/-! Checked applications of the public equivalence theorems to a workflow with captured
values, delayed pure execution, and nested parallel groups. -/

open Lean LeanEff LeanCloud LeanCloud.Proofs
namespace LeanCloudTests.ProofExamples

private theorem bool_roundtrip : Pure.RoundTrips (inferInstance : Codec Bool) := by
  intro value
  cases value <;> rfl

private def child [Monad m] (captured : Bool) : Cloud m Bool :=
  .impure none .delay (.one fun _ => .pure none captured)

private theorem child_meaning [Monad m] (captured : Bool) : Pure.Evaluation (child (m := m) captured) (.ok captured) :=
  .delay _ (by simpa [ArrsF.apply, ArrsF.viewL] using Pure.Evaluation.pure (info := none) (m := m) captured)

private def nested [Monad m] (captured : Bool) : Cloud m Bool :=
  .impure none (.parallel (inferInstance : Codec Bool) 2
    (fun index => child (if index.val = 0 then captured else !captured)))
    (.one fun values => .pure none values[0]!)

private theorem nested_meaning [Monad m] (captured : Bool) : Pure.Evaluation (nested (m := m) captured) (.ok captured) := by
  apply Pure.Evaluation.parallelOk (outcomes := fun index => .ok (if index.val = 0 then captured else !captured))
    (values := #[captured, !captured])
  · exact bool_roundtrip
  · intro index
    exact child_meaning _
  · simp [Array.ofFn_succ, Array.mapM_eq_mapM_toList, List.mapM_cons] <;> rfl
  · simpa [ArrsF.apply, ArrsF.viewL] using Pure.Evaluation.pure (info := none) (m := m) captured

private def source [Monad m] (_ : Unit) : Cloud m Json :=
  .impure none (.command (inferInstance : Codec Bool) (.exec "captured" fun _ => pure true))
    (.one fun captured =>
      .impure none (.parallel (inferInstance : Codec Bool) 2
        (fun index => if index.val = 0 then nested captured else child (!captured)))
        (.one fun values => .pure none (toJson values)))

private theorem source_meaning [Monad m] : Pure.Evaluation (source (m := m) ()) (.ok (toJson #[true, false])) := by
  unfold source
  apply Pure.Evaluation.exec (body := fun _ => true)
  · rfl
  · simp only [ArrsF.apply, ArrsF.viewL]
    apply Pure.Evaluation.parallelOk (outcomes := fun index => .ok (if index.val = 0 then true else false))
      (values := #[true, false])
    · exact bool_roundtrip
    · intro index
      by_cases first : index.val = 0
      · simpa only [first, ite_true] using nested_meaning true
      · simpa only [first, ite_false, Bool.not_true] using child_meaning false
    · simp [Array.ofFn_succ, Array.mapM_eq_mapM_toList, List.mapM_cons] <;> rfl
    · simpa [ArrsF.apply, ArrsF.viewL] using Pure.Evaluation.pure (info := none) (m := m) (toJson #[true, false])

-- All three theorem applications use the original program and input, from empty storage.
example :
    ∃ sufficientFuel, ∀ fuel, sufficientFuel ≤ fuel →
      ((SequentialReplay.interpret ReplayModel.store ReplayModel.noBlobs fuel source ()).run []).1 =
        ((DirectInterpreter.interpret ReplayModel.noBlobs source ()).run []).1 :=
  sequential_replay_matches_direct source () ⟨_, source_meaning⟩ (fun _ => rfl)

example :
    ∃ sufficientFuel, ∀ fuel, sufficientFuel ≤ fuel →
      ((ParallelReplay.interpret fuel source ()).run []).1 =
        ((DirectInterpreter.interpret ReplayModel.noBlobs source ()).run []).1 :=
  parallel_replay_matches_direct source () ⟨_, source_meaning⟩ (fun _ => rfl)

-- Faults may occur in any branch, before or after any journal operation.
example (faults : ReplayFaults.Plan) :
    ∃ sufficientFuel, ∀ fuel, sufficientFuel ≤ fuel →
      let direct := ((DirectInterpreter.interpret ReplayFaults.noBlobs source ()).run.run ⟨[], {}⟩).1
      let replay := ((RestartingParallelReplay.interpret fuel source ()).run
        (ReplayFaults.Saved.initial faults)).1
      match direct with
      | .ok expected => replay = expected
      | .error _ => False := by
  obtain ⟨bound, agrees⟩ := restarting_parallel_replay_matches_direct source () ⟨_, source_meaning⟩ (fun _ => rfl) faults
  refine ⟨bound, fun fuel enough => ?_⟩
  have correct := agrees fuel enough
  cases direct : ((DirectInterpreter.interpret ReplayFaults.noBlobs source ()).run.run ⟨[], {}⟩).1 with
  | ok expected => simpa only [direct] using correct
  | error side => simp only [direct] at correct

end LeanCloudTests.ProofExamples
