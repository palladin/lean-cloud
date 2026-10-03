import LeanCloud.Proofs.BackendFuelInitial

namespace LeanCloud.Backend.Proofs.Fuel
open Lean LeanEff LeanCloud.Proofs Execution Iteration

def entrypoints [Codec α] (count : Nat) (budget : Nat → Nat) (source : Cloud Replay.M Json) :=
  (Array.range count).map fun index => loop (α := α) (budget index + 1) source

def renameAction (mapping : Nat → Nat) : Action → Action
  | .commit id => .commit (mapping id)
  | .reply id => .reply (mapping id)
  | .crash worker => .crash worker
  | .restart worker => .restart worker

/-- A finite realization by the actual public worker loop. Every physical
action is retained, with a consistent injection of its issued request ids.
Only idle time and proof iteration boundaries become target stutters.
`Related` preserves the complete shared service state at every boundary. -/
inductive Realizes [Codec α] (trace : Iteration.Trace traversal source count) (budget : Nat → Nat) :
    Nat → (Nat → Nat) → (Nat → Nat) → Execution.State (Answer α) → Prop where
  | initial {mapping}
      (related : Related budget source mapping (trace.states 0)
        (Execution.initial Replay.initial (entrypoints (α := α) count budget source))) :
      Realizes trace budget 0 budget mapping (Execution.initial Replay.initial (entrypoints count budget source))
  | quiet {time remaining mapping target}
      (prior : Realizes trace budget time remaining mapping target)
      (idle : trace.events time = none) (same : trace.states (time + 1) = trace.states time) :
      Realizes trace budget (time + 1) remaining mapping target
  | physical {time remaining mapping target updated lastMap final action}
      (prior : Realizes trace budget time remaining mapping target)
      (event : trace.events time = some (.action action))
      (executed : Transition (entrypoints count budget source) (renameAction mapping action) target final)
      (related : Related updated source lastMap (trace.states (time + 1)) final) :
      Realizes trace budget (time + 1) updated lastMap final
  | iterate {time remaining mapping target updated lastMap index}
      (prior : Realizes trace budget time remaining mapping target)
      (event : trace.events time = some (.iterate index))
      (related : Related updated source lastMap (trace.states (time + 1)) target) :
      Realizes trace budget (time + 1) updated lastMap target

theorem Realizes.related [Codec α] {trace : Iteration.Trace traversal source count} {budget time remaining mapping target}
    (realized : Realizes (α := α) trace budget time remaining mapping target) :
    Related remaining source mapping (trace.states time) target := by
  induction realized with
  | initial related | physical _ _ _ related | iterate _ _ related => exact related
  | quiet _ idle same ih => rw [same]; exact ih

theorem finite_realization [Codec α] {source : Cloud Replay.M Json} {tree}
    (whole : Expansion source tree) (supported : PureProgram source)
    (comparable : ReplayRecovery.Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (traversal : Nat) (enoughTraversal : sizeOf tree ≤ traversal)
    (trace : Iteration.Trace traversal source count)
    (initialized : trace.states 0 = Execution.initial Replay.initial (Array.replicate count (Iteration.program traversal source)))
    (limit : Nat) (budget : Nat → Nat) (enough : ∀ index, index < count → traversal + limit ≤ budget index) :
    ∃ remaining mapping target, Realizes (α := α) trace budget limit remaining mapping target := by
  have linked time : Linked (trace.states time) := trace.linked (by rw [initialized]; exact initial_linked _ _) time
  obtain ⟨kept, _⟩ := Iteration.certified whole supported comparable sameExit traversal enoughTraversal trace initialized
  have stage (time : Nat) (bounded : time ≤ limit) :
      ∃ remaining mapping target, Realizes (α := α) trace budget time remaining mapping target ∧
        ∀ index, index < count → traversal + (limit - time) ≤ remaining index := by
    induction time with
    | zero =>
      obtain ⟨mapping, related⟩ := Related.initial (α := α) traversal source supported count budget
        (by intro index inside; have bound := enough index inside; omega)
      rw [← initialized] at related
      exact ⟨budget, mapping, _, .initial related, by simpa using enough⟩
    | succ time ih =>
      obtain ⟨remaining, mapping, target, prior, bound⟩ := ih (by omega)
      have related := prior.related
      have executed := trace.execution time
      cases event : trace.events time with
      | none =>
        simp only [event] at executed
        exact ⟨remaining, mapping, target, .quiet prior event executed,
          fun index inside => Nat.le_trans (by omega) (bound index inside)⟩
      | some action =>
        simp only [event] at executed
        have valid := kept time
        have callers := linked time
        generalize future : trace.states (time + 1) = final at executed ⊢
        have realizePhysical {updated lastMap finalTarget action}
            (chosen : trace.events time = some (.action action))
            (transition : Transition (entrypoints count budget source) (renameAction mapping action) target finalTarget)
            (same : Related updated source lastMap final finalTarget)
            (remainingBound : ∀ index, index < count → traversal + (limit - (time + 1)) ≤ updated index) :
            ∃ remaining mapping target, Realizes (α := α) trace budget (time + 1) remaining mapping target ∧
              ∀ index, index < count → traversal + (limit - (time + 1)) ≤ remaining index := by
          refine ⟨updated, lastMap, finalTarget, .physical prior chosen transition ?_, remainingBound⟩
          rw [future]; exact same
        cases executed with
        | action physical =>
          cases physical with
          | commit issued lawful =>
            obtain ⟨next, committed, same⟩ := related.commit callers issued lawful (entrypoints count budget source)
            exact realizePhysical event committed same (fun index inside => Nat.le_trans (by omega) (bound index inside))
          | reply delivered =>
            obtain ⟨next, lastMap, replied, same⟩ := related.reply callers _ (entrypoints count budget source) delivered
            exact realizePhysical event replied same (fun index inside => Nat.le_trans (by omega) (bound index inside))
          | crash crashed =>
            obtain ⟨next, crashed, same⟩ := related.crash _ (entrypoints count budget source) crashed
            exact realizePhysical event crashed same (fun index inside => Nat.le_trans (by omega) (bound index inside))
          | @restart index before final restarted =>
            have initialBound : traversal ≤ budget index + 1 := by
              by_cases inside : index < count
              · have enough := enough index inside; omega
              · simp only [Execution.step] at restarted
                split at restarted <;> try contradiction
                simp [inside] at restarted
            obtain ⟨next, lastMap, restarted, same⟩ := related.restart callers traversal supported count budget index initialBound restarted
            apply realizePhysical event restarted same
            intro other inside
            by_cases equal : other = index
            · subst other; simp only [extend, ↓reduceIte]; have enough := enough index inside; omega
            · simp only [extend, equal, ↓reduceIte]; have old := bound other inside; omega
        | @iterate before index attempt value code held found unfinished =>
          have codeEq := (Array.mem_replicate.mp (Array.mem_of_getElem? found)).2
          subst code
          have inside : index < count := by simpa using (Array.getElem?_eq_some_iff.mp found).choose
          obtain ⟨actual, handle, valueEq, outcome, outcomeEq, handleEq, _⟩ :=
            valid.returned Worker.Grows.refl index _ value held rfl
          subst actual
          subst handle
          subst value
          cases outcome with
          | some value => cases unfinished
          | none =>
            have positive : 0 < remaining index := by have old := bound index inside; omega
            let left := remaining index - 1
            have current : remaining index = left + 1 := by dsimp [left]; omega
            have enoughStep : traversal ≤ left + 1 := by have old := bound index inside; omega
            obtain ⟨lastMap, same⟩ := related.iterate callers traversal supported index attempt left held current enoughStep
            refine ⟨extend remaining index left, lastMap, target, .iterate prior event ?_, ?_⟩
            · rw [future]; exact same
            · intro other insideOther
              by_cases equal : other = index
              · subst other; simp only [extend, ↓reduceIte]; have old := bound index inside; omega
              · simp only [extend, equal, ↓reduceIte]; have old := bound other insideOther; omega
  obtain ⟨remaining, mapping, target, realized, _⟩ := stage limit (Nat.le_refl _)
  exact ⟨remaining, mapping, target, realized⟩

end LeanCloud.Backend.Proofs.Fuel
