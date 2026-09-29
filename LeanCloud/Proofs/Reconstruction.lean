import LeanCloud.Proofs.ReconstructionStep

/-! Structural reconstruction of a pure program through recorded prefixes.
The target action retains its own specification; crashes in the prefix leave
the durable journal unchanged. -/

namespace LeanCloud.Proofs
open Lean LeanEff CrashModel ReplayRecovery ReplayInterpreter.Internal

/-- Reconstruction fuel depends on the original route, not on which durable
records a previous attempt managed to commit. The target has its own budget. -/
def TreeRoute.prefixSteps {tree current target node} : TreeRoute tree current target node → Nat
  | .terminal .. | .fork .. => 0
  | .delay rest | .next rest | .child _ rest => rest.prefixSteps + 1

/-- A single finite budget covers every reconstruction path, independently of
delivery order and the journal left by previous attempts. -/
theorem TreeRoute.fuel_bound {tree current target node} (route : TreeRoute tree current target node) :
    route.prefixSteps + 1 ≤ sizeOf tree := by
  induction route with
  | terminal => simp [prefixSteps]
  | fork => simp [prefixSteps]; omega
  | delay rest ih => simp only [prefixSteps]; simp_wf; omega
  | next rest ih => simp only [prefixSteps]; simp_wf; omega
  | @child children result next current target node index rest ih =>
    have smaller := List.sizeOf_lt_of_mem (List.getElem_mem index.isLt)
    simp only [prefixSteps]
    simp_wf
    omega

theorem TreeRoute.reconstruct {tree current target node}
    (route : TreeRoute tree current target node)
    (journal : Journal) (blobs : BlobStorage Unit (M Journal))
    (post : StepResult → Journal → Prop) (stopped : Journal → Prop) (safe : stopped journal)
    (bound : Nat)
    (handle : ∀ program : Cloud (M Journal) Json, PureProgram program → Expansion program node →
      ∀ fuel, bound ≤ fuel → Spec (· = journal) (walk db blobs fuel program target target) post stopped)
    {program : Cloud (M Journal) Json} (expansion : Expansion program tree) (supported : PureProgram program)
    (nonempty : 0 < current.size) (ready : route.Ready journal) :
    ∀ fuel, route.prefixSteps + bound ≤ fuel → Spec (· = journal) (walk db blobs fuel program current target) post stopped := by
  induction route generalizing program with
  | terminal => simpa only [prefixSteps, Nat.zero_add] using handle program supported expansion
  | fork => simpa only [prefixSteps, Nat.zero_add] using handle program supported expansion
  | delay rest ih =>
    cases expansion with
    | delay expanded =>
      have enough := ih handle expanded (supported.2.apply ()) nonempty ready
      intro fuel large
      simp only [prefixSteps] at large
      cases fuel with
      | zero => omega
      | succ fuel => exact enough fuel (by omega)
  | @next children result tree current target node rest ih =>
    cases expansion with
    | @success α codec count branches continuation outcomes values trees next evaluated collected childrenExpansion expanded =>
      obtain ⟨view, remaining⟩ := ready
      have enough := ih handle expanded (supported.2.apply values) (by simpa using nonempty) remaining
      have size : values.size = count := (collect_outcomes_size _ _ collected).trans evaluated.size
      intro fuel large
      simp only [prefixSteps] at large
      cases fuel with
      | zero => omega
      | succ fuel =>
        exact walk_after_join journal blobs fuel codec supported.1.1 count branches continuation values
          current target size (rest.next_ne nonempty) view post stopped safe (enough fuel (by omega))
  | @child children result next current target node index rest ih =>
    cases expansion with
    | @success α codec count branches continuation outcomes values trees next evaluated collected childrenExpansion expanded
    | @failure α codec count branches continuation outcomes error trees evaluated collected childrenExpansion =>
      obtain ⟨slots, view, size, remaining⟩ := ready
      let selected : Fin count := ⟨index.val, by rw [← childrenExpansion.size]; exact index.isLt⟩
      have branch := childrenExpansion.at selected index.isLt
      have enough := ih handle branch ((supported.1.2 selected).map codec.encode) (by simp) remaining
      obtain ⟨enters, chosen⟩ := rest.child_path
      intro fuel large
      simp only [prefixSteps] at large
      cases fuel with
      | zero => omega
      | succ fuel =>
        exact walk_into_child journal blobs fuel codec count branches continuation current target slots
          (size.trans childrenExpansion.size) enters selected chosen view post stopped safe (enough fuel (by omega))

/-- Lift reconstruction through the actual worker entry point. Live deliveries
have an open immediate parent; obsolete deliveries use the separate completed-
parent lemma. The root-location guard follows from the program's route. -/
theorem TreeRoute.step_reconstruct {tree target node}
    (route : TreeRoute tree Location.root target node)
    (journal : Journal) (blobs : BlobStorage Unit (M Journal))
    (post : StepResult → Journal → Prop) (stopped : Journal → Prop) (safe : stopped journal)
    (bound : Nat)
    (handle : ∀ program : Cloud (M Journal) Json, PureProgram program → Expansion program node →
      ∀ fuel, bound ≤ fuel → Spec (· = journal) (walk db blobs fuel program target target) post stopped)
    {program : Cloud (M Journal) Json} (expansion : Expansion program tree) (supported : PureProgram program)
    (ready : route.Ready journal)
    (parents : ∀ parent index, target.parent? = some (parent, index) →
      ∃ slots : Array (Option Exit), JournalDb.get JournalAdapter.raw parent.key journal =
        (some (toJson (Result.suspended slots)), journal)) :
    ∀ fuel, route.prefixSteps + bound ≤ fuel → Spec (· = journal) (step db blobs fuel program target) post stopped := by
  have enough := route.reconstruct journal blobs post stopped safe bound handle expansion supported
    (by simp [Location.root]) ready
  intro fuel large
  rw [step]
  simp only [route.root_guard, Bool.false_eq_true, ↓reduceIte]
  cases linked : target.parent? with
  | none => exact enough fuel large
  | some pair =>
    obtain ⟨parent, index⟩ := pair
    obtain ⟨slots, view⟩ := parents parent index linked
    apply load_then journal parent (some (.suspended slots)) view _ post stopped safe
    exact enough fuel large

end LeanCloud.Proofs
