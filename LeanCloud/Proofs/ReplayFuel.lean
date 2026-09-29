import LeanCloud.Proofs.Reconstruction
import LeanCloud.Proofs.TreeActivation

/-! Traversal fuel is observationally irrelevant above the reconstruction
bound. Equality includes the crash result, committed journal, and fault script,
so a finite trace can be replayed with the public loop's decreasing budget. -/

namespace LeanCloud.Proofs.ReplayRecovery
open Lean LeanEff CrashModel CrashRecovery JournalAdapter ReplayInterpreter.Internal

/-- Exact equality for every fault script at this durable journal. -/
def SameAt (journal : Journal) (first second : Worker α) : Prop :=
  ∀ start : State Journal, start.durable = journal → (call first).run start = (call second).run start

theorem SameAt.refl (journal : Journal) (action : Worker α) : SameAt journal action action := fun _ _ => rfl

/-- A common read prefix either crashes identically or enters equivalent
continuations with the same committed state and remaining fault script. -/
theorem load_same {journal : Journal} (location : Location) (record : Option Result)
    (view : JournalDb.get raw location.key journal = (record.map toJson, journal))
    (first second : Option Result → Worker α) (rest : SameAt journal (first record) (second record)) :
    SameAt journal (load db location >>= first) (load db location >>= second) := by
  intro start same
  have observed := load_reads location journal record view start same
  rw [call_bind, call_bind, run_bind, run_bind]
  generalize executed : (call (load db location)).run start = loaded at *
  obtain ⟨outcome, current⟩ := loaded
  cases outcome with
  | error crash => rfl
  | ok value =>
    obtain ⟨rfl, unchanged⟩ := observed.2
    exact rest current unchanged

private theorem target_fuel_eq {m : Type → Type} [Monad m]
    (backend : Db σ m) (blobs : BlobStorage σ m)
    {program : Cloud m Json} {node} (expansion : Expansion program node)
    (noDelay : ∀ rest, node ≠ .delay rest) (current : Location) (first second : Nat) :
    walk backend blobs (first + 1) program current current =
      walk backend blobs (second + 1) program current current := by
  cases expansion with
  | pure | fail => simp only [walk, beq_self_eq_true, ↓reduceIte]
  | delay rest => exact False.elim (noDelay _ rfl)
  | success | failure =>
    simp only [walk, beq_self_eq_true, Bool.true_and, ↓reduceIte]

private theorem join_same (journal : Journal) (blobs : BlobStorage Unit (M Journal)) (first second : Nat)
    (codec : Codec α) (law : CodecLaw codec) (count : Nat) (branches : Fin count → Cloud (M Journal) α)
    (continuation : ArrsF (Control (M Journal)) (Array α) Json) (values : Array α)
    (current target : Location) (size : values.size = count) (different : current ≠ target)
    (view : JournalDb.get raw current.key journal =
      (some (toJson (Result.completed (.success (.arr (values.map codec.encode))))), journal))
    (rest : SameAt journal
      (walk db blobs first (ArrsF.apply continuation values) current.next target)
      (walk db blobs second (ArrsF.apply continuation values) current.next target)) :
    SameAt journal
      (walk db blobs (first + 1) (.impure (.parallel codec count branches) continuation) current target)
      (walk db blobs (second + 1) (.impure (.parallel codec count branches) continuation) current target) := by
  rw [walk, walk]
  apply load_same current (some (.completed (.success (.arr (values.map codec.encode))))) view
  simpa only [beq_eq_false_iff_ne.mpr different, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    ← size, ReplayModel.decode_group_encoded codec law values, pure_bind] using rest

private theorem child_same (journal : Journal) (blobs : BlobStorage Unit (M Journal)) (first second : Nat)
    (codec : Codec α) (count : Nat) (branches : Fin count → Cloud (M Journal) α)
    (continuation : ArrsF (Control (M Journal)) (Array α) Json)
    (current target : Location) (slots : Array (Option Exit)) (size : slots.size = count)
    (enters : current.entersChild target = true) (index : Fin count)
    (selected : target[current.size]!.1 = index.val)
    (view : JournalDb.get raw current.key journal = (some (toJson (Result.suspended slots)), journal))
    (rest : SameAt journal
      (walk db blobs first (codec.encode <$> branches index) (current.child index.val) target)
      (walk db blobs second (codec.encode <$> branches index) (current.child index.val) target)) :
    SameAt journal
      (walk db blobs (first + 1) (.impure (.parallel codec count branches) continuation) current target)
      (walk db blobs (second + 1) (.impure (.parallel codec count branches) continuation) current target) := by
  have different : current ≠ target := by
    intro same
    subst target
    simp [Location.entersChild] at enters
  rw [walk, walk]
  apply load_same current (some (.suspended slots)) view
  simpa only [beq_eq_false_iff_ne.mpr different, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    size, bne_self_eq_false, enters, Bool.not_true, selected, index.isLt, ↓reduceDIte] using rest

end ReplayRecovery
open Lean LeanEff CrashModel JournalAdapter ReplayRecovery ReplayInterpreter.Internal

/-- Enough reconstruction fuel gives exactly the same execution, including
crashes at any read or target-operation boundary. -/
theorem TreeRoute.walk_fuel_same {tree current target node}
    (route : TreeRoute tree current target node) (journal : Journal) (blobs : BlobStorage Unit (M Journal))
    {program : Cloud (M Journal) Json} (expansion : Expansion program tree) (supported : PureProgram program)
    (nonempty : 0 < current.size) (ready : route.Ready journal) :
    ∀ first second, route.prefixSteps + 1 ≤ first → route.prefixSteps + 1 ≤ second →
      SameAt journal (walk db blobs first program current target) (walk db blobs second program current target) := by
  induction route generalizing program with
  | terminal outcome current
  | fork children result next current =>
    intro first second enoughFirst enoughSecond
    obtain ⟨first, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : first ≠ 0)
    obtain ⟨second, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : second ≠ 0)
    rw [target_fuel_eq db blobs expansion (by intro rest; simp) current first second]
    exact SameAt.refl _ _
  | delay rest ih =>
    cases expansion with
    | delay expanded =>
      intro first second enoughFirst enoughSecond
      simp only [TreeRoute.prefixSteps] at enoughFirst enoughSecond
      obtain ⟨first, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : first ≠ 0)
      obtain ⟨second, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : second ≠ 0)
      exact ih expanded (supported.2.apply ()) nonempty ready first second (by omega) (by omega)
  | @next children result tree current target node rest ih =>
    cases expansion with
    | @success α codec count branches continuation outcomes values trees next evaluated collected childrenExpansion expanded =>
      obtain ⟨view, remaining⟩ := ready
      have size : values.size = count := (collect_outcomes_size _ _ collected).trans evaluated.size
      intro first second enoughFirst enoughSecond
      simp only [TreeRoute.prefixSteps] at enoughFirst enoughSecond
      obtain ⟨first, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : first ≠ 0)
      obtain ⟨second, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : second ≠ 0)
      exact join_same journal blobs first second codec supported.1.1 count branches continuation values current target
        size (rest.next_ne nonempty) view
        (ih expanded (supported.2.apply values) (by simpa using nonempty) remaining first second (by omega) (by omega))
  | @child children result next current target node index rest ih =>
    cases expansion with
    | @success α codec count branches continuation outcomes values trees next evaluated collected childrenExpansion expanded
    | @failure α codec count branches continuation outcomes error trees evaluated collected childrenExpansion =>
      obtain ⟨slots, view, size, remaining⟩ := ready
      let selected : Fin count := ⟨index.val, by rw [← childrenExpansion.size]; exact index.isLt⟩
      have branch := childrenExpansion.at selected index.isLt
      obtain ⟨enters, chosen⟩ := rest.child_path
      intro first second enoughFirst enoughSecond
      simp only [TreeRoute.prefixSteps] at enoughFirst enoughSecond
      obtain ⟨first, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : first ≠ 0)
      obtain ⟨second, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : second ≠ 0)
      exact child_same journal blobs first second codec count branches continuation current target slots
        (size.trans childrenExpansion.size) enters selected chosen view
        (ih branch ((supported.1.2 selected).map codec.encode) (by simp) remaining first second (by omega) (by omega))

/-- The worker's parent check has a common read prefix. Live and obsolete
deliveries therefore have the same exact execution at every sufficient budget. -/
theorem TreeRoute.step_fuel_same {program : Cloud (M Journal) Json} {tree target node}
    (expansion : Expansion program tree) (supported : PureProgram program)
    (route : TreeRoute tree Location.root target node) (journal : Journal)
    (bounded : Extends journal (tree.journal Location.root))
    (causal : tree.Causal Location.root journal) (activated : route.Activated journal)
    (blobs : BlobStorage Unit (M Journal)) (first second : Nat)
    (enoughFirst : route.prefixSteps + 1 ≤ first) (enoughSecond : route.prefixSteps + 1 ≤ second) :
    SameAt journal (step db blobs first program target) (step db blobs second program target) := by
  simp only [step, route.root_guard, Bool.false_eq_true, ↓reduceIte]
  rcases route.delivery_ready expansion bounded causal activated with ⟨ready, parentOpen⟩ |
    ⟨parent, index, outcome, linked, recorded⟩
  · have same := route.walk_fuel_same journal blobs expansion supported (by simp [Location.root]) ready
      first second enoughFirst enoughSecond
    cases linked : target.parent? with
    | none => exact same
    | some pair =>
      obtain ⟨parent, index⟩ := pair
      obtain ⟨slots, view⟩ := parentOpen parent index linked
      exact load_same parent (some (.suspended slots)) view _ _ same
  · rw [linked]
    exact load_same parent (some (.completed outcome)) recorded _ _ (SameAt.refl _ _)

end LeanCloud.Proofs
