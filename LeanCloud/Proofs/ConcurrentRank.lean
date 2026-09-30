import LeanCloud.Proofs.ConcurrentNoLoss

/-! A finite progress measure once the journal is fixed. Returning to a
completed ancestor decreases the number of completed enclosing groups. Other
responses move forward in the original finite list of command locations.
This is proof data only; it imposes no execution order on the workers. -/

namespace LeanCloud.Proofs.ConcurrentJournal
open Lean Simulation SimulationBackend JournalAdapter JournalDb ReplayRecovery

private def prefixCount (closed : Location → Bool) (source : Location) (depth : Nat) : Nat :=
  ((List.range depth).filter fun i => closed (source.extract 0 i)).length

/-- Count completed strict prefixes, excluding the command itself. -/
def ancestors (closed : Location → Bool) (source : Location) : Nat :=
  prefixCount closed source source.size

private theorem prefixCount_succ (closed : Location → Bool) (source : Location) (depth : Nat) :
    prefixCount closed source (depth + 1) =
      prefixCount closed source depth + if closed (source.extract 0 depth) then 1 else 0 := by
  simp [prefixCount, List.range_succ, List.filter_append]
  split <;> simp_all

private theorem prefixCount_mono (closed : Location → Bool) (source : Location)
    {before after : Nat} (later : before ≤ after) :
    prefixCount closed source before ≤ prefixCount closed source after :=
  ((List.range_sublist.mpr later).filter _).length_le

private theorem ancestors_extract (closed : Location → Bool) (source : Location)
    (depth : Nat) (inside : depth ≤ source.size) :
    ancestors closed (source.extract 0 depth) = prefixCount closed source depth := by
  simp only [ancestors, prefixCount, Array.size_extract, Nat.sub_zero, Nat.min_eq_left inside]
  congr 1
  apply List.filter_congr
  intro i member
  have bound : i ≤ depth := Nat.le_of_lt (List.mem_range.mp member)
  simp [Array.extract_extract, Nat.min_eq_left bound]

theorem ancestors_child (closed : Location → Bool) (source : Location) (index : Nat) :
    ancestors closed (source.child index) = ancestors closed source + if closed source then 1 else 0 := by
  rw [ancestors, Location.size_child, prefixCount_succ]
  have prefixes : prefixCount closed (source.child index) source.size = ancestors closed source := by
    unfold prefixCount ancestors
    congr 1
    apply List.filter_congr
    intro i member
    have bound : i ≤ source.size := Nat.le_of_lt (List.mem_range.mp member)
    rw [Location.child, Array.extract_push_of_le bound]
  rw [prefixes]
  simp [Location.child, Array.extract_push_of_le (Nat.le_refl source.size)]

theorem ancestors_next (closed : Location → Bool) (source : Location) :
    ancestors closed source.next = ancestors closed source := by
  simp only [ancestors, Location.size_next, prefixCount]
  congr 1
  apply List.filter_congr
  intro i member
  have bound : i < source.size := List.mem_range.mp member
  obtain ⟨base, ⟨branch, command⟩, rfl⟩ := Array.exists_push_of_size_pos (by omega : 0 < source.size)
  rw [Location.next_push]
  have inside : i ≤ base.size := by simp only [Array.size_push] at bound; omega
  rw [Array.extract_push_of_le inside, Array.extract_push_of_le inside]

theorem ancestors_redirect {closed : Location → Bool} {source parent : Location}
    (enters : parent.entersChild source = true) (finished : closed parent = true) :
    ancestors closed parent < ancestors closed source := by
  have size := Location.entersChild_size enters
  have initial : source.extract 0 parent.size = parent := by
    have parts : parent.size < source.size ∧ parent = source.extract 0 parent.size := by
      simpa only [Location.entersChild, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using enters
    exact parts.2.symm
  have same := ancestors_extract closed source parent.size (Nat.le_of_lt size)
  rw [initial] at same
  have bound := prefixCount_mono closed source (show parent.size + 1 ≤ source.size by omega)
  rw [prefixCount_succ, initial, finished, ite_eq_left rfl, ← same] at bound
  exact Nat.lt_of_lt_of_le (by omega) bound

/-- The second coordinate decreases on ordinary children and continuations;
the first decreases on completed-ancestor wakeups. -/
def rank (tree : ExecutionTree) (closed : Location → Bool) (source : Location) : Nat × Nat :=
  let locations := (tree.nodes Location.root).map Prod.fst
  (ancestors closed source, locations.length - locations.idxOf source)

private theorem position_lt {tree : ExecutionTree} {source target : Location}
    (first : source ∈ (tree.nodes Location.root).map Prod.fst)
    (last : target ∈ (tree.nodes Location.root).map Prod.fst)
    (before : source.Earlier target) :
    ((tree.nodes Location.root).map Prod.fst).idxOf source <
      ((tree.nodes Location.root).map Prod.fst).idxOf target := by
  let locations := (tree.nodes Location.root).map Prod.fst
  have order := tree.locations_order Location.root (by simp [Location.root])
  have firstBound := List.idxOf_lt_length_of_mem first
  have lastBound := List.idxOf_lt_length_of_mem last
  by_cases earlier : locations.idxOf source < locations.idxOf target
  · exact earlier
  · by_cases same : locations.idxOf source = locations.idxOf target
    · have equal : source = target := by
        have leftValue := List.getElem_idxOf firstBound
        change locations[locations.idxOf source] = source at leftValue
        simp only [same] at leftValue
        exact leftValue.symm.trans (List.getElem_idxOf lastBound)
      exact False.elim (before.ne equal)
    · have reverse := order.rel_getElem_of_lt lastBound firstBound (by dsimp [locations] at earlier same; omega)
      rw [List.getElem_idxOf lastBound, List.getElem_idxOf firstBound] at reverse
      exact False.elim (Location.Earlier.irrefl _ (before.trans reverse))

theorem rank_forward {tree : ExecutionTree} {closed : Location → Bool} {source target : Location}
    (first : source ∈ (tree.nodes Location.root).map Prod.fst)
    (last : target ∈ (tree.nodes Location.root).map Prod.fst)
    (same : ancestors closed target = ancestors closed source) (before : source.Earlier target) :
    Prod.Lex (· < ·) (· < ·) (rank tree closed target) (rank tree closed source) := by
  have positions := position_lt first last before
  have inside := List.idxOf_lt_length_of_mem last
  simp only [rank, same]
  exact .right _ (by omega)

theorem rank_redirect (tree : ExecutionTree) {closed : Location → Bool} {source parent : Location}
    (enters : parent.entersChild source = true) (finished : closed parent = true) :
    Prod.Lex (· < ·) (· < ·) (rank tree closed parent) (rank tree closed source) :=
  .left _ _ (ancestors_redirect enters finished)

private theorem fixed_checkpoint {before checked after : Durable}
    (started : Grows before checked) (later : Grows checked after) (fixed : view before = view after) :
    view checked = view after :=
  later.1.antisymm (by rw [← fixed]; exact started.1)

/-- When the journal is fixed, every emitted location strictly decreases the
finite progress measure. Fork initialization cannot occur without a new record;
an incomplete fork exposes children, a join advances, and stale work wakes a
completed ancestor. Duplicate delivery does not change any of these facts. -/
theorem StepProgress.rank_decreases {tree current node before after locations}
    (route : TreeRoute tree Location.root current node)
    (progress : StepProgress tree current node before (.runnable locations) after)
    (emitted : Emits tree (.runnable locations) after)
    (fixed : view before = view after) (closed : Location → Bool)
    (correct : ∀ location, closed location = true ↔ ∃ outcome, CompletedAt (view after) location.key outcome)
    (target : Location) (member : target ∈ locations) :
    Prod.Lex (· < ·) (· < ·) (rank tree closed target) (rank tree closed current) := by
  have first : current ∈ (tree.nodes Location.root).map Prod.fst := List.mem_map.mpr ⟨_, route.member, rfl⟩
  have last : target ∈ (tree.nodes Location.root).map Prod.fst := by
    obtain ⟨node, route, _⟩ := emitted target member
    exact List.mem_map.mpr ⟨_, route.member, rfl⟩
  cases progress with
  | command progress =>
    cases progress with
    | finished recorded =>
      cases linked : current.parent? with
      | none => simp [Finished, linked] at recorded
      | some pair =>
        obtain ⟨parent, index⟩ := pair
        have notification : Notification parent index node.exit before after (.runnable locations) := by
          simpa only [Finished, linked] using recorded.2
        cases notification with
        | wake outcome complete =>
          have same : target = parent := by simpa using member
          subst target
          exact rank_redirect tree (Location.ReportsTo.of_parent linked).2.1 ((correct parent).mpr ⟨outcome, complete⟩)
        | waiting => simp at member
    | initialized size checked started later noResult noFork published =>
      have same := fixed_checkpoint started later fixed
      rw [same] at noResult noFork
      exact False.elim (initialized_changes ⟨noResult, noFork⟩ published rfl)
    | waiting size slots slotSize checked started later incomplete settled published =>
      have same := fixed_checkpoint started later fixed
      rw [same] at incomplete
      have openGroup : closed current = false := by
        cases found : closed current with
        | false => rfl
        | true =>
          obtain ⟨outcome, complete⟩ := (correct current).mp found
          exact False.elim (incomplete outcome complete)
      obtain ⟨index, _, selected⟩ := Array.mem_filterMap.mp member
      split at selected
      · cases selected
        apply rank_forward first last
        · simp [ancestors_child, openGroup]
        · exact Location.earlier_child current index
      · cases selected
    | joined complete =>
      have same : target = current.next := by simpa using member
      subst target
      exact rank_forward first last (ancestors_next closed current)
        (Location.earlier_next current (route.nonempty (by simp [Location.root])))
  | redirect redirected =>
    obtain ⟨parent, children, result, next, parentRoute, active, complete, enters, work⟩ := redirected
    cases work
    have same : target = parent := by simpa using member
    subst target
    exact rank_redirect tree enters ((correct parent).mpr ⟨_, complete⟩)
  | parent parent index outcome linked complete work =>
    cases work
    have same : target = parent := by simpa using member
    subst target
    exact rank_redirect tree (Location.ReportsTo.of_parent linked).2.1 ((correct parent).mpr ⟨outcome, complete⟩)

/-- Collapse an older notification witness to the fixed visible journal.
Physical logs and queue contents need not be equal. -/
theorem OpenReport.fixed {source : Location} {before after state : Durable}
    (report : OpenReport source before after) (first : view before = view state) (last : view after = view state) :
    OpenReport source state state := by
  obtain ⟨parent, index, outcome, checked, linked, started, later, child, incomplete⟩ := report
  have same := fixed_checkpoint started later (first.trans last.symm)
  rw [same, last] at child incomplete
  exact ⟨parent, index, outcome, state, linked, .refl _, .refl _, child, incomplete⟩

end LeanCloud.Proofs.ConcurrentJournal
