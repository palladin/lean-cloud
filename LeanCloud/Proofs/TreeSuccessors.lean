import LeanCloud.Proofs.TreeActivation

/-! Durable prerequisites for work emitted by the interpreter. Membership in
the original program alone is insufficient: replay also needs the records on
the path to the selected command. -/

namespace LeanCloud.Proofs
open Lean JournalDb JournalAdapter ReplayRecovery

def TreeRoute.append {tree start middle node target leaf}
    (firstRoute : TreeRoute tree start middle node) (suffix : TreeRoute node middle target leaf) :
    TreeRoute tree start target leaf :=
  match firstRoute with
  | .terminal .. | .fork .. => suffix
  | .delay rest => .delay (rest.append suffix)
  | .next rest => .next (rest.append suffix)
  | .child index rest => .child index (rest.append suffix)

theorem TreeRoute.Activated.append {tree start middle node target leaf journal}
    {firstRoute : TreeRoute tree start middle node} {suffix : TreeRoute node middle target leaf}
    (first : firstRoute.Activated journal) (second : suffix.Activated journal) :
    (firstRoute.append suffix).Activated journal := by
  induction firstRoute with
  | terminal | fork => exact second
  | delay rest ih => exact ih first second
  | next rest ih => exact ⟨first.1, ih first.2 second⟩
  | child index rest ih => exact ⟨first.1, ih first.2 second⟩

/-- Some original reconstruction route has all its durable prerequisites. -/
def ExecutionTree.Activated (tree : ExecutionTree) (journal : Journal) (location : Location) : Prop :=
  ∃ node, ∃ route : TreeRoute tree Location.root location node, route.Activated journal

def ExecutionTree.EmitsActivated (tree : ExecutionTree) (journal : Journal) : StepResult → Prop
  | .done outcome => outcome = tree.exit
  | .runnable locations => ∀ location ∈ locations, tree.Activated journal location

theorem ExecutionTree.Activated.grow {tree before after location}
    (active : ExecutionTree.Activated tree before location) (growth : Extends before after) :
    tree.Activated after location := by
  obtain ⟨node, route, activated⟩ := active
  exact ⟨node, route, activated.grow growth⟩

theorem ExecutionTree.Activated.root (tree : ExecutionTree) (journal : Journal) :
    tree.Activated journal Location.root := tree.entry_activated Location.root journal

theorem TreeRoute.Activated.location {tree target node journal}
    {route : TreeRoute tree Location.root target node} (active : route.Activated journal) :
    tree.Activated journal target := ⟨node, route, active⟩

theorem TreeRoute.Activated.child {tree current children result next journal}
    {route : TreeRoute tree Location.root current (.fork children result next)}
    (active : route.Activated journal)
    (opened : journal (forkKey current.key) = some (toJson children.length) ∨
      CompletedAt journal current.key (encodeOutcome (inferInstance : Codec Json) result))
    (index : Fin children.length) : tree.Activated journal (current.child index.val) := by
  obtain ⟨node, entry, ready⟩ := children[index.val].entry_activated (current.child index.val) journal
  exact ⟨node, route.append (.child index entry), active.append ⟨opened, ready⟩⟩

theorem TreeRoute.Activated.next {tree current children result next journal}
    {route : TreeRoute tree Location.root current (.fork children result (some next))}
    (active : route.Activated journal)
    (completed : CompletedAt journal current.key (encodeOutcome (inferInstance : Codec Json) result)) :
    tree.Activated journal current.next := by
  obtain ⟨node, entry, ready⟩ := next.entry_activated current.next journal
  exact ⟨node, route.append (.next entry), active.append ⟨completed, ready⟩⟩

private theorem TreeRoute.Activated.parent_route {tree current target node journal}
    {route : TreeRoute tree current target node} (active : route.Activated journal)
    (nonempty : 0 < current.size) :
    target.parent? = current.parent? ∨
      ∃ parent index node, target.parent? = some (parent, index) ∧
        ∃ firstRoute : TreeRoute tree current parent node, firstRoute.Activated journal := by
  induction route with
  | terminal | fork => exact .inl rfl
  | delay rest ih =>
    rcases ih active nonempty with same | ⟨parent, index, node, linked, firstRoute, ready⟩
    · exact .inl same
    · exact .inr ⟨parent, index, node, linked, .delay firstRoute, ready⟩
  | @next children result tree current target node rest ih =>
    rcases ih active.2 (by simpa using nonempty) with same | ⟨parent, index, node, linked, firstRoute, ready⟩
    · exact .inl (same.trans (Location.next_parent_eq current))
    · exact .inr ⟨parent, index, node, linked, .next firstRoute, active.1, ready⟩
  | @child children result next current target node index rest ih =>
    rcases ih active.2 (by simp) with same | ⟨parent, child, node, linked, firstRoute, ready⟩
    · exact .inr ⟨current, index.val, _, same.trans (Location.parent_child current nonempty index.val),
        .fork children result next current, trivial⟩
    · exact .inr ⟨parent, child, node, linked, .child index firstRoute, active.1, ready⟩

theorem TreeRoute.Activated.parent {tree target node journal parent index}
    {route : TreeRoute tree Location.root target node} (active : route.Activated journal)
    (linked : target.parent? = some (parent, index)) : tree.Activated journal parent := by
  rcases active.parent_route (by simp [Location.root]) with same |
    ⟨original, child, node, originalLink, firstRoute, ready⟩
  · rw [linked] at same
    simp [Location.root, Location.parent?] at same
  · rw [linked] at originalLink
    cases originalLink
    exact ⟨node, firstRoute, ready⟩

theorem ExecutionTree.EmitsActivated.singleton {tree journal location}
    (active : ExecutionTree.Activated tree journal location) : tree.EmitsActivated journal (.runnable #[location]) := by
  intro selected member
  have same : selected = location := by simpa using member
  exact same ▸ active

theorem ExecutionTree.EmitsActivated.completion {tree journal parent}
    (active : ExecutionTree.Activated tree journal parent) (result : Result) :
    tree.EmitsActivated journal (completionResponse parent result) := by
  cases result with
  | completed _ => exact singleton active
  | suspended _ => intro _ member; simp at member

theorem TreeRoute.emits_initial_activated {tree current children result next journal}
    (route : TreeRoute tree Location.root current (.fork children result next))
    (active : route.Activated journal) (count : Nat) (size : children.length = count)
    (published : Published (records current.key (Result.settle (Array.replicate count none))) journal) :
    tree.EmitsActivated journal
      (.runnable (if count == 0 then #[current] else Array.ofFn fun index : Fin count => current.child index.val)) := by
  by_cases empty : count = 0
  · simp only [empty, beq_self_eq_true, ↓reduceIte]
    exact ExecutionTree.EmitsActivated.singleton active.location
  · have missing : none ∈ (Array.replicate count none : Array (Option Exit)) := by simp [empty]
    rw [Result.settle_missing _ missing] at published
    have descriptor := (published_fork published).1
    simp only [Array.size_replicate] at descriptor
    simp only [beq_eq_false_iff_ne.mpr empty, Bool.false_eq_true, ↓reduceIte]
    intro location member
    obtain ⟨index, rfl⟩ := Array.mem_ofFn.mp member
    exact active.child (.inl (by simpa only [size] using descriptor)) ⟨index.val, by omega⟩

theorem TreeRoute.emits_missing_activated {tree current children result next journal}
    (route : TreeRoute tree Location.root current (.fork children result next))
    (active : route.Activated journal) (count : Nat) (size : children.length = count)
    (slots : Array (Option Exit))
    (descriptor : journal (forkKey current.key) = some (toJson children.length)) :
    tree.EmitsActivated journal (.runnable ((Array.ofFn fun index : Fin count => index.val).filterMap fun index =>
      if slots[index]!.isNone then some (current.child index) else none)) := by
  intro location member
  obtain ⟨index, member, selected⟩ := Array.mem_filterMap.mp member
  obtain ⟨original, rfl⟩ := Array.mem_ofFn.mp member
  split at selected
  · cases selected
    exact active.child (.inl descriptor) ⟨original.val, by omega⟩
  · cases selected

end LeanCloud.Proofs
