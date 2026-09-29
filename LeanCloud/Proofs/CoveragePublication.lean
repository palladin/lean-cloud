import LeanCloud.Proofs.TreeCoverage
import LeanCloud.Proofs.JournalFrame

/-! Coverage through the journal writes of one retained child delivery.
The write footprint is the actual completion layout: the child's result, its
parent slot, and the optional parent-result cache. -/

namespace LeanCloud.Proofs
open Lean JournalDb JournalLayout JournalAdapter ReplayRecovery

/-- A retained command can still run after its own descriptor or result is
recorded. Unrelated groups keep exactly the same missing children. -/
theorem Coverage.grow_command {tree root before after pending done current node}
    (nonempty : 0 < root.size) (member : (current, node) ∈ tree.nodes root)
    (covered : Coverage before pending tree root done) (growth : Extends before after)
    (available : pending current)
    (frame : Frame [forkKey current.key, resultKey current.key] before after) :
    Coverage after pending tree root done := by
  apply covered.grow growth (fun h => h)
  intro location children result next group _ uncached missing
  by_cases same : location = current
  · subst location
    exact .inr ⟨current, available, .here current⟩
  have different : resultKey location.key ≠ resultKey current.key :=
    fun equal => same (Location.key_injective (tree.node_nonempty nonempty group)
      (tree.node_nonempty nonempty member) (result_key_injective equal))
  refine .inl ⟨(frame _ (by simp [result_ne_fork, different])).trans uncached, ?_⟩
  obtain ⟨index, absent⟩ := missing
  exact ⟨index, (frame _ (by simp [Ne.symm (fork_ne_child current.key location.key index.val),
    Ne.symm (result_ne_child current.key location.key index.val)])).trans absent⟩

private theorem initial_fork_footprint (key : String) (count : Nat) :
    ∀ entry ∈ records key (Result.settle (Array.replicate count none)),
      entry.1 ∈ [forkKey key, resultKey key] := by
  cases count with
  | zero =>
    intro entry member
    simp [Result.settle, records, pure, Except.pure, Functor.map, Except.map] at member
    subst entry
    simp
  | succ count =>
    rw [Result.settle_missing _ (by simp)]
    intro entry member
    simp [records, childRecord] at member
    rcases member with same | ⟨index, inside, value, slot, _⟩
    · subst entry; simp
    · simp [getElem!_pos, inside] at slot

/-- Actual fork initialization preserves coverage even if only its descriptor
or empty-group result committed. The incoming message is still responsible for
publishing the child work items or the empty group's join. -/
theorem Expansion.initialize_fork_covered {m : Type → Type} {program : Cloud m Json}
    {tree root current children result next pending done}
    (expansion : Expansion program (.fork children result next))
    (nonempty : 0 < root.size) (member : (current, .fork children result next) ∈ tree.nodes root)
    (initial : Journal) (bounded : Extends initial (tree.journal root))
    (covered : Coverage initial pending tree root done) (available : pending current)
    (comparable : Comparable (tree.journal root)) :
    Spec (· = initial)
      (ReplayInterpreter.Internal.save db current (Result.settle (Array.replicate children.length none)))
      (fun _ journal => Between initial (tree.journal root) journal ∧
        Coverage journal pending tree root done ∧
        Published (records current.key (Result.settle (Array.replicate children.length none))) journal ∧
        Frame [forkKey current.key, resultKey current.key] initial journal)
      (fun journal => Between initial (tree.journal root) journal ∧ Coverage journal pending tree root done ∧
        Frame [forkKey current.key, resultKey current.key] initial journal) := by
  have saved := tree.save_admitted nonempty member
    (expansion.settle_admitted (ExecutionTree.PartialSlots.empty children)) comparable initial
  have frame := save_frame [forkKey current.key, resultKey current.key] initial current
    (Result.settle (Array.replicate children.length none)) (initial_fork_footprint current.key children.length)
  apply (saved.preserve frame).weaken
  · intro journal same; subst journal; exact ⟨⟨Extends.refl _, bounded⟩, Frame.refl _ _⟩
  · intro _ journal h
    exact ⟨h.1.1, covered.grow_command nonempty member h.1.1.1 available h.2, h.1.2, h.2⟩
  · intro journal h
    exact ⟨h.1, covered.grow_command nonempty member h.1.1 available h.2, h.2⟩

/-- Even an interrupted completion cannot strand its parent's join. If the
parent becomes complete, the retained child delivery can wake it. All other
waiting groups retain their exact missing slots and result-cache state. -/
theorem Coverage.grow_completion {m : Type → Type} {program : Cloud m Json}
    {tree root before after pending done current parent index}
    (expansion : Expansion program tree) (nonempty : 0 < root.size)
    (covered : Coverage before pending tree root done) (growth : Extends before after)
    (bounded : Extends after (tree.journal root)) (available : pending current)
    (linked : current.parent? = some (parent, index))
    (frame : Frame [resultKey current.key, childKey parent.key index, resultKey parent.key] before after) :
    Coverage after pending tree root done := by
  have parentSize := (Location.parent_size linked).1
  have currentSize : 0 < current.size := by have := (Location.parent_size linked).2; omega
  apply covered.grow_of_woken expansion nonempty growth bounded (fun h => h)
  intro location children result next member descriptor uncached missing completed
  by_cases own : location = current
  · subst location
    exact ⟨current, available, .here current⟩
  by_cases parentNode : location = parent
  · subst location
    exact ⟨current, available, .parent linked completed (.here parent)⟩
  have locationSize := tree.node_nonempty nonempty member
  have otherOwn : resultKey location.key ≠ resultKey current.key :=
    fun same => own (Location.key_injective locationSize currentSize (result_key_injective same))
  have otherParent : resultKey location.key ≠ resultKey parent.key :=
    fun same => parentNode (Location.key_injective locationSize parentSize (result_key_injective same))
  have sameCache : after (resultKey location.key) = before (resultKey location.key) :=
    frame _ (by simp [otherOwn, otherParent, result_ne_child])
  obtain ⟨child, absent⟩ := missing
  have otherSlot : childKey location.key child.val ≠ childKey parent.key index :=
    fun same => parentNode (Location.key_injective locationSize parentSize (child_key_injective same).1)
  have sameSlot : after (childKey location.key child.val) = before (childKey location.key child.val) :=
    frame _ (by simp [otherSlot, Ne.symm (result_ne_child current.key location.key child.val),
      Ne.symm (result_ne_child parent.key location.key child.val)])
  exact False.elim (completed.no_missing (sameCache.trans uncached) (growth _ _ descriptor) child
    (sameSlot.trans absent))

/-- The existing precise completion interval supplies that footprint; no
stronger database transaction or atomic group update is assumed. -/
theorem Coverage.completion_interval {m : Type → Type} {program : Cloud m Json}
    {tree root before after pending done current parent index outcome slots}
    (expansion : Expansion program tree) (nonempty : 0 < root.size)
    (covered : Coverage before pending tree root done)
    (interval : Between before (completionJournal before current parent index outcome slots) after)
    (bounded : Extends after (tree.journal root)) (available : pending current)
    (linked : current.parent? = some (parent, index))
    (uncached : before (resultKey parent.key) = none) :
    Coverage after pending tree root done := by
  apply covered.grow_completion expansion nonempty interval.1 bounded available linked
  intro key outside
  have different : key ≠ resultKey current.key ∧ key ≠ childKey parent.key index ∧ key ≠ resultKey parent.key := by
    simpa using outside
  exact interval.fixed key
    ((completionJournal_fields before current parent index outcome slots linked uncached).2.2.2 key
      different.1 different.2.1 different.2.2)

/-- The actual child completion preserves global workflow coverage through
every physical read/write and crash. Its selected message is retained until
the queue adapter publishes the returned work. -/
theorem TreeRoute.finish_child_covered {m : Type → Type} {program : Cloud m Json}
    {tree current node parent index slots pending done}
    (expansion : Expansion program tree) (route : TreeRoute tree Location.root current node)
    (linked : current.parent? = some (parent, index))
    (initial : Journal) (bounded : Extends initial (tree.journal Location.root))
    (covered : Coverage initial pending tree Location.root done) (available : pending current)
    (view : JournalDb.get raw parent.key initial = (some (toJson (Result.suspended slots)), initial))
    (comparable : Comparable (tree.journal Location.root))
    (ready : node.FinishReady current initial) (sameExit : (node.exit == node.exit) = true) :
    let updated := slots.set! index (some node.exit)
    Spec (· = initial) (ReplayInterpreter.Internal.finish db current node.exit)
      (fun response journal => Between initial (tree.journal Location.root) journal ∧
        Coverage journal pending tree Location.root done ∧ CompletedAt journal current.key node.exit ∧
        JournalDb.get raw parent.key journal = (some (toJson (Result.settle updated)), journal) ∧
        response = completionResponse parent (Result.settle updated))
      (fun journal => Between initial (tree.journal Location.root) journal ∧
        Coverage journal pending tree Location.root done) := by
  have rootSize : 0 < Location.root.size := by simp [Location.root]
  obtain ⟨children, result, next, inside, parentNode, childResult⟩ := route.child_outcome linked
  have uncached := (tree.suspended_snapshot rootSize parentNode initial bounded view).1
  obtain ⟨interval, safe⟩ := expansion.finish_child_from_tree rootSize route.member ready.admitted parentNode
    ⟨index, inside⟩ linked childResult initial bounded
    (tree.finish_source rootSize route.member bounded ready) view comparable sameExit
  apply safe.weaken
  · intro journal same; subst journal; exact ⟨Extends.refl _, interval.1⟩
  · intro response journal h
    have bound := h.1.1.2.trans interval.2
    exact ⟨⟨h.1.1.1, bound⟩, covered.completion_interval expansion rootSize h.1.1 bound available linked uncached,
      h.1.2, h.2⟩
  · intro journal h
    have bound := h.2.trans interval.2
    exact ⟨⟨h.1, bound⟩, covered.completion_interval expansion rootSize h bound available linked uncached⟩

end LeanCloud.Proofs
