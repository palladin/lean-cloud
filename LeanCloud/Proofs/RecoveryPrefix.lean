import LeanCloud.Proofs.RecoveryCursor

namespace LeanCloud.Proofs.RecoveryPrefix
open Lean LeanEff ReplayFaults ReplayModel ReplayInterpreter WorkerRecovery
open ReplayCursor Routing

variable {info : Option SourceSiteId}

private theorem command (point : ReplayTarget)
    (branch : point.branchStart = Proofs.Location.branchStart point.location)
    (current : Location) (fuel : Nat) (encode : β → Json) (codec : Codec α)
    (operation : LeanCloud.Operation WorkerM α) (next : ArrsF (Control WorkerM) SourceSiteId α β)
    (wire : Json) (value : α)
    (valid : ∀ journal, pre journal → invariant journal)
    (present : ∀ journal, pre journal → journal.lookup (ReplayStore.valueKey current) =
      some ⟨Internal.request codec operation, .success wire⟩)
    (decoded : codec.decode wire = .ok value)
    (rest : Ensures invariant pre (atPoint ReplayFaults.store ReplayFaults.noBlobs point fuel encode (next.apply value) current.next) post) :
    Ensures invariant pre (atPoint ReplayFaults.store ReplayFaults.noBlobs point (fuel + 1) encode
      (.impure info (.command codec operation) next) current) post := by
  have nextSize : current.next.size = current.size := by simp [LeanCloud.Location.next]
  by_cases same : current.size = point.location.size
  · simp only [atPoint, same, beq_self_eq_true, ite_true, nextSize] at rest ⊢
    simp only [replay, Internal.command, bind_assoc]
    apply Ensures.read_bind _ _ valid
    intro found saved h
    have equal := h.2.trans (present saved.durable h.1)
    subst found
    simpa [Internal.check, Internal.resume, Internal.decode, decoded] using rest saved h.1
  · simp only [atPoint, beq_eq_false_iff_ne.mpr same, nextSize] at rest ⊢
    simp only [reconstruct, beq_eq_false_iff_ne.mpr (before_branch branch same),
      Bool.false_eq_true, ↓reduceIte, Internal.recorded, bind_assoc]
    apply Ensures.read_bind _ _ valid
    intro found saved h
    have equal := h.2.trans (present saved.durable h.1)
    subst found
    simpa [Internal.check, Internal.decode, decoded] using rest saved h.1

private theorem joined (point : ReplayTarget)
    (branch : point.branchStart = Proofs.Location.branchStart point.location)
    (current : Location) (fuel : Nat) (encode : β → Json) (codec : Codec α) (count : Nat)
    (branches : Fin count → Cloud WorkerM α) (next : ArrsF (Control WorkerM) SourceSiteId (Array α) β)
    (values : Array α) (route : Follows current point.location) (skip : current.entersChild point.location = false)
    (valid : ∀ journal, pre journal → invariant journal)
    (present : ∀ journal, pre journal → journal.lookup (ReplayStore.valueKey current) =
      some ⟨⟨"parallel", s!"array({codec.schema})/v1", toJson count⟩, .success (Json.arr (values.map codec.encode))⟩)
    (decoded : (@instCodecArray α codec).decode (Json.arr (values.map codec.encode)) = .ok values)
    (size : values.size = count)
    (rest : Ensures invariant pre (atPoint ReplayFaults.store ReplayFaults.noBlobs point fuel encode (next.apply values) current.next) post) :
    Ensures invariant pre (atPoint ReplayFaults.store ReplayFaults.noBlobs point (fuel + 1) encode
      (.impure info (.parallel codec count branches) next) current) post := by
  have nextSize : current.next.size = current.size := by simp [LeanCloud.Location.next]
  by_cases same : current.size = point.location.size
  · simp only [atPoint, same, beq_self_eq_true, ite_true, nextSize] at rest ⊢
    simp only [replay]
    apply Ensures.read_bind _ _ valid
    intro found saved h
    have equal := h.2.trans (present saved.durable h.1)
    subst found
    simpa [Internal.check, Internal.resume, Internal.decodeGroup, Internal.decode, decoded, size] using rest saved h.1
  · have skipped : current.entersChild point.branchStart = false := by
      rw [branch, Routing.enters_branchStart (by have := route.depth; omega), skip]
    simp only [atPoint, beq_eq_false_iff_ne.mpr same, nextSize] at rest ⊢
    simp only [reconstruct, beq_eq_false_iff_ne.mpr (before_branch branch same),
      skipped, Bool.false_eq_true, ↓reduceIte, Internal.recorded, bind_assoc]
    apply Ensures.read_bind _ _ valid
    intro found saved h
    have equal := h.2.trans (present saved.durable h.1)
    subst found
    simpa [Internal.check, Internal.decodeGroup, Internal.decode, decoded, size] using rest saved h.1

open RecoveryCursor

/-- Reconstruction reads only the cached prefix. A crash there preserves the
same precondition needed by the assigned computation. -/
theorem transport [rootCodec : Codec α] (source : Cloud WorkerM α)
    {journal current} {encode : β → Json} {program : Cloud WorkerM β} {cost}
    (cursor : Cursor source journal current encode program cost)
    (point : ReplayTarget) (branch : point.branchStart = Proofs.Location.branchStart point.location)
    (follows : Follows current point.location) (fuel : Nat)
    (valid : ∀ after, pre after → invariant after)
    (extension : ∀ after, pre after → Extends journal after)
    (rest : Ensures invariant pre (atPoint ReplayFaults.store ReplayFaults.noBlobs point fuel encode program current) post) :
    Ensures invariant pre (atPoint ReplayFaults.store ReplayFaults.noBlobs point (cost + fuel)
      rootCodec.encode source Location.root) post := by
  induction cursor generalizing point fuel with
  | root => simpa using rest
  | delay cursor ih =>
    rw [Nat.add_assoc]
    apply ih point branch follows (1 + fuel) extension
    simpa only [Nat.add_comm 1, ReplayCursor.delay _ _ _ branch] using rest
  | exec codec label body next cursor present decoded ih =>
    have route := (cursor.route source).1
    have edge := next_follows _ (Nat.lt_of_lt_of_le (by decide) route.depth)
    rw [Nat.add_assoc]
    apply ih point branch (edge.trans follows) (1 + fuel) extension
    rw [Nat.add_comm 1]
    exact command point branch _ fuel _ codec _ next _ _ valid
      (fun after h => extension after h _ _ present) decoded rest
  | joined codec count branches next values cursor present decoded size ih =>
    have route := (cursor.route source).1
    have nonempty : 0 < _ := Nat.lt_of_lt_of_le (by decide) route.depth
    have edge := next_follows _ nonempty
    have skip := skip_follows edge follows (next_ne _ nonempty) (skip_next _)
    rw [Nat.add_assoc]
    apply ih point branch (edge.trans follows) (1 + fuel) extension
    rw [Nat.add_comm 1]
    exact joined point branch _ fuel _ codec count branches next values (edge.trans follows) skip valid
      (fun after h => extension after h _ _ present) decoded size rest
  | @child β γ journal current encode cost info codec count branches next cursor index ih =>
    have route := (cursor.route source).1
    have edge := child_follows _ (Nat.lt_of_lt_of_le (by decide) route.depth) index
    have enters := enters_follows (enters_child _ index) follows
    have selected : point.location[current.size]!.1 = index.val := by
      simpa [LeanCloud.Location.child] using (follows.branch_at current.size (by simp [LeanCloud.Location.child])).symm
    rw [Nat.add_assoc]
    apply ih point branch (edge.trans follows) (1 + fuel) extension
    simpa only [Nat.add_comm 1,
      ReplayCursor.child _ _ _ branch _ _ codec count branches next _ _ index enters selected follows] using rest

end LeanCloud.Proofs.RecoveryPrefix
