import LeanCloud.Backend.Contract

/-! An executable instance of the service laws. Decisions belong to the test
driver/environment, not to the replay interpreter. Every decision is checked;
selecting a nonexistent publication is an invalid test schedule. -/

namespace LeanCloud.Backend

structure Decision where
  delivery : Option MessageId := none
  acceptAcknowledgement : Bool := true
  deriving Repr, BEq

def execute (decision : Decision) (request : Request α) (state : State) :
    Except String (α × State) :=
  match request with
  | .get key => .ok (state.records.lookup key, state)
  | .put key value => .ok (true, { state with
      records := (key, value) :: state.records
      pastRecords := state.records :: state.pastRecords })
  | .enqueue location => .ok ((), { state with
      queue.messages := state.queue.messages.push { location, published := state.snapshot } })
  | .dequeue =>
    match decision.delivery with
    | none => .ok (none, state)
    | some id =>
      match state.queue.messages[id]? with
      | none => .error "Delivery does not refer to an accepted publication"
      | some message => .ok (some (message.location, state.queue.receipts.size),
          { state with queue.receipts := state.queue.receipts.push id })
  | .acknowledge receipt =>
    if !decision.acceptAcknowledgement then .ok (false, state)
    else
      match state.queue.receipts[receipt]? with
      | none => .ok (false, state)
      | some id =>
        match state.queue.messages[id]? with
        | none => .error "Receipt refers to a missing publication"
        | some message => .ok (true, { state with
            queue.messages := state.queue.messages.setIfInBounds id { message with acknowledged := true } })

/-- The executable model is checked against the same relation that constrains
adapter histories. This is a primitive-operation theorem, not an interpreter
equivalence assumption. -/
theorem execute_sound (decision : Decision) (request : Request α)
    (before after : State) (reply : α)
    (executed : execute decision request before = .ok (reply, after)) :
    Commits before request reply after := by
  cases request with
  | get key =>
    cases executed
    exact ⟨rfl, rfl⟩
  | put key value =>
    cases executed
    simp only [Commits, Db.Put, ↓reduceIte]
    refine ⟨?_, ?_, by trivial, by trivial⟩
    · simp [Db.view]
    · intro other different
      simp [Db.view, List.lookup_cons, beq_eq_false_iff_ne.mpr different]
  | enqueue location =>
    cases executed
    exact ⟨rfl, rfl⟩
  | dequeue =>
    cases selected : decision.delivery with
    | none =>
      simp only [execute, selected] at executed
      cases executed
      rfl
    | some id =>
      cases stored : before.queue.messages[id]? with
      | none => simp [execute, selected, stored] at executed
      | some message =>
        simp only [execute, selected, stored] at executed
        cases executed
        exact ⟨id, message, stored, rfl, rfl, rfl⟩
  | acknowledge receipt =>
    simp only [execute] at executed
    split at executed
    · cases executed; rfl
    · cases known : before.queue.receipts[receipt]? with
      | none =>
        simp only [known] at executed
        cases executed; rfl
      | some id =>
        simp only [known] at executed
        cases stored : before.queue.messages[id]? with
        | none => simp [stored] at executed
        | some message =>
          simp only [stored] at executed
          cases executed
          exact ⟨id, message, known, stored, rfl⟩

/-- The executable model is an instance of the abstract primitive contract. -/
def modelLaws : Laws State where
  view := id
  operation operation before reply after :=
    ∃ decision, execute decision operation before = .ok (reply, after)
  commits operation before reply after performed := by
    obtain ⟨decision, performed⟩ := performed
    exact execute_sound decision operation before after reply performed

end LeanCloud.Backend
