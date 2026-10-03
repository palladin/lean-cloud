import LeanCloud.Proofs.BackendProtocol

namespace LeanCloud.Backend.Proofs.Iteration
open Lean LeanEff LeanCloud.Proofs

def dispatch (traversal : Nat) (source : Cloud Replay.M Json)
    (reply : Option (Location × Receipt)) : Backend.M Outcome :=
  match reply with
  | none => ((afterPoll traversal source .idle).run ⟨(), none⟩).run
  | some (location, receipt) => ((afterPoll traversal source (.item location)).run ⟨(), some (location, receipt)⟩).run

def polling (traversal : Nat) (source : Cloud Replay.M Json) :
    {β : Type} → Request β → (β → Program Outcome) → Prop
  | _, .dequeue, next => ∀ reply, next reply = Program.ofEff (dispatch traversal source reply)
  | _, _, _ => True

def NoDequeue : {β : Type} → Request β → Prop
  | _, .dequeue => False
  | _, _ => True

theorem no_dequeue_protocol (traversal : Nat) (source : Cloud Replay.M Json) {program : Program Outcome}
    (uses : program.uses NoDequeue) : program.protocol (polling traversal source) := by
  induction program with
  | pure value => trivial
  | request operation next ih =>
    refine ⟨?_, fun value => ih value (uses.2 value)⟩
    cases operation <;> try trivial
    exact False.elim uses.1

private theorem write_no_dequeue (outcome : Exit) :
    StateUses NoDequeue (CompletionStore.write Replay.rawDb throw outcome) := by
  have get : StateUses NoDequeue (Replay.rawDb.get CompletionStore.key) :=
    fun _ => ⟨trivial, fun _ => trivial⟩
  have put : StateUses NoDequeue (Replay.rawDb.put CompletionStore.key (toJson outcome)) :=
    fun _ => ⟨trivial, fun _ => trivial⟩
  unfold CompletionStore.write
  apply StateUses.bind (StateUses.putSame Replay.rawDb _ _ get put)
  intro accepted
  cases accepted <;> exact fun _ => Uses.pure _ _

theorem complete_no_dequeue (location : Location) (response : StepResult) :
    StateUses NoDequeue (Replay.queue.complete location response) := by
  unfold Replay.queue LeaseQueue.toWorkQueue
  simp only []
  apply StateUses.bind (fun _ => Uses.pure _ _)
  intro worker
  cases held : worker.delivery with
  | none => exact .pure _
  | some pair =>
    obtain ⟨delivered, receipt⟩ := pair
    simp only []
    split
    · exact .pure _
    · have acknowledge : StateUses NoDequeue (Replay.transport.acknowledge receipt) :=
        fun _ => ⟨trivial, fun _ => trivial⟩
      have finish := acknowledge.leased.bind (fun _ =>
        (show StateUses NoDequeue (modify fun worker : Replay.Worker => {worker with delivery := none}) from
          fun _ => Uses.pure _ _))
      cases response with
      | done outcome => exact (write_no_dequeue outcome).leased.bind fun _ => finish
      | runnable locations =>
        apply StateUses.bind (rest := fun _ => finish)
        rw [← Array.forIn_toList]
        apply StateUses.forIn
        intro item acc
        have enqueue : StateUses NoDequeue (Replay.transport.enqueue item) :=
          fun _ => ⟨trivial, fun _ => trivial⟩
        exact enqueue.leased.bind fun _ => .pure _

theorem afterPoll_no_dequeue (traversal : Nat) (source : Cloud Replay.M Json)
    (supported : PureProgram source) (work : Work) :
    StateUses NoDequeue (afterPoll traversal source work).run := by
  cases work with
  | idle | completed _ => exact .pure _
  | item location =>
    unfold afterPoll
    apply StateUses.except_bind
    · intro worker
      exact (Footprint.step traversal source supported location worker).mono (second := NoDequeue)
        (by intro β operation allowed; cases operation <;> simp_all [NoDequeue, Footprint.JournalOnly])
    · intro response
      exact (complete_no_dequeue location response).except.except_bind fun _ => .pure _

/-- Normalize the two real polling requests. JSON decoding is ordinary pure
code; an invalid completion record remains an infrastructure error. -/
theorem normalized (traversal : Nat) (source : Cloud Replay.M Json) :
    Program.ofEff (program traversal source) =
      .request (.get CompletionStore.key) (fun value =>
        match value with
        | none => .request .dequeue (fun reply => Program.ofEff (dispatch traversal source reply))
        | some json =>
          match fromJson? (α := Exit) json with
          | .error _ => .pure (.error "Invalid workflow completion record")
          | .ok outcome => .pure (.ok (.ok (some outcome), ⟨(), none⟩))) := by
  apply congrArg (Program.request (.get CompletionStore.key))
  funext value
  cases value with
  | none =>
    apply congrArg (Program.request .dequeue)
    funext reply
    cases reply with
    | none => rfl
    | some pair => cases pair; rfl
  | some json =>
    dsimp [program, ReplayIteration.iteration, Replay.queue, LeaseQueue.toWorkQueue,
      CompletionStore.read, Replay.rawDb, LeaseQueue.liftBackend,
      Program.ofEff, Program.ofArrs, Program.bind, EffF.bind, EffF.send,
      Backend.request, StateT.run, StateT.bind, StateT.pure, ExceptT.run,
      ExceptT.bind, ExceptT.bindCont, ExceptT.lift, ExceptT.pure, ExceptT.mk, liftM, monadLift, pure,
      bind, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]
    cases fromJson? (α := Exit) json <;> rfl

theorem protocol (traversal : Nat) (source : Cloud Replay.M Json) (supported : PureProgram source) :
    (Program.ofEff (program traversal source)).protocol (polling traversal source) := by
  rw [normalized]
  refine ⟨trivial, ?_⟩
  intro value
  cases value with
  | some json =>
    simp only []
    cases fromJson? (α := Exit) json <;> trivial
  | none =>
    refine ⟨fun _ => rfl, ?_⟩
    intro reply
    apply no_dequeue_protocol
    cases reply with
    | none => trivial
    | some pair => exact afterPoll_no_dequeue traversal source supported (.item pair.1) ⟨(), some pair⟩

end LeanCloud.Backend.Proofs.Iteration
