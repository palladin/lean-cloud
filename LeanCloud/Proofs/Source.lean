import LeanCloud.DirectInterpreter

namespace LeanCloud.Proofs.Source
open LeanEff DirectInterpreter.Internal

/-! Source annotations change neither requests nor their meaning. These lemmas
also cover computations nested inside parallel effects. -/
mutual
  theorem eval_withSource {m : Type → Type u} [Monad m] {α : Type}
      (blobs : BlobStorage m) (site : SourceSiteId) (program : Cloud m α) :
      eval blobs (Cloud.withSource site program) = eval blobs program :=
    match program with
    | EffF.pure _ _ => rfl
    | .impure _ request next => by
      simp only [Cloud.withSource, eval]
      rw [control_withSource blobs site request]
      congr 1
      funext value
      exact continuation_withSource blobs site next value
  termination_by structural program

  theorem control_withSource {m : Type → Type u} [Monad m] {α : Type}
      (blobs : BlobStorage m) (site : SourceSiteId) (request : Control m α) :
      evalControl blobs (Cloud.sourceControl site request) = evalControl blobs request :=
    match request with
    | .delay | .fail _ | .command .. => rfl
    | .parallel codec count branches => by
      simp only [Cloud.sourceControl, evalControl]
      have same : (fun i => (eval blobs (Cloud.withSource site (branches i))).run) =
          (fun i => (eval blobs (branches i)).run) :=
        funext fun i => congrArg ExceptT.run (eval_withSource blobs site (branches i))
      rw [same]
  termination_by structural request

  theorem continuation_withSource {m : Type → Type u} [Monad m] {α β : Type}
      (blobs : BlobStorage m) (site : SourceSiteId)
      (next : ArrsF (Control m) SourceSiteId α β) (value : α) :
      evalContinuation blobs (Cloud.sourceContinuation site next) value = evalContinuation blobs next value :=
    match next with
    | .one k => eval_withSource blobs site (k value)
    | .append first rest => by
      simp only [Cloud.sourceContinuation, evalContinuation]
      rw [continuation_withSource blobs site first value]
      congr 1
      funext value
      exact continuation_withSource blobs site rest value
  termination_by structural next
end

end LeanCloud.Proofs.Source
