import LeanCloud.Proofs.BackendMap
import LeanCloud.Proofs.PureContinuation

/-! Change the underlying backend in the same cloud syntax. Branches, codecs,
and continuation functions are preserved; execution of user effects is outside
the pure recovery theorem. No closures are serialized by this proof mapping. -/

namespace LeanCloud.Proofs.BackendMap
open LeanEff
variable {m n : Type → Type} [Monad m] [Monad n]

def operation (f : BackendMap m n) : Operation m α → Operation n α
  | .exec label body => .exec label (fun arg => f.map (body arg))
  | .putBlob bytes => .putBlob bytes
  | .readBlob ref => .readBlob ref
  | .resolveBlob name => .resolveBlob name

mutual
  def program (f : BackendMap m n) (source : Cloud m α) : Cloud n α :=
    match source with
    | EffF.pure value => EffF.pure value
    | .impure request rest => .impure (f.control request) (f.continuation rest)
  termination_by structural source

  def control (f : BackendMap m n) (source : Control m α) : Control n α :=
    match source with
    | .delay => .delay
    | .fail error => .fail error
    | .parallel codec count branches => .parallel codec count (fun index => f.program (branches index))
    | .choice codec count branches => .choice codec count (fun index => f.program (branches index))
    | .sequential codec op => .sequential codec (f.operation op)
  termination_by structural source

  def continuation (f : BackendMap m n) (source : ArrsF (Control m) α β) : ArrsF (Control n) α β :=
    match source with
    | .one next => .one (fun value => f.program (next value))
    | .append first rest => .append (f.continuation first) (f.continuation rest)
  termination_by structural source
end

theorem program_bind (f : BackendMap m n) (source : Cloud m α) (next : α → Cloud m β) :
    f.program (EffF.bind source next) = EffF.bind (f.program source) (fun value => f.program (next value)) := by
  cases source <;> rfl

theorem program_map (f : BackendMap m n) (source : Cloud m α) (g : α → β) :
    f.program (g <$> source) = g <$> f.program source := f.program_bind source (fun value => EffF.pure (g value))

private def view (f : BackendMap m n) : ArrsF.ViewL (Control m) α β → ArrsF.ViewL (Control n) α β
  | .one next => .one (fun value => f.program (next value))
  | .cons next rest => .cons (fun value => f.program (next value)) (f.continuation rest)

private theorem viewLAppend_map (f : BackendMap m n) (first : ArrsF (Control m) α β) (rest : ArrsF (Control m) β γ) :
    ArrsF.viewLAppend (f.continuation first) (f.continuation rest) = f.view (ArrsF.viewLAppend first rest) := by
  cases first with
  | one next => rfl
  | append left right =>
    exact viewLAppend_map f left (.append right rest)
termination_by sizeOf first

private theorem viewL_map (f : BackendMap m n) (rest : ArrsF (Control m) α β) :
    ArrsF.viewL (f.continuation rest) = f.view (ArrsF.viewL rest) := by
  cases rest with
  | one next => rfl
  | append first rest => exact viewLAppend_map f first rest

theorem continuation_apply (f : BackendMap m n) (rest : ArrsF (Control m) α β) (value : α) :
    f.program (ArrsF.apply rest value) = ArrsF.apply (f.continuation rest) value := by
  rw [ArrsF.apply, ArrsF.apply, viewL_map]
  cases observed : ArrsF.viewL rest with
  | one next => rfl
  | cons next tail =>
    simp only [view, program_bind]
    congr 1
    funext value
    exact continuation_apply f tail value
termination_by sizeOf rest
decreasing_by simpa [observed] using ArrsF.viewL_rest_lt rest

end LeanCloud.Proofs.BackendMap
