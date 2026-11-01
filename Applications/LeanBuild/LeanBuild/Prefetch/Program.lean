import LeanCloud.ExecServices
import LeanEff.Core
import Std.Data.HashSet

namespace LeanBuild.Prefetch
open Lean LeanCloud LeanEff

/-- Queue observations and local transfer completions; no receipt is acquired. -/
inductive Operation : Type → Type where
  | observe : Operation (Nat × Array Nat × Bool)
  | peek (after : Option WorkPosition) : Operation (Array WorkPreview)
  | start (item : WorkPreview) : Operation Unit

inductive Host : Effect where
  | request (operation : Operation α) : Host (Except String α)

abbrev Program := ExceptT String (EffF Host Empty)

def perform (operation : Operation α) : Program α := ExceptT.mk (EffF.send (.request operation))

structure State where
  warmed : Std.HashSet Nat := {}
  active : Std.HashSet Nat := {}
  pending : Array WorkPreview := #[]
  after : Option WorkPosition := none
  nextHead : Nat := 0
  nextPage : Nat := 0

/-- Keep following priority order without a page barrier. Time and completion
order come from the handler, so the same policy can run on a virtual clock. -/
partial def program (concurrency : Nat) (state : State := {}) : Program Unit := do
  let (now, completed, cancelled) ← perform .observe
  if cancelled then return
  let mut s := { state with
    active := completed.foldl (·.erase ·) state.active
    warmed := completed.foldl (·.insert ·) state.warmed }
  let unseen := fun (item : WorkPreview) =>
    !s.warmed.contains item.position.sequence && !s.active.contains item.position.sequence
  s := { s with pending := s.pending.filter unseen }
  if now ≥ s.nextHead then
    let head ← perform (.peek none)
    let candidates := head.filter unseen
    unless candidates.isEmpty do
      s := { s with pending := candidates, after := head.back?.map (·.position) }
    s := { s with nextHead := now + 200 }
  if s.pending.isEmpty && s.active.size < max 1 concurrency && now ≥ s.nextPage then
    let page ← perform (.peek s.after)
    s := { s with after := page.back?.map (·.position), pending := page.filter unseen }
    if s.pending.isEmpty then s := { s with nextPage := now + 200 }
  while s.active.size < max 1 concurrency && !s.pending.isEmpty do
    let some item := s.pending[0]? | break
    perform (.start item)
    s := { s with pending := s.pending.extract 1 s.pending.size, active := s.active.insert item.position.sequence }
  program concurrency s

partial def runWith [Monad m] (handle : {α : Type} → Operation α → m (Except String α))
    (program : Program α) : m (Except String α) := do
  match program.run with
  | .pure _ result => return result
  | .impure _ (.request op) next =>
    runWith handle (ExceptT.mk (next.apply (← handle op)))

end LeanBuild.Prefetch
