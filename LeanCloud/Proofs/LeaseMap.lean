import LeanCloud.Proofs.BackendMap
import Init.Data.Array.Monadic

/-! The actual leased-work adapter preserves a backend map, including its local
receipt state and the separate successor-publication and acknowledgement calls. -/

namespace LeanCloud.Proofs.BackendMap
open LeanCloud.LeaseQueue
variable {m n : Type → Type} [Monad m] [Monad n]

def lease (f : BackendMap m n) (queue : LeanCloud.LeaseQueue σ m ρ) : LeanCloud.LeaseQueue σ n ρ where
  enqueue location := (f.state σ).map (queue.enqueue location)
  dequeue := (f.state σ).map queue.dequeue
  acknowledge receipt := (f.state σ).map (queue.acknowledge receipt)

theorem liftBackend_map (f : BackendMap m n) (action : StateT σ m α) :
    (f.state (Worker σ ρ)).map (liftBackend action) = liftBackend ((f.state σ).map action) := by
  funext worker
  change f.map (action worker.backend >>= _) = _
  rw [f.map_bind]
  congr 1
  funext pair
  exact f.map_pure _

theorem next_map (f : BackendMap m n) (queue : LeanCloud.LeaseQueue σ m ρ)
    (read : StateT σ m (Option Exit)) (write : Exit → StateT σ m Unit) :
    (f.state (Worker σ ρ)).map (queue.toWorkQueue read write).next =
      ((f.lease queue).toWorkQueue ((f.state σ).map read) (fun outcome => (f.state σ).map (write outcome))).next := by
  simp only [toWorkQueue, (f.state (Worker σ ρ)).map_bind, f.map_modify, liftBackend_map]
  congr 1
  funext cleared
  congr 1
  funext completed
  cases completed with
  | some outcome => exact (f.state (Worker σ ρ)).map_pure _
  | none =>
    simp only [(f.state (Worker σ ρ)).map_bind, liftBackend_map]
    congr 1
    funext delivery
    cases delivery with
    | none => exact (f.state (Worker σ ρ)).map_pure _
    | some delivery =>
      simp only [(f.state (Worker σ ρ)).map_bind, f.map_modify, (f.state (Worker σ ρ)).map_pure]

theorem complete_map (f : BackendMap m n) (queue : LeanCloud.LeaseQueue σ m ρ)
    (read : StateT σ m (Option Exit)) (write : Exit → StateT σ m Unit)
    (location : Location) (response : StepResult) :
    (f.state (Worker σ ρ)).map ((queue.toWorkQueue read write).complete location response) =
      ((f.lease queue).toWorkQueue ((f.state σ).map read) (fun outcome => (f.state σ).map (write outcome))).complete location response := by
  simp only [toWorkQueue, (f.state (Worker σ ρ)).map_bind, f.map_get]
  congr 1
  funext worker
  cases worker.delivery with
  | none => exact (f.state (Worker σ ρ)).map_pure _
  | some delivery =>
    obtain ⟨delivered, receipt⟩ := delivery
    by_cases different : (delivered != location) = true
    · simp only [different, ↓reduceIte, (f.state (Worker σ ρ)).map_pure]
    · simp only [different, Bool.false_eq_true, ↓reduceIte]
      cases response with
      | done outcome =>
        simp only [(f.state (Worker σ ρ)).map_bind, liftBackend_map, f.map_modify]
        rfl
      | runnable locations =>
        simp only [(f.state (Worker σ ρ)).map_bind, liftBackend_map, f.map_modify]
        congr 1
        · rw [← Array.forIn_toList, ← Array.forIn_toList, (f.state (Worker σ ρ)).map_forIn]
          congr 1
          funext location acc
          simp only [(f.state (Worker σ ρ)).map_bind, liftBackend_map, (f.state (Worker σ ρ)).map_pure]
          rfl

end LeanCloud.Proofs.BackendMap
