import LeanCloud.JournalDb
import LeanCloud.LeaseQueue

/-! Proof tools for changing a backend monad without changing its operation
sequence. These maps preserve pure returns and binds; they are not interpreters. -/

namespace LeanCloud.Proofs
open Lean

structure BackendMap (m n : Type → Type) [Monad m] [Monad n] where
  map : {α : Type} → m α → n α
  map_pure : ∀ {α} (value : α), map (pure value) = pure value
  map_bind : ∀ {α β} (action : m α) (next : α → m β),
    map (action >>= next) = (map action >>= fun value => map (next value))

namespace BackendMap
variable {m n : Type → Type} [Monad m] [Monad n]

def comp {p : Type → Type} [Monad p] (first : BackendMap m n) (next : BackendMap n p) : BackendMap m p where
  map action := next.map (first.map action)
  map_pure value := by rw [first.map_pure, next.map_pure]
  map_bind action rest := by rw [first.map_bind, next.map_bind]

def state (f : BackendMap m n) (σ : Type) : BackendMap (StateT σ m) (StateT σ n) where
  map action := fun handle => f.map (action handle)
  map_pure value := by funext handle; exact f.map_pure (value, handle)
  map_bind action next := by funext handle; exact f.map_bind (action handle) (fun pair => next pair.1 pair.2)

def except (f : BackendMap m n) (ε : Type) : BackendMap (ExceptT ε m) (ExceptT ε n) where
  map action := ExceptT.mk (f.map action.run)
  map_pure value := by
    change f.map (pure (Except.ok value : Except ε _)) = pure _
    exact f.map_pure _
  map_bind {α β} action next := by
    change f.map (action.run >>= _) = _
    rw [f.map_bind]
    congr 1
    funext outcome
    cases outcome with
    | ok value => rfl
    | error error => exact f.map_pure (Except.error error : Except ε β)

def db (f : BackendMap m n) (backend : Db σ m) : Db σ n where
  get key := (f.state σ).map (backend.get key)
  put key value := (f.state σ).map (backend.put key value)

theorem map_forIn (f : BackendMap m n) (items : List α) (acc : β)
    (body : α → β → m (ForInStep β)) :
    f.map (forIn items acc body) = forIn items acc (fun item state => f.map (body item state)) := by
  induction items generalizing acc with
  | nil => exact f.map_pure acc
  | cons item rest ih =>
    simp only [List.forIn_cons, f.map_bind]
    congr 1
    funext step
    cases step with
    | done value => exact f.map_pure value
    | yield value => exact ih value

theorem map_get (f : BackendMap m n) : (f.state σ).map get = get := by
  funext handle
  exact f.map_pure (handle, handle)

theorem map_modify (f : BackendMap m n) (change : σ → σ) :
    (f.state σ).map (modify change) = modify change := by
  funext handle
  exact f.map_pure ((), change handle)

theorem map_throw (f : BackendMap m n) (error : ε) :
    (f.except ε).map (throw error : ExceptT ε m α) = throw error :=
  f.map_pure (Except.error error : Except ε α)

theorem map_lift [LawfulMonad m] [LawfulMonad n] (f : BackendMap m n) (action : m α) :
    (f.except ε).map (liftM action) = (liftM (f.map action) : ExceptT ε n α) := by
  change f.map (Except.ok <$> action) = Except.ok <$> f.map action
  simp only [← bind_pure_comp, f.map_bind, f.map_pure]

theorem map_functor [LawfulMonad m] [LawfulMonad n] (f : BackendMap m n) (action : m α) (g : α → β) :
    f.map (g <$> action) = g <$> f.map action := by
  simp only [← bind_pure_comp, f.map_bind, f.map_pure]

end BackendMap

/-- A map of storage actions may change the base monad and the local handle.
The latter accounts for the lease receipt carried by the actual worker loop. -/
structure DbMap {m n : Type → Type} [Monad m] [Monad n] (source : Db σ m) (target : Db τ n) where
  actions : BackendMap (StateT σ m) (StateT τ n)
  get : ∀ key, actions.map (source.get key) = target.get key
  put : ∀ key value, actions.map (source.put key value) = target.put key value

namespace DbMap
variable {m n p : Type → Type} [Monad m] [Monad n] [Monad p]

abbrev worker {source : Db σ m} {target : Db τ n} (f : DbMap source target) := f.actions.except CloudError

def leased [LawfulMonad m] (source : Db σ m) : DbMap source (LeanCloud.LeaseQueue.db (ρ := ρ) source) where
  actions := {
    map action := LeanCloud.LeaseQueue.liftBackend action
    map_pure value := by
      funext worker
      simp [LeanCloud.LeaseQueue.liftBackend, pure, StateT.pure]
    map_bind action next := by
      funext worker
      simp only [LeanCloud.LeaseQueue.liftBackend, bind, StateT.bind, bind_assoc, pure_bind] }
  get _ := rfl
  put _ _ := rfl

end DbMap
end LeanCloud.Proofs
