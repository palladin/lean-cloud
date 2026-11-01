import LeanBuild.Model

namespace LeanBuild.LakeSession

/-- The compiler session is a resource with an explicit lifecycle. `submit`
queues a module; `poll` returns each completed job once. Lake owns CPU scheduling. -/
inductive Operation (α : Type) : Type → Type where
  | start (cpus : Nat) : Operation α Unit
  | submit (module : Module) : Operation α Unit
  | poll : Operation α (Array (String × α))
  | finish : Operation α Unit
  | cancel : Operation α Unit

inductive Phase where
  | fresh | open | closed
  deriving BEq

/-- Protocol validation shared by the real handler and models. A session cannot
close with outstanding jobs, accept duplicate jobs, or return unknown results. -/
structure State where
  phase : Phase := .fresh
  pending : Std.HashSet String := {}
  submitted : Std.HashSet String := {}

def State.start (s : State) : Except String State := do
  unless s.phase == .fresh do throw "Lake session already started"
  return { s with phase := .open }

def State.submit (s : State) (name : String) : Except String State := do
  unless s.phase == .open do throw "Lake session is not open"
  if s.submitted.contains name then throw "Module already submitted to Lake"
  return { s with pending := s.pending.insert name, submitted := s.submitted.insert name }

def State.complete (s : State) (names : Array String) : Except String State := do
  unless s.phase == .open do throw "Lake session is not open"
  let mut s := s
  for name in names do
    unless s.pending.contains name do throw "Unknown or duplicate Lake completion"
    s := { s with pending := s.pending.erase name }
  return s

def State.finish (s : State) : Except String State := do
  unless s.phase == .open && s.pending.isEmpty do throw "Lake session has unfinished jobs or is not open"
  return { s with phase := .closed }

/-- Cancelling is idempotent, including before startup or after normal finish. -/
def State.cancel (s : State) : State := { s with phase := .closed, pending := {} }

end LeanBuild.LakeSession
