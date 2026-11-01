import LeanBuild.Builders.Program

/-! A small-step handler for the *same* builder Eff program used in production.
Each scheduler turn executes at most one request. Parallel children retain their
continuations and obey their pool limit; launched jobs belong to a builder scope.
Only queue rows and immutable result records are shared between builders.

Lease expiry and cancellation are injected between requests. Expiry fences old
receipts (as WorkQueueStore does); cancellation drains jobs, closes Lake and
releases the builder's receipts before its scope can finish. -/
namespace LeanBuild.Tests.BuilderModel
open Lean LeanEff LeanCloud Builders

private def require (condition : Bool) (message : String) : Except String PUnit.{u+1} :=
  unless condition do throw message

private structure Pool (α : Type) (count : Nat) : Type 1 where
  next : Nat := 0
  active : Array (Fin count) := #[]
  results : Array (Option α) := Array.replicate count none
  error : Option String := none
  halted : Bool := false

private inductive Fiber : Type → Type 1 where
  | run {α : Type} (program : Program BuildResult α) : Fiber α
  | pool {α β : Type} (limit count : Nat) (children : Fin count → Fiber β)
      (state : Pool β count) (stop : β → Bool)
      (next : Except String (Array β) → Program BuildResult α) : Fiber α

private instance : Inhabited (Fiber α) := ⟨.run (throw "Invalid model fiber")⟩

private def Fiber.outcome : Fiber α → Option (Except String α)
  | .run program => match program.run with | .pure _ result => some result | _ => none
  | .pool .. => none

private structure Lease where
  item : WorkItem
  worker : Nat

private structure Worker where
  root : Fiber Unit
  jobs : Array (Fiber (Event BuildResult)) := #[]
  replies : Array (Event BuildResult) := #[]
  prepared : Std.HashSet String := {}
  installed : Std.HashSet String := {}
  receipts : Std.HashSet String := {}
  session : LakeSession.State := {}
  queued : Array Module := #[]
  running : Array Module := #[]
  completions : Array (String × BuildResult) := #[]
  slots : Nat := 1
  peak : Nat := 0
  cancelled : Bool := false
  closed : Bool := false
  submitted : Nat := 0
  deriving Inhabited

structure Coverage where
  requests : Nat := 0
  switches : Nat := 0
  redeliveries : Nat := 0
  expiries : Nat := 0
  cancellations : Nat := 0
  cancelledJobs : Nat := 0
  cancelledOutstanding : Nat := 0
  releasedOnCancel : Nat := 0
  crossWorkerRedeliveries : Nat := 0
  staleAcks : Nat := 0
  staleReleases : Nat := 0
  repeatedCommits : Nat := 0
  poolOverlap : Bool := false
  buildersOverlap : Bool := false
  cancellationPhase : String := ""
  deriving Repr

structure Faults where
  expire : Nat := 0
  cancelAfter : Option String := none

private structure World where
  workers : Array Worker
  queue : Array WorkItem := #[]
  sent : Std.HashSet String := {}
  leases : Std.HashMap String Lease := {}
  delivered : Std.HashMap String Nat := {}
  records : Std.HashMap String BuildResult := {}
  finished : Std.HashSet String := {}
  serial : Nat := 0
  clock : Nat := 0
  random : Nat := 0
  failure : Option String := none
  faults : Faults := {}
  coverage : Coverage := {}
  lastWorker : Option Nat := none
  /-- Last effect boundary, used for reproducible fault injection. -/
  boundary : Option (Nat × String) := none

private def World.update (s : World) (worker : Nat) (f : Worker → Worker) : World :=
  { s with workers := s.workers.modify worker f }

private def Worker.fill (w : Worker) : Worker :=
  let room := w.slots - w.running.size
  let running := w.running ++ w.queued.extract 0 room
  { w with running, queued := w.queued.extract room w.queued.size, peak := max w.peak running.size }

private def label : Operation BuildResult α → String
  | .readResult _ => "read"
  | .commitResult _ => "commit"
  | .install .. => "install"
  | .lake (.submit _) => "submit"
  | .publish .. => "publish"
  | .send _ => "send"
  | .complete .. => "ack"
  | .receive _ => "receive"
  | _ => "local"

/-- A stale receipt is a no-op, never an ACK/release of a replacement lease. -/
private def release (s : World) (worker : Nat) (receipt : String) : World :=
  let s := s.update worker fun w => { w with receipts := w.receipts.erase receipt }
  match s.leases[receipt]? with
  | none => { s with coverage.staleReleases := s.coverage.staleReleases + 1 }
  | some lease => { s with
      leases := s.leases.erase receipt, queue := s.queue.push lease.item
      coverage.releasedOnCancel := s.coverage.releasedOnCancel + if s.workers[worker]!.cancelled then 1 else 0 }

/-- The outer Except reports a violated model invariant. The inner Except is
an operation error delivered back to the real Eff continuation. -/
private def operate (worker : Nat) : Operation BuildResult α → World → Except String (Except String α × World)
  | .readResult name, s => return (.ok s.records[name]?, s)
  | .commitResult result, s => do
    if s.workers[worker]!.cancelled then return (.error "Build cancelled", s)
    if let some old := s.records[result.name]? then
      require (old.status == result.status) "Conflicting immutable results"
      return (.ok old, { s with coverage.repeatedCommits := s.coverage.repeatedCommits + 1 })
    return (.ok result, { s with records := s.records.insert result.name result })
  | .prepared, s => return (.ok s.workers[worker]!.prepared, s)
  | .remember inputs, s => do
    require (inputs.all (fun r => s.workers[worker]!.installed.contains r.name) || s.workers[worker]!.cancelled)
      "Remembered artifacts before installation"
    return (.ok (), s.update worker fun w => { w with prepared := inputs.foldl (fun names r => names.insert r.name) w.prepared })
  | .install _ inputs _, s => do
    require (inputs.all (·.status == .built)) "Installed failed prerequisite"
    if s.workers[worker]!.cancelled then return (.ok (), s)
    return (.ok (), s.update worker fun w => { w with installed := inputs.foldl (fun names r => names.insert r.name) w.installed })
  | .lake (.start cpus), s => do
    let .ok session := s.workers[worker]!.session.start | throw "Invalid Lake start"
    return (.ok (), s.update worker fun w => { w with session, slots := compilerSlots cpus })
  | .lake (.submit m), s => do
    let w := s.workers[worker]!
    let .ok session := w.session.submit m.name | throw "Invalid Lake submission"
    require (m.imports.all (fun n => s.records[n]?.any (·.status == .built))) "Compiled before prerequisites were durable"
    require (m.imports.all w.installed.contains || w.cancelled) "Compiled without local prerequisites"
    return (.ok (), s.update worker fun w => { w with session, queued := w.queued.push m, submitted := w.submitted + 1 }.fill)
  | .lake .poll, s => do
    let w := s.workers[worker]!
    let .ok session := w.session.complete (w.completions.map (·.1)) | throw "Invalid Lake completion"
    return (.ok w.completions, s.update worker fun w => { w with session, completions := #[] })
  | .lake .finish, s => do
    let .ok session := s.workers[worker]!.session.finish | throw "Invalid Lake finish"
    return (.ok (), s.update worker fun w => { w with session })
  | .lake .cancel, s =>
    return (.ok (), s.update worker fun w => { w with session := w.session.cancel, queued := #[], running := #[], completions := #[] })
  | .publish _ result, s => return (.ok result, s)
  | .receive count, s => do
    let sorted := s.queue.qsort (fun a b => a.priority > b.priority)
    let batch := sorted.extract 0 count
    let deliveries := batch.mapIdx fun i item => { receipt := toString (s.serial + i), value := item.value : WorkDelivery }
    let leases := (batch.zip deliveries).foldl (fun leases (item, d) => leases.insert d.receipt ⟨item, worker⟩) s.leases
    let remaining := sorted.extract count sorted.size
    let redeliveries := (batch.filter (fun item => s.delivered.contains item.key)).size
    let crossWorker := (batch.filter (fun item => s.delivered[item.key]?.any (· != worker))).size
    let s := { s with
      queue := remaining, leases, serial := s.serial + batch.size
      delivered := batch.foldl (fun names (item : WorkItem) => names.insert item.key worker) s.delivered
      coverage.redeliveries := s.coverage.redeliveries + redeliveries
      coverage.crossWorkerRedeliveries := s.coverage.crossWorkerRedeliveries + crossWorker }
    let s := s.update worker fun w => { w with receipts := deliveries.foldl (fun names (d : WorkDelivery) => names.insert d.receipt) w.receipts }
    return (.ok (deliveries, remaining.isEmpty && leases.isEmpty), s)
  | .send items, s => do
    if s.workers[worker]!.cancelled then return (.ok (), s)
    let s := items.foldl (fun s item => if s.sent.contains item.key then s else
      { s with sent := s.sent.insert item.key, queue := s.queue.push item }) s
    return (.ok (), s)
  | .complete receipts _, s => do
    if s.workers[worker]!.cancelled then return (.ok (), s)
    let mut s := s
    for receipt in receipts do
      s := s.update worker fun w => { w with receipts := w.receipts.erase receipt }
      if let some lease := s.leases[receipt]? then
        require (lease.worker == worker) "Acknowledged another builder's receipt"
        require (s.records.contains lease.item.key) "Acknowledged before publication"
        s := { s with leases := s.leases.erase receipt, finished := s.finished.insert lease.item.key }
      else s := { s with coverage.staleAcks := s.coverage.staleAcks + 1 }
    return (.ok (), s)
  | .release receipts, s => return (.ok (), receipts.foldl (release · worker ·) s)
  | .cancelled, s => return (.ok s.workers[worker]!.cancelled, s)
  | .activity _, s => return (.ok (), s)
  | .events, s =>
    let w := s.workers[worker]!
    let replies := if w.cancelled then #[.cancelled] else w.replies
    return (.ok (s.clock, replies), s.update worker fun w => { w with replies := #[] })

/-- One effect, or one pool bookkeeping step. Never evaluates a whole job. -/
private partial def step (worker : Nat) (fiber : Fiber α) (s : World) : Except String (Fiber α × World) := do
  match fiber with
  | .run program =>
    match program.run with
    | .pure .. => return (fiber, s)
    | .impure _ (.request op) next =>
      let (value, s) ← operate worker op s
      let s := { s with
        boundary := some (worker, label op), lastWorker := some worker
        coverage.requests := s.coverage.requests + 1
        coverage.switches := s.coverage.switches + if s.lastWorker.any (· != worker) then 1 else 0 }
      return (.run (ExceptT.mk (next.apply value)), s)
    | .impure _ (.launch job) next =>
      let s := if s.workers[worker]!.cancelled then s else
        s.update worker fun w => { w with jobs := w.jobs.push (.run (ExceptT.mk job)) }
      return (.run (ExceptT.mk (next.apply ())), s)
    | .impure _ (.parallel limit count jobs) next =>
      return (.pool limit count (fun i => .run (ExceptT.mk (jobs i))) {} (fun _ => false)
        (fun result => ExceptT.mk (next.apply result)), s)
    | .impure _ (.all limit count jobs) next =>
      return (.pool limit count (fun i => .run (ExceptT.mk (jobs i))) {} (!·)
        (fun result => ExceptT.mk (next.apply (result.map (·.all id)))), s)
  | .pool limit count children state stop next =>
    let mut state := state
    while !state.halted && state.error.isNone && state.active.size < max 1 limit do
      if h : state.next < count then
        state := { state with next := state.next + 1, active := state.active.push ⟨state.next, h⟩ }
      else break
    let s := { s with coverage.poolOverlap := s.coverage.poolOverlap || state.active.size > 1 }
    if state.active.isEmpty then
      let result := match state.error with
        | some error => .error error
        | none => .ok (state.results.filterMap id)
      return (.run (next result), s)
    let slot := s.random % state.active.size
    let some i := state.active[slot]? | throw "Missing active child"
    let (child, s) ← step worker (children i) s
    let children := fun j => if j == i then child else children j
    if let some result := child.outcome then
      state := { state with active := state.active.eraseIdxIfInBounds slot }
      match result with
      | .error error => state := { state with error := some error }
      | .ok value => state := { state with results := state.results.set! i.val (some value), halted := state.halted || stop value }
    return (.pool limit count children state stop next, s)

private inductive Turn where
  | root (worker : Nat)
  | job (worker index : Nat)
  | compiler (worker : Nat)
  | close (worker : Nat)
  deriving Inhabited

private def runnable (s : World) : Array Turn := Id.run do
  let mut turns := #[]
  for i in [:s.workers.size] do
    let w := s.workers[i]!
    if w.closed then continue
    if w.root.outcome.isNone then turns := turns.push (.root i)
    for j in [:w.jobs.size] do turns := turns.push (.job i j)
    if !w.running.isEmpty then turns := turns.push (.compiler i)
    if w.root.outcome.isSome && w.jobs.isEmpty then turns := turns.push (.close i)
  return turns

private def takeTurn (turn : Turn) (s : World) : Except String World := do
  match turn with
  | .root worker =>
    let (root, s) ← step worker s.workers[worker]!.root s
    return s.update worker fun w => { w with root }
  | .job worker index =>
    let (job, s) ← step worker s.workers[worker]!.jobs[index]! s
    match job.outcome with
    | none => return s.update worker fun w => { w with jobs := w.jobs.set! index job }
    | some outcome =>
      let s := s.update worker fun w => { w with jobs := w.jobs.eraseIdxIfInBounds index }
      if s.workers[worker]!.cancelled then return s
      match outcome with
      | .error error => throw error
      | .ok event => return s.update worker fun w => { w with replies := w.replies.push event }
  | .compiler worker =>
    let w := s.workers[worker]!
    let i := s.random % w.running.size
    let some m := w.running[i]? | throw "Missing compiler job"
    let result : BuildResult := { name := m.name, status := if s.failure == some m.name then .failed else .built }
    return s.update worker fun w => { w with
      running := w.running.eraseIdxIfInBounds i
      completions := w.completions.push (m.name, result) }.fill
  | .close worker =>
    let w := s.workers[worker]!
    if let some (.error error) := w.root.outcome then unless w.cancelled do throw error
    require (w.cancelled || w.session.phase == .closed) "Builder returned with open Lake session"
    let s := w.receipts.toArray.foldl (release · worker ·) s
    return s.update worker fun w => { w with
      closed := true, replies := #[], session := w.session.cancel
      queued := #[], running := #[], completions := #[] }

private def inject (s : World) : World := Id.run do
  let mut s := s
  if let some (worker, phase) := s.boundary then
    -- Expire a live delivery while its old continuation still owns a receipt.
    if s.faults.expire > 0 && (phase == "publish" || phase == "commit") && !s.leases.isEmpty then
      let entries := s.leases.toArray
      let some (receipt, lease) := entries[s.random % entries.size]? | return s
      s := { s with
        leases := s.leases.erase receipt, queue := s.queue.push lease.item
        faults.expire := s.faults.expire - 1, coverage.expiries := s.coverage.expiries + 1 }
    let w := s.workers[worker]!
    let outstanding := w.jobs.size + w.receipts.size + w.session.pending.size
    if s.faults.cancelAfter == some phase && !w.cancelled && outstanding > 0 then
      s := s.update worker fun w => { w with cancelled := true }
      s := { s with
        faults.cancelAfter := none, coverage.cancellations := s.coverage.cancellations + 1
        coverage.cancelledJobs := s.coverage.cancelledJobs + s.workers[worker]!.jobs.size
        coverage.cancelledOutstanding := s.coverage.cancelledOutstanding + outstanding
        coverage.cancellationPhase := phase }
  return s

structure Result : Type 1 where
  records : Std.HashMap String BuildResult
  coverage : Coverage
  participating : Nat

/-- Finite seeded schedules; failure reports include the seed at the call site.
No wall-clock timing, threads, native processes or real service calls. -/
def run (plan : Plan) (cpus : Array Nat) (seed : Nat) (failure : Option String := none)
    (faults : Faults := {}) : Except String Result := do
  require (cpus.size ≥ 2) "Model needs multiple builders"
  let workers := cpus.map fun cpus => { root := .run (program plan cpus) : Worker }
  let mut s : World := { workers, random := seed, failure, faults }
  -- Workflow seeds once before launching builders. Interpret the actual seeding
  -- program too, without injecting builder failures into this earlier stage.
  let mut seeding : Fiber Unit := .run (seedProgram plan)
  while seeding.outcome.isNone do
    let (next, world) ← step 0 seeding s
    seeding := next
    s := world
  if let some (.error error) := seeding.outcome then throw error
  for _ in [:200000] do
    if s.workers.all (·.closed) then
      require (s.queue.isEmpty && s.leases.isEmpty && s.finished.size == plan.modules.size) "Scopes closed with unfinished queue work"
      require (s.workers.all fun w => w.jobs.isEmpty && w.receipts.isEmpty && w.session.pending.isEmpty &&
        w.running.isEmpty && w.queued.isEmpty && w.peak ≤ w.slots) "Scope leaked jobs, leases or compiler slots"
      return {
        records := s.records, coverage := s.coverage
        participating := (s.workers.filter (·.submitted > 0)).size }
    s := { s with clock := s.clock + 1, random := (s.random * 1664525 + 1013904223) % 4294967296, boundary := none }
    let turns := runnable s
    require (!turns.isEmpty) "Model deadlocked"
    let before := s.coverage.requests
    s ← takeTurn turns[s.random % turns.size]! s
    require (s.coverage.requests ≤ before + 1) "One scheduler turn ran multiple effects"
    s := inject s
    s := { s with coverage.buildersOverlap := s.coverage.buildersOverlap ||
      (s.workers.filter fun w => !w.session.pending.isEmpty).size > 1 }
  throw "Model exceeded its step budget"

end LeanBuild.Tests.BuilderModel
