import LeanCloud.Proofs.ReplayStep
import LeanCloud.Proofs.Storage

/-! Replay a branch's recorded prefix without re-executing its effects.
The certificate tracks recorded values and locations. `Evaluation` separately
proves where those values and the external-state changes came from. -/

namespace LeanCloud.Proofs.ReplayModel
open Lean LeanEff ReplayInterpreter.Internal

/-- A recorded prefix connects two computations and their locations.
`steps` counts reconstruction iterations, including transparent delays. -/
inductive ReplayPrefix {World : Type} (journal : Journal) :
    Cloud (StateM World) Json → Location →
    Cloud (StateM World) Json → Location → Nat → Prop where
  | here {program location} :
      ReplayPrefix journal program location program location 0
  | delay {continuation current remaining target steps} :
      ReplayPrefix journal (ArrsF.apply continuation ()) current
        remaining target steps →
      ReplayPrefix journal (.impure .delay continuation) current
        remaining target (steps + 1)
  | sequential {α : Type} {codec : Codec α} {operation : Operation (StateM World) α}
      {continuation current remaining target steps value}
      (law : CodecLaw codec)
      (recorded : journal current.key =
        some (toJson (Result.completed (.success (codec.encode value))))) :
      ReplayPrefix journal (ArrsF.apply continuation value) current.next
        remaining target steps →
      ReplayPrefix journal (.impure (.sequential codec operation) continuation)
        current remaining target (steps + 1)
  | parallel {α : Type} {codec : Codec α} {count : Nat}
      {branches : Fin count → Cloud (StateM World) α}
      {continuation current remaining target steps values}
      (law : CodecLaw codec) (size : values.size = count)
      (recorded : journal current.key =
        some (toJson (Result.completed (.success (Json.arr (values.map codec.encode)))))) :
      ReplayPrefix journal (ArrsF.apply continuation values) current.next
        remaining target steps →
      ReplayPrefix journal (.impure (.parallel codec count branches) continuation)
        current remaining target (steps + 1)

namespace ReplayPrefix

variable {World : Type} {blobs : BlobModel World} {journal : Journal}
    {program remaining : Cloud (StateM World) Json} {current target : Location}
    {steps : Nat}

/-- Compose prefixes at their shared computation and location. -/
theorem trans {middle : Cloud (StateM World) Json} {middleLocation : Location}
    {firstSteps secondSteps : Nat}
    (first : ReplayPrefix journal program current
      middle middleLocation firstSteps)
    (second : ReplayPrefix journal middle middleLocation
      remaining target secondSteps) :
    ReplayPrefix journal program current
      remaining target (firstSteps + secondSteps) := by
  induction first with
  | here => simpa using second
  | delay _ ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ReplayPrefix.delay (ih second)
  | sequential law recorded _ ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ReplayPrefix.sequential law recorded (ih second)
  | parallel law size recorded _ ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ReplayPrefix.parallel law size recorded (ih second)

/-- Preserving completed records preserves the replay certificate. -/
theorem preserve {updated : Journal}
    (certificate : ReplayPrefix journal program current
      remaining target steps)
    (preserved : Journal.PreservesCompleted journal updated) :
    ReplayPrefix updated program current remaining target steps := by
  induction certificate with
  | here => exact .here
  | delay _ ih => exact .delay ih
  | sequential law recorded _ ih =>
    exact .sequential law (preserved _ _ recorded) ih
  | parallel law size recorded _ ih =>
    exact .parallel law size (preserved _ _ recorded) ih

theorem same_depth
    (certificate : ReplayPrefix journal program current
      remaining target steps) : current.size = target.size := by
  induction certificate with
  | here => rfl
  | delay _ ih => exact ih
  | sequential _ _ _ ih => simpa only [Location.size_next] using ih
  | parallel _ _ _ _ ih => simpa only [Location.size_next] using ih

theorem command_le
    (certificate : ReplayPrefix journal program current
      remaining target steps) (nonempty : 0 < current.size) :
    current[current.size - 1]!.2 ≤ target[target.size - 1]!.2 := by
  induction certificate with
  | here => exact Nat.le_refl _
  | delay _ ih => exact ih nonempty
  | sequential _ _ _ ih | parallel _ _ _ _ ih =>
    have nextBound := ih (Location.next_nonempty _ nonempty)
    simp only [Location.size_next] at nextBound
    have advance := Location.next_command _ nonempty
    omega

/-- Extending a branch prefix leaves the route through every ancestor intact. -/
theorem keeps_ancestor
    (certificate : ReplayPrefix journal program current
      remaining target steps) {ancestor : Location}
    (enters : ancestor.entersChild current = true) : ancestor.entersChild target = true := by
  induction certificate with
  | here => exact enters
  | delay _ ih => exact ih enters
  | sequential _ _ _ ih | parallel _ _ _ _ ih => exact ih (Location.entersChild_next enters)

theorem branch_at
    (certificate : ReplayPrefix journal program current
      remaining target steps) (index : Nat) (inside : index < current.size) :
    target[index]!.1 = current[index]!.1 := by
  induction certificate with
  | here => rfl
  | delay _ ih => exact ih inside
  | sequential _ _ _ ih | parallel _ _ _ _ ih =>
    exact (ih (by simpa using inside)).trans (Location.next_branch _ index inside)

theorem root_branch (certificate : ReplayPrefix journal program current remaining target steps)
    (nonempty : 0 < current.size) : target[0]!.1 = current[0]!.1 :=
  certificate.branch_at 0 nonempty

private theorem earlier_ne_requested {current target requested : Location}
    (depth : current.size = target.size)
    (earlier : current[current.size - 1]!.2 < target[target.size - 1]!.2)
    (aligned : target = requested ∨ target.entersChild requested = true) : current ≠ requested := by
  intro equal
  rcases aligned with rfl | enters
  · subst current
    exact Nat.lt_irrefl _ earlier
  · have deeper := Location.entersChild_size enters
    rw [equal] at depth
    omega

/-- Recorded prefixes reconstruct the selected computation without executing
any primitive effect or changing any part of the environment state. -/
theorem reconstruct_towards
    (certificate : ReplayPrefix journal program current remaining target steps)
    (fuel : Nat) (world : World) (pending : List Location) (completed : Option Exit)
    (requested : Location) (aligned : target = requested ∨ target.entersChild requested = true)
    (nonempty : 0 < current.size) :
    (walk (storage blobs) (fuel + steps) program current requested).run ⟨journal, pending, completed⟩ world =
      (walk (storage blobs) fuel remaining target requested).run ⟨journal, pending, completed⟩ world := by
  induction certificate with
  | here => rfl
  | delay _ ih =>
    rw [Nat.add_succ, walk_delay]
    exact ih aligned nonempty
  | sequential law recorded tail ih =>
    have depth := tail.same_depth
    simp only [Location.size_next] at depth
    have later := tail.command_le (Location.next_nonempty _ nonempty)
    simp only [Location.size_next] at later
    have advance := Location.next_command _ nonempty
    have different := earlier_ne_requested depth (by omega) aligned
    rw [Nat.add_succ, walk_recorded_sequential blobs _ _ law _ _ _ _ _ _ _ different recorded]
    exact ih aligned (Location.next_nonempty _ nonempty)
  | parallel law size recorded tail ih =>
    have depth := tail.same_depth
    simp only [Location.size_next] at depth
    have later := tail.command_le (Location.next_nonempty _ nonempty)
    simp only [Location.size_next] at later
    have advance := Location.next_command _ nonempty
    have different := earlier_ne_requested depth (by omega) aligned
    rw [Nat.add_succ, walk_recorded_parallel blobs _ _ law _ _ _ _ _ _ _ _ size different recorded]
    exact ih aligned (Location.next_nonempty _ nonempty)

theorem reconstruct
    (certificate : ReplayPrefix journal program current remaining target steps)
    (fuel : Nat) (world : World) (pending : List Location) (completed : Option Exit)
    (nonempty : 0 < current.size) :
    (walk (storage blobs) (fuel + steps) program current target).run ⟨journal, pending, completed⟩ world =
      (walk (storage blobs) fuel remaining target target).run ⟨journal, pending, completed⟩ world :=
  certificate.reconstruct_towards fuel world pending completed target (Or.inl rfl) nonempty

end ReplayPrefix
end LeanCloud.Proofs.ReplayModel
