import LeanCloud.Proofs.Resumption

namespace LeanCloud.Proofs.Suspension
open Lean LeanEff ReplayModel ReplayInterpreter Reconstruction

variable {info : Option SourceSiteId}

/-- After suspension the parent can resume at its fork, and every child can be
reconstructed from the same source using the durable records already present. -/
def Paths {m : Type → Type u} (journal : Journal) (encode : α → Json) (program : Cloud m α)
    (current location : Location) (count : Nat) : Prop :=
  Resumable journal encode program current location ∧
    ∀ index : Fin count, Resumable journal encode program current (location.child index)

theorem Paths.lift {m : Type → Type u} {journal current source location count}
    {encode : α → Json} {program : Cloud m α} {sourceEncode : β → Json} {sourceProgram : Cloud m β}
    (paths : Paths journal encode program current location count)
    (lift : ∀ target, Resumable journal encode program current target →
      Resumable journal sourceEncode sourceProgram source target) :
    Paths journal sourceEncode sourceProgram source location count :=
  ⟨lift _ paths.1, fun index => lift _ (paths.2 index)⟩

theorem Paths.extend {m : Type → Type u} {before after current location count}
    {encode : α → Json} {program : Cloud m α} (paths : Paths before encode program current location count)
    (extension : Extends before after) : Paths after encode program current location count :=
  ⟨paths.1.extend extension, fun index => (paths.2 index).extend extension⟩

theorem Paths.prepend {m : Type → Type u} {journal source current location count steps}
    {encode : α → Json} {program : Cloud m α} {sourceEncode : β → Json} {sourceProgram : Cloud m β}
    (paths : Paths journal encode program current location count)
    (witness : Prefix journal current sourceEncode sourceProgram source steps encode program)
    (nonempty : 0 < source.size) : Paths journal sourceEncode sourceProgram source location count :=
  paths.lift (fun _ resumable => resumable.prepend witness nonempty)

/-- The paths carried by a fork report are mathematical certificates of the
existing message; no continuation or program is added to its wire format. -/
def ReportPaths {m : Type → Type u} (journal : Journal) (encode : α → Json) (program : Cloud m α)
    (report : Report) : Prop :=
  ∀ location count, report.progress = .ok (.fork location count) →
    Paths journal encode program Location.root location count

theorem ReportPaths.extend {m : Type → Type u} {before after} {encode : α → Json} {program : Cloud m α} {report}
    (paths : ReportPaths before encode program report) (extension : Extends before after) :
    ReportPaths after encode program report :=
  fun location count forked => (paths location count forked).extend extension

theorem immediate {m : Type → Type u} (journal : Journal) (encode : β → Json) (current : Location)
    (codec : Codec α) (count : Nat) (branches : Fin count → Cloud m α) (next : ArrsF (Control m) SourceSiteId (Array α) β) :
    Paths journal encode (.impure info (.parallel codec count branches) next) current current count :=
  ⟨.here .., fun index => .child journal encode current codec count branches next index⟩

end LeanCloud.Proofs.Suspension
