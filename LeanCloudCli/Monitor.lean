import LeanCloudCli.Runtime
import LeanCloudCli.Styled

namespace LeanCloudCli
open Lean LeanCloud

structure Node where
  name : String
  state : String
  role : String := ""
  resources : Option (Array ResourceSample) := none
  warning : String := ""
  deriving Inhabited

def Context.nodes (ctx : Context) : Cli (Array Node) := do
  let connection ← ctx.requireConnection
  let nodes ← Client.call connection .nodes
  saveJson (ctx.home / "nodes.json") nodes
  return nodes.map fun node => {
    name := ctx.node node.id, role := node.id
    state := if node.online then "running" else "unavailable"
    resources := some node.samples, warning := node.warning }

def humanBytes (value : Nat) : String :=
  if value ≥ 1073741824 then s!"{value / 1073741824}.{value % 1073741824 * 10 / 1073741824} GiB"
  else if value ≥ 1048576 then s!"{value / 1048576}.{value % 1048576 * 10 / 1048576} MiB"
  else if value ≥ 1024 then s!"{value / 1024}.{value % 1024 * 10 / 1024} KiB"
  else s!"{value} B"

def percent (value : Nat) : String :=
  let fraction := toString (value % 1000 / 10)
  s!"{value / 1000}.{if fraction.length == 1 then "0" ++ fraction else fraction}%"

def spark (values : Array (Option Nat)) (width : Nat := 24) (scale : Option Nat := none) : String := Id.run do
  let values := values.extract (values.size - width) values.size
  let peak := max 1 (scale.getD (values.foldl (fun n v => max n (v.getD 0)) 0))
  let marks := "▁▂▃▄▅▆▇█".toList.toArray
  let mut result := String.ofList (List.replicate (width - values.size) ' ')
  for value in values do
    result := result.push (match value with
      | none => '·'
      | some 0 => '_'
      | some n => marks[min 7 ((n * 8 + peak - 1) / peak - 1)]!)
  return result

structure History where
  name : String
  resources : Array ResourceSample := #[]
  fresh : Bool := true
  deriving Inhabited

/-- Each API response already contains the bounded sample window for its node. -/
def rememberNodes (nodes : Array Node) : Array History :=
  nodes.map fun node => {
    name := node.name, fresh := node.state == "running", resources := node.resources.getD #[] }

private def pressure (used capacity : Nat) : Styled.Color :=
  if used * 100 ≥ capacity * 90 then .red
  else if used * 100 ≥ capacity * 70 then .yellow else .green

/-- A fixed-capacity meter. Overflow stays visible as `+` and in the numeric
value; missing capacity is not rendered as an empty (zero-usage) meter. -/
def meter (used capacity width : Nat) : Styled.Line := Id.run do
  if capacity == 0 then return Styled.text "[unavailable]" .muted
  let filled := min width ((used * width + capacity - 1) / capacity)
  let color := pressure used capacity
  let bars := String.ofList (List.replicate filled '|')
  let bars := if used > capacity && width > 0 then
    String.ofList (bars.toList.take (width - 1)) ++ "+" else bars
  return Styled.text "[" .muted ++ Styled.text bars color ++
    Styled.text (String.ofList (List.replicate (width - filled) '·')) .muted ++ Styled.text "]" .muted

end LeanCloudCli
