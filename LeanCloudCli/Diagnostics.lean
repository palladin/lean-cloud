import LeanCloudCli.Monitor

namespace LeanCloudCli

def listConnections (ctx : Context) : Cli Unit := do
  let catalog ← Profiles.load
  printHeading "  CONNECTION                    ENDPOINT"
  for entry in catalog.entries.qsort (fun a b => a.project < b.project) do
    let connection ← entry.context.requireConnection
    let marker := if entry.project == ctx.project && entry.root == ctx.root.toString then "* " else "  "
    printStyled (Styled.text (marker ++ pad 30 entry.project) (if marker == "* " then .selected else .cyan) ++
      Styled.text (safe connection.url))
  if catalog.entries.isEmpty then printLine "No saved connections. Use 'connect NAME URL'."
  printLine "* selected · use 'status' to check the selected endpoint"

def Context.status (ctx : Context) : Cli Unit := do
  let connection ← ctx.requireConnection
  printHeading s!"Deployment: {safe ctx.project}"
  let deployment ← ctx.deployment
  printLine s!"Endpoint:   {safe connection.url}"
  printLine s!"Identity:   {safe connection.deployment}"
  printLine s!"Image:      {safe deployment.image}"
  printLine s!"Programs:   {deployment.programs.size}"
  printLine s!"Runs:       {(← ctx.allRuns).size}; use 'ps' for workflow status"
  let nodes ← ctx.nodes
  printLine s!"Nodes:      {(nodes.filter (·.state == "running")).size}/{nodes.size} endpoints reachable; use 'top' for metrics"
  for node in nodes do
    printLine s!"  {safe node.role}: {safe node.state}"

private def check (label : String) (action : Cli Unit) : Cli Bool := do
  let result ← observing action
  match result with
  | .ok () => printStyled (Styled.text "[ok]   " .green ++ Styled.text label); return true
  | .error error => printStyled (Styled.text "[fail] " .red ++ Styled.text s!"{label}: {safe error}"); return false

/-- Read-only diagnostics of the same API used by every workflow command. -/
def Context.doctor (ctx : Context) : Cli Unit := do
  let connection ← ctx.requireConnection
  printHeading s!"Checking {safe ctx.project}…"
  let api ← check "Authenticated deployment API" (discard (Client.call connection .describe))
  let catalog ← check "Program catalog" (discard (Client.call connection .programs))
  let runs ← check "Run catalog" (discard (Client.call connection (.runs none 1)))
  let nodes ← check "Node endpoints" do
    let nodes ← Client.call connection .nodes
    unless !nodes.isEmpty && nodes.all (·.online) do throw "Some node endpoints are unavailable; use 'top'"
  printLine "Checks cover authentication and API access; no workflow was submitted."
  unless api && catalog && runs && nodes do throw "Remote API checks failed."

end LeanCloudCli
