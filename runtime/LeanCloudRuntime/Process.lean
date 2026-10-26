import Lean

namespace LeanCloudRuntime.Process

@[extern "lean_cloud_kill_group"]
opaque killGroup (pid : UInt32) : IO Unit

structure Output where
  exitCode : UInt32
  stdout : String
  stderr : String
  stopped : Bool
  deriving Repr

private partial def captureFile (input output : IO.FS.Handle) (limit : Nat)
    (overflow : IO.Ref Bool) (total : Nat := 0) (tail : ByteArray := {}) : IO ByteArray := do
  let bytes ← input.read 65536
  if bytes.isEmpty then output.flush; return tail
  if total + bytes.size > limit then overflow.set true
  try output.write (bytes.extract 0 (limit - total))
  catch error => overflow.set true; throw error
  let tail := tail ++ bytes
  captureFile input output limit overflow (total + bytes.size)
    (tail.extract (tail.size - 65536) tail.size)

private partial def waitFiles (child : IO.Process.Child cfg) (deadline : Nat)
    (overflow : IO.Ref Bool) (files : Array (System.FilePath × Nat))
    (cancelled : IO Bool) : IO (UInt32 × Bool) := do
  for (path, limit) in files do
    if ← path.pathExists then
      if (← path.metadata).byteSize.toNat > limit then overflow.set true
  if let some code ← child.tryWait then return (code, false)
  if (← cancelled) || (← IO.monoMsNow) ≥ deadline || (← overflow.get) then
    killGroup child.pid
    return (← child.wait, true)
  IO.sleep 10
  waitFiles child deadline overflow files cancelled

/-- Process output goes straight to files; only a diagnostic tail is held in RAM.
Monitored artifact limits stop the process group; final sizes are checked again
before uploading. Container storage/memory quotas remain the hard OS boundary. -/
def runFiles (args : IO.Process.SpawnArgs) (milliseconds : Nat)
    (stdoutPath stderrPath : System.FilePath) (logLimit : Nat)
    (files : Array (System.FilePath × Nat) := #[]) (cancelled : IO Bool := pure false) : IO Output := do
  let outFile ← IO.FS.Handle.mk stdoutPath .write
  let errFile ← IO.FS.Handle.mk stderrPath .write
  let child ← IO.Process.spawn { args with stdin := .null, stdout := .piped, stderr := .piped, setsid := true }
  let reaped ← IO.mkRef false
  let overflow ← IO.mkRef false
  let stdout ← IO.asTask (captureFile child.stdout outFile logLimit overflow) .dedicated
  let stderr ← IO.asTask (captureFile child.stderr errFile logLimit overflow) .dedicated
  try
    let (code, stopped) ← waitFiles child ((← IO.monoMsNow) + milliseconds) overflow files cancelled
    reaped.set true
    -- A normally exited command may leave descendants holding its pipes.
    -- The stopped path already killed the group before reaping the child.
    unless stopped do killGroup child.pid
    let out ← IO.ofExcept stdout.get
    let err ← IO.ofExcept stderr.get
    return { exitCode := code, stdout := (String.fromUTF8? out).getD "Non-UTF8 tool output", stderr := (String.fromUTF8? err).getD "Non-UTF8 tool error"
             stopped := stopped || (← overflow.get) }
  finally
    unless ← reaped.get do
      killGroup child.pid
      discard child.wait
    try discard <| IO.ofExcept stdout.get catch _ => pure ()
    try discard <| IO.ofExcept stderr.get catch _ => pure ()

end LeanCloudRuntime.Process
