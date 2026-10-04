import LeanEff.Core
import Lean

namespace LeanCloudCli
open LeanEff

structure ProcessOutput where
  exitCode : UInt32 := 0
  stdout : String := ""
  stderr : String := ""
  deriving Inhabited, BEq, Repr

/-- A handle owned by the host handler, not an IO value in the CLI program. -/
structure LockId where
  value : Nat
  deriving BEq, Repr

structure ProcessId where
  value : Nat
  deriving BEq, Repr

/-- Bounded byte chunks; completion is reported after both output pipes drain. -/
structure ProcessChunk where
  stdout : ByteArray := ByteArray.empty
  stderr : ByteArray := ByteArray.empty
  exitCode : Option UInt32 := none


/-- The CLI's host boundary. Requests contain data, never arbitrary IO actions. -/
inductive HostOp : Type → Type where
  | process (command : String) (args : Array String) (input : Option String) : HostOp ProcessOutput
  | startProcess (command : String) (args : Array String) : HostOp ProcessId
  | pollProcess (id : ProcessId) (timeoutMs : UInt32) : HostOp ProcessChunk
  | closeProcess (id : ProcessId) : HostOp Unit
  | readFile (path : System.FilePath) : HostOp String
  | writeFile (path : System.FilePath) (text : String) : HostOp Unit
  | rename (source target : System.FilePath) : HostOp Unit
  | exists (path : System.FilePath) : HostOp Bool
  | readDir (path : System.FilePath) : HostOp (Array String)
  | isDir (path : System.FilePath) : HostOp Bool
  | createDir (path : System.FilePath) : HostOp Unit
  | realPath (path : System.FilePath) : HostOp System.FilePath
  | currentDir : HostOp System.FilePath
  | getEnv (name : String) : HostOp (Option String)
  | pid : HostOp UInt32
  | now : HostOp Nat
  | sleep (milliseconds : UInt32) : HostOp Unit
  | write (text : String) (stderr : Bool := false) : HostOp Unit
  | flush : HostOp Unit
  | readLine : HostOp String
  | enterTerminal : HostOp Bool
  | leaveTerminal : HostOp Unit
  | key (timeoutMs : UInt32) : HostOp UInt32
  | dimensions : HostOp (Nat × Nat)
  | lock (path : System.FilePath) : HostOp LockId
  | unlock (id : LockId) : HostOp Unit

/-- Host failures are responses so CLI catch/finally works with every handler. -/
inductive Host : Effect where
  | request (operation : HostOp α) : Host (Except String α)

abbrev Cli := ExceptT String (Eff [Host])

def request (operation : HostOp α) : Cli α :=
  ExceptT.mk (send (Host.request operation))

def printLine (text : String) : Cli Unit := request (.write (text ++ "\n"))
def printError (text : String) : Cli Unit := request (.write (text ++ "\n") true)

/-- Cleanup is part of the effect program and also runs after a host failure.
    As with IO, a cleanup failure takes precedence over the original failure. -/
instance : MonadFinally Cli where
  tryFinally' action finalizer := ExceptT.mk do
    let result ← action.run
    let cleanup ← (finalizer result.toOption).run
    return match cleanup with
      | .error error => .error error
      | .ok value => result.map (fun result => (result, value))

def withLock (path : System.FilePath) (action : Cli α) : Cli α := do
  let handle ← request (.lock path)
  try action finally request (.unlock handle)

namespace Cli

/-- Interpret the same CLI using any host algebra, including a pure state model. -/
partial def runWith [Monad m] (handle : {α : Type} → HostOp α → m (Except String α))
    (program : Cli α) : m (Except String α) := do
  match program.run with
  | .pure result => return result
  | .impure (.here (.request operation)) next =>
    let result ← handle operation
    runWith handle (ExceptT.mk (ArrsF.apply next result))
  | .impure (.there rest) _ => nomatch rest

end Cli
end LeanCloudCli
