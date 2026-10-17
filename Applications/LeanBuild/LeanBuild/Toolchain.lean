import LeanCloudRuntime.Process
import LeanCloudRuntime.ProcessLock
import LeanCloudRuntime.Digest

namespace LeanBuild.Toolchain
open Lean LeanCloudRuntime

/-- Pinned by the image builder from the official release's asset digest. -/
structure Release where
  version : String
  platform : String
  sha256 : String
  deriving ToJson, FromJson

def Release.validate (release : Release) : Except String Unit := do
  let [major, minor, patch] := release.version.splitOn "." | throw "Invalid toolchain release"
  let some major := major.toNat? | throw "Invalid toolchain release"
  let some minor := minor.toNat? | throw "Invalid toolchain release"
  let some patch := patch.toNat? | throw "Invalid toolchain release"
  unless release.version == s!"{major}.{minor}.{patch}" &&
      (major > 4 || (major == 4 && minor >= 35)) &&
      ["linux", "linux_aarch64"].contains release.platform &&
      release.sha256.length == 64 && release.sha256.toList.all
        (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) do
    throw "Invalid pinned toolchain release"

private def run (directory : System.FilePath) (command : String) (args : Array String) : IO Unit := do
  let result ← Process.runFiles { cmd := command, args }
    660000 (directory / "install.stdout") (directory / "install.stderr") (1024 * 1024)
  unless !result.stopped && result.exitCode == 0 do
    throw (IO.userError s!"Toolchain installation failed: {result.stderr.takeEnd 4000}")

/-- Publish an installation only after checksum, extraction, and helper checks.
The lock and staging directory also cover interrupted or competing startups. -/
def ensure (release : Release) (cache helper : System.FilePath)
    (download : String → System.FilePath → IO Unit) : IO System.FilePath := do
  IO.ofExcept release.validate
  IO.FS.createDirAll cache
  let lock ← ProcessLock.acquire (cache / s!"{release.sha256}.lock").toString
  try
    let installed := cache / release.sha256
    let marker := (toJson release).compress
    if ← (installed / ".lean-build-ready").pathExists then
      unless (← IO.FS.readFile (installed / ".lean-build-ready")) == marker &&
          (← (installed / "bin/lean").pathExists) && (← (installed / "bin/lake").pathExists) do
        throw (IO.userError "Incomplete cached toolchain")
      return installed
    let staging := cache / s!"{release.sha256}.pending"
    if ← staging.pathExists then IO.FS.removeDirAll staging
    IO.FS.createDir staging
    try
      let archive := staging / "release.tar.zst"
      let name := s!"lean-{release.version}-{release.platform}"
      IO.eprintln s!"Downloading Lean {release.version} ({release.platform})…"
      download s!"https://github.com/leanprover/lean4/releases/download/v{release.version}/{name}.tar.zst" archive
      unless (← Digest.file archive.toString) == release.sha256 do
        throw (IO.userError "Lean toolchain checksum mismatch")
      let unpacked := staging / "unpacked"
      IO.FS.createDir unpacked
      run staging "tar" #["--zstd", "-xf", archive.toString, "--strip-components=1", "-C", unpacked.toString]
      let version ← IO.Process.output { cmd := (unpacked / "bin/lean").toString, args := #["--version"] }
      unless version.exitCode == 0 && version.stdout.startsWith s!"Lean (version {release.version}," do
        throw (IO.userError "Downloaded toolchain has the wrong version")
      run staging (unpacked / "bin/lean").toString #[helper.toString]
      IO.FS.writeFile (unpacked / ".lean-build-ready") marker
      if ← installed.pathExists then IO.FS.removeDirAll installed
      IO.FS.rename unpacked installed
      IO.eprintln s!"Lean {release.version} is ready."
      return installed
    finally
      if ← staging.pathExists then IO.FS.removeDirAll staging
  finally ProcessLock.release lock

def fromFile (spec cache helper : System.FilePath) : IO System.FilePath := do
  let release : Release ← IO.ofExcept (Json.parse (← IO.FS.readFile spec) >>= fromJson?)
  ensure release cache helper fun url output =>
    run output.parent.get! "curl" #["--fail", "--location", "--silent", "--show-error",
      "--retry", "3", "--connect-timeout", "20", "--max-time", "600", "--retry-max-time", "600",
      "--output", output.toString, url]

end LeanBuild.Toolchain
