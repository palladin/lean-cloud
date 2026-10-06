import LeanCloud.Timing
import Std.Time

namespace LeanCloudCli.Time
open Std.Time LeanCloud

private def digits (width value : Nat) : String :=
  let text := toString value
  String.ofList (List.replicate (width - text.length) '0') ++ text

def duration (milliseconds : Nat) : String :=
  let seconds := milliseconds / 1000
  if milliseconds < 1000 then s!"{milliseconds}ms"
  else if seconds < 60 then s!"{seconds}.{digits 3 (milliseconds % 1000)}s"
  else if seconds < 3600 then s!"{seconds / 60}m{digits 2 (seconds % 60)}s"
  else if seconds < 86400 then s!"{seconds / 3600}h{digits 2 (seconds / 60 % 60)}m"
  else s!"{seconds / 86400}d{digits 2 (seconds / 3600 % 24)}h"

def stamp (milliseconds : Nat) : String :=
  let format : GenericFormat .any := datespec("uuuu-MM-dd HH:mm:ss")
  format.format (DateTime.ofTimestampWithZone
    (Timestamp.ofMillisecondsSinceUnixEpoch (.ofInt milliseconds)) TimeZone.UTC)

def elapsed (span : Option Timing.Span) (now : Nat) : String :=
  span.map (fun span => duration (span.elapsed now)) |>.getD "—"

end LeanCloudCli.Time
