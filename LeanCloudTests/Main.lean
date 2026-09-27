import LeanCloudTests

open LeanCloudTests

def main (args : List String) : IO UInt32 := do
  if args == ["--list"] then
    for test in allCases do IO.println test.name
    return 0
  let selected := allCases.filter fun test =>
    args.isEmpty || args.any (fun category => category.isPrefixOf test.name)
  if selected.isEmpty then
    IO.eprintln "No matching tests. Use --list or a test-name prefix."
    return 1
  let mut failed := 0
  for (test, index) in selected.toList.zipIdx do
    try
      test.run
    catch error =>
      failed := failed + 1
      IO.eprintln s!"FAIL {test.name}\n{error}"
    if (index + 1) % 64 == 0 then
      IO.println s!"Checked {index + 1}/{selected.size} tests"
  IO.println s!"{selected.size - failed}/{selected.size} tests passed"
  return if failed == 0 then 0 else 1
