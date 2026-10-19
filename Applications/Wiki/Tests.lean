import Wiki.Command
import LeanCloud.SequentialReplay
import Std.Sync.Mutex

open Lean LeanCloud LeanCloudRuntime Wiki

private def check (p : Bool) (message : String) : IO Unit :=
  unless p do throw (IO.userError message)

private def rejects (action : IO α) (message : String) : IO Unit := do
  let failed ← try discard action; pure false catch _ => pure true
  check failed message

private def objects (ref : Std.Mutex (Std.HashMap String ByteArray)) : ObjectStore where
  ensureContainer := pure ()
  read key := ref.atomically do return (← get)[key]?
  create key bytes := ref.atomically do
    if let some old := (← get)[key]? then return old
    modify (·.insert key bytes)
    return bytes
  erase key := ref.atomically do modify (·.erase key)
  list _ := return #[]

private def journal (ref : Std.Mutex (List (String × ReplayRecord))) : ReplayStore IO where
  read key := ref.atomically do return (← get).lookup key
  create key value := ref.atomically do
    if let some old := (← get).lookup key then return old
    modify ((key, value) :: ·)
    return value

/-- Same worker step, concurrently dispatched child assignments. This exercises
real IO effects and the production replay interpreter without HTTP infrastructure. -/
private def dispatch [Codec α] (store : ReplayStore IO) (blobs : BlobStorage IO)
    (program : Cloud IO α) : Nat → Assignment → ExceptT CloudError IO Unit
  | 0, _ => throw ⟨.protocol, "Test fuel exhausted"⟩
  | fuel + 1, assignment => do
    match ← ReplayInterpreter.step store blobs 10000 (fun _ : Unit => program) () assignment
        (environment := { currentWorker := { cpus := 2 }, workers := #[{ cpus := 2 }, { cpus := 2 }] }) with
    | .done => pure ()
    | .fork location count =>
      let jobs ← (List.range count).mapM fun i =>
        liftM (IO.asTask ((dispatch store blobs program fuel ⟨0, location.child i⟩).run))
      -- Drain all children before propagating an independent worker stop.
      let outputs ← liftM (jobs.mapM fun job => IO.wait job : IO _)
      for output in outputs do
        let result ← liftM (IO.ofExcept output)
        liftExcept result
      dispatch store blobs program fuel ⟨0, assignment.branchStart⟩

private def concurrent [Codec α] (store : ReplayStore IO) (blobs : BlobStorage IO)
    (program : Cloud IO α) : IO α := do
  let result ← (dispatch store blobs program 100 ⟨0, Location.root⟩).run
  let .ok () := result | throw (IO.userError s!"Concurrent worker failed: {repr result}")
  let .ok (some outcome) ← store.outcome.run | throw (IO.userError "Missing root")
  IO.ofExcept ((← (ReplayInterpreter.result outcome : ExceptT CloudError IO α).run).mapError (·.message))

private def direct (store : ObjectStore) (program : Cloud IO α) : IO α := do
  match ← (DirectInterpreter.Internal.eval store.storage program {
    currentWorker := { cpus := 4 }, workers := #[{ cpus := 4 }, { cpus := 4 }] }).run with
  | .ok value => return value
  | .error e => throw (IO.userError e.message)

private def compress (path : System.FilePath) (text : String) : IO ByteArray := do
  IO.FS.writeFile path text
  let out ← IO.Process.output { cmd := "bzip2", args := #["-k", "-f", path.toString] }
  check (out.exitCode == 0) "Cannot create compressed fixture"
  IO.FS.readBinFile (System.FilePath.mk (path.toString ++ ".bz2"))

private def nativeTests (store : ObjectStore) : IO Unit := IO.FS.withTempDir fun root => do
  let request ← Import.document store "fixtures/tiny.xml"
  let b := backend store
  let prepared ← direct store (prepare b request)
  check (prepared.articles == 3 && prepared.shards == 1) "Default namespace/redirect filtering"
  let r : CountRequest := { dataset := prepared.dataset, vocabulary := #["proof", "theorem", "algorithm", "computer", "absent"] }
  let decoded : CountRequest ← IO.ofExcept (fromJson? (Json.mkObj [
    ("dataset", toJson prepared.dataset), ("vocabulary", toJson #["proof"])]))
  check decoded.ignoreCase "Request defaults were lost"
  check ({ r with vocabulary := #["Proof", "proof"] }.validate.toOption.isNone) "Folded duplicate vocabulary accepted"
  check ({ r with vocabulary := #["two words"] }.validate.toOption.isNone) "Invalid vocabulary accepted"
  let escaped : GrepRequest := { dataset := prepared.dataset, pattern := "\\\\1", regex := true }
  IO.ofExcept escaped.validate
  let escapedMatcher ← Native.matcher escaped.pattern true false
  check ((← Native.find escapedMatcher "x\\1") == some (1, 2)) "Escaped backslash was mistaken for a back reference"
  check ({ escaped with pattern := "(a)\\1" }.validate.toOption.isNone) "Regex back reference accepted"
  let registry : Registry := ⟨Wiki.programs (throw (IO.userError "Registry must not connect to storage"))⟩
  IO.ofExcept registry.validate
  for p in registry.programs do check (!p.info.sources.isEmpty) "Missing workflow source view"
  let counted ← direct store (count b r)
  check (counted.articles == 3 && counted.counts.map (·.occurrences) == #[4, 1, 2, 1, 0] &&
    counted.counts.map (·.articles) == #[2, 1, 2, 1, 0]) "Wrong counts (XML entity/CDATA/token handling)"
  -- Force cuts inside JSON, UTF-8 and individual article lines. The cloud
  -- reader must repair them exactly once using lean-reducers' byte source.
  let ranged := backendWith (pure store) 17
  check ((← direct store (count ranged r)) == counted) "Byte-range count differs from whole-shard count"
  let dataset ← b.dataset prepared.dataset
  -- Expiry during source setup must stop before the first blob request,
  -- instead of fetching/folding the entire batch and only then failing.
  let reads ← Std.Mutex.new (0 : Nat)
  let observed := { store with read := fun key => do
    reads.atomically (modify (· + 1))
    store.read key }
  let timed := backendWith (do IO.sleep 5; return observed) 17 0
  rejects (direct store (timed.articles dataset).length) "Expired analysis succeeded"
  check ((← reads.atomically get) == 0) "Expired analysis continued fetching blobs"
  let invalid ← Files.putJson store { dataset with source := default }
  rejects (direct store (count b { r with dataset := invalid })) "Invalid dataset provenance accepted"
  let duplicate ← Files.putJson store { dataset with shards := dataset.shards ++ dataset.shards }
  rejects (direct store (count b { r with dataset := duplicate })) "Duplicate shards were counted twice"
  let some shard := dataset.shards[0]? | throw (IO.userError "Missing fixture shard")
  let wrongCounts ← Files.putJson store { dataset with shards := #[{ shard with articles := shard.articles + 1 }] }
  rejects (direct store (count ranged { r with dataset := wrongCounts })) "Range reduction ignored per-file article counts"
  rejects (direct store (grep ranged { dataset := wrongCounts, pattern := "proof" })) "Range grep ignored article counts"
  let corrupt : ObjectStore := { store with read := fun key => do
    let bytes ← store.read key
    if key == shard.file.manifest.key then return some "corrupt".toUTF8
    return bytes }
  rejects (direct corrupt (count (backend corrupt) r)) "Corrupt article artifact accepted"
  let result ← direct store (grep b { dataset := prepared.dataset, pattern := "π proof" })
  check (result.matched == 1) "UTF-8 literal search"
  let manifest : MatchManifest ← Files.readJson store result.results
  let lines ← Files.readText store manifest.parts[0]!.file
  let hit : Hit ← IO.ofExcept (Json.parse lines >>= fromJson?)
  check (hit.id == 2 && hit.length == "π proof".utf8ByteSize && hit.excerpt.startsWith "π proof") "Grep positions/excerpt"
  let regex ← direct store (grep b { dataset := prepared.dataset, pattern := "proof|theorem", regex := true, ignoreCase := true })
  check (regex.matched == 2) "Regex selection"
  let splitRegex ← direct store (grep ranged { dataset := prepared.dataset, pattern := "proof|theorem", regex := true, ignoreCase := true })
  check (splitRegex.matched == regex.matched && splitRegex.articles == regex.articles) "Range grep lost or duplicated articles"
  let expectedParts : MatchManifest ← Files.readJson store regex.results
  let actualParts : MatchManifest ← Files.readJson store splitRegex.results
  let expectedText ← expectedParts.parts.foldlM (fun text part => do return text ++ (← Files.readText store part.file)) ""
  let actualText ← actualParts.parts.foldlM (fun text part => do return text ++ (← Files.readText store part.file)) ""
  check (actualText == expectedText) "Range grep changed output order"
  let perFileLimit := expectedParts.parts.foldl (fun n part => n + part.file.size) 0 - 1
  rejects (direct store (grep ranged { dataset := prepared.dataset, pattern := "proof|theorem", regex := true, ignoreCase := true, maxOutputBytes := perFileLimit })) "Splitting bypassed per-file output limit"
  let empty ← direct store (grep b { dataset := prepared.dataset, pattern := "unlikely absent string" })
  check (empty.matched == 0 && empty.articles == 3) "Empty search"
  rejects (direct store (grep b { dataset := prepared.dataset, pattern := "[", regex := true })) "Invalid regex accepted"
  rejects (direct store (grep b { dataset := prepared.dataset, pattern := "proof", maxOutputBytes := 1 })) "Output limit silently truncated"
  let all ← direct store (prepare b { request with includeRedirects := true })
  check (all.articles == 4) "Redirect option"
  let talk ← direct store (prepare b { request with namespaceId := 1 })
  check (talk.articles == 1) "Namespace option"
  let missing ← direct store (prepare b { request with namespaceId := 99 })
  let zero ← direct store (count b { r with dataset := missing.dataset })
  check (zero.articles == 0 && zero.counts.all (·.occurrences == 0)) "Empty dataset"
  rejects (direct store (grep b { dataset := missing.dataset, pattern := "[", regex := true }))
    "Empty dataset hid an invalid regex"
  let xml ← IO.FS.readFile "fixtures/tiny.xml"
  let sections := xml.splitOn "  <page>"
  let a := sections[0]! ++ "  <page>" ++ sections[1]!
  let middle := "  <page>" ++ sections[2]!
  let c := "  <page>" ++ String.intercalate "  <page>" (sections.drop 3)
  let a ← compress (root / "a") a
  let middle ← compress (root / "b") middle
  let c ← compress (root / "c") c
  let dump := root / "dump.bz2"
  let index := root / "index.txt"
  IO.FS.writeBinFile dump (a ++ middle ++ c)
  -- Repeated offsets and colons in titles are both legal.
  IO.FS.writeFile index s!"0:1:Proof:theorem\n{a.size}:2:Computer\n{a.size + middle.size}:3:Empty\n{a.size + middle.size}:4:Redirect\n"
  let split ← Import.multistream store dump index 1
  let source ← b.source split.source
  check (source.parts.size == 3) "Indexed splitting did not use stream boundaries"
  let preparedSplit ← direct store (prepare b split)
  let splitCounts ← direct store (count b { r with dataset := preparedSplit.dataset })
  check (splitCounts == counted) "Split/unsplit counts differ"
  let grouped ← Import.document store dump
  let preparedGrouped ← direct store (prepare b grouped)
  check ((← direct store (count b { r with dataset := preparedGrouped.dataset })) == counted) "Concatenated bzip2 streams lost pages"
  let indexBytes ← compress (root / "compressed-index") (← IO.FS.readFile index)
  IO.FS.writeBinFile (root / "index.bz2") indexBytes
  discard (Import.multistream store dump (root / "index.bz2") 1)
  -- Test concurrent effects and replay caching using the production worker step.
  let calls ← Std.Mutex.new (0 : Nat)
  let countedBackend := { b with saveCounts := fun value => do calls.atomically (modify (· + 1)); b.saveCounts value }
  let log ← Std.Mutex.new []
  let r := { r with dataset := preparedSplit.dataset }
  let actual ← concurrent (journal log) store.storage (count countedBackend r)
  check (actual == counted) "Concurrent replay differs from direct"
  let before ← calls.atomically get
  discard (concurrent (journal log) store.storage (count countedBackend r))
  check ((← calls.atomically get) == before) "Replay executed recorded analysis again"
  -- Simulate a worker stopping after committing an effect but before its next
  -- journal read: restart the assignment against the surviving journal.
  let crashLog ← Std.Mutex.new []
  let fault ← Std.Mutex.new (0, true)
  let original := journal crashLog
  let crashing := { original with read := fun key => do
    let stop ← fault.atomically do
      let (reads, armed) ← get
      let stop := reads ≥ 4 && armed
      set (reads + 1, armed && !stop)
      return stop
    if stop then throw (IO.userError "injected node stop")
    original.read key }
  rejects (concurrent crashing store.storage (count b r)) "Crash injection did not fire"
  check ((← concurrent original store.storage (count b r)) == counted) "Local restart changed output"
  let afterLog ← Std.Mutex.new []
  let committed := journal afterLog
  let armed ← Std.Mutex.new true
  let afterCommit := { committed with create := fun key value => do
    let recorded ← committed.create key value
    let stop ← armed.atomically do let old ← get; set false; return old
    if stop then throw (IO.userError "node stopped after commit")
    return recorded }
  rejects (concurrent afterCommit store.storage (count b r)) "Post-commit stop did not fire"
  check ((← concurrent committed store.storage (count b r)) == counted) "Post-commit restart changed output"
  -- An exception from the user's effect is a recorded failure, never a crash retry.
  let failedCalls ← IO.mkRef (0 : Nat)
  let failedLog ← Std.Mutex.new []
  let failing := { b with saveCounts := fun _ => do
    failedCalls.modify (· + 1)
    throw (IO.userError "analysis failed") }
  let mut firstCalls := 0
  for attempt in [:2] do
    let result ← (SequentialReplay.interpret (journal failedLog) store.storage 10000 (count failing) r).run
    match result with
    | .ok _ => throw (IO.userError "Analysis exception was lost")
    | .error e => check (e == ⟨.application, "analysis failed"⟩) "Wrong recorded failure"
    if attempt == 0 then firstCalls ← failedCalls.get
    else check ((← failedCalls.get) == firstCalls) "Ordinary IO error was retried"
  check (firstCalls > 0) "No failing effect executed"
  for bad in [xml.replace "</mediawiki>" "", xml.replace "<text />" "<text>&unknown;</text>",
      "<!DOCTYPE mediawiki [<!ENTITY x 'expanded'>]>" ++ xml,
      xml.replace "<text />" "<text deleted=\"deleted\" />"] do
    IO.FS.writeFile (root / "bad.xml") bad
    let badRequest ← Import.document store (root / "bad.xml")
    rejects (direct store (prepare b badRequest)) "Invalid XML accepted"
  IO.FS.writeBinFile (root / "truncated.bz2") ((a ++ middle ++ c).extract 0 (a.size + middle.size + c.size - 8))
  let truncated ← Import.document store (root / "truncated.bz2")
  rejects (direct store (prepare b truncated)) "Truncated bzip2 accepted"
  IO.FS.writeBinFile (root / "garbage.bz2") (a ++ middle ++ c ++ "junk".toUTF8)
  let garbage ← Import.document store (root / "garbage.bz2")
  rejects (direct store (prepare b garbage)) "Trailing compressed garbage accepted"
  IO.FS.writeFile index "20:2:B\n10:1:A\n"
  rejects (Import.multistream store dump index) "Unordered index accepted"
  -- Both decoded fields fit their limits, but escaping tabs makes the combined
  -- NDJSON line exceed the reader's bound. Preparation must reject it itself.
  let oversized := root / "oversized.xml"
  let output ← IO.FS.Handle.mk oversized .write
  let tabs := String.ofList (List.replicate 65536 '\t')
  output.putStr "<mediawiki><page><title>"
  for _ in [:96] do output.putStr tabs
  output.putStr "</title><ns>0</ns><id>1</id><revision><id>1</id><text>"
  for _ in [:96] do output.putStr tabs
  output.putStr "</text></revision></page></mediawiki>"
  output.flush
  let error ← try
    discard (Native.normalize oversized.toString root.toString false true true 0 false MiB.toUInt64)
    pure ""
  catch error => pure error.toString
  check (error == "Encoded article exceeds 64 MiB") "Preparation published an unreadable encoded article"
  IO.println "PASS XML/bzip2 preparation, indexed partitions, count/grep, concurrent replay and restart"

private def generatedTests : IO Unit := do
  let r : CountRequest := { dataset := default, vocabulary := #["proof", "algorithm", "x", "absent"] }
  for seed in [:100] do
    let texts := (Array.range (1 + seed % 17)).map fun i =>
      String.intercalate " " (((List.range (i + seed % 7)).map fun j =>
        ["Proof", "algorithm", "x", "proof!", "xx", "123", "π", "PROOF"][j % 8]!) ++ ["proof"])
    let scanned := texts.map fun text => wordHits (vocabulary r) true text
    -- Independent, deliberately simple reference tokenizer.
    let reference := texts.map fun text => r.vocabulary.map fun word =>
      ((text.toLower.toList.map fun c => if c.isAlpha then c else ' ') |> String.ofList).splitOn " "
        |>.filter (· == word) |>.length
    check (scanned.map (fun hits => (Array.range r.vocabulary.size).map (hits.getD · 0)) == reference)
      "Generated token counts differ from reference"
    let all := scanned.foldl addArticle { counts := r.vocabulary.map fun word => { word } }
    for width in [1, 2, 7, 31] do
      let parts := (Array.range ((scanned.size + width - 1) / width)).map fun i =>
        (scanned.extract (i*width) ((i+1)*width)).foldl addArticle { counts := r.vocabulary.map fun word => { word } }
      check (mergeCounts r parts == all) "Shard boundaries changed counts"
  let literal ← Native.matcher "PROOF" false true
  check ((← Native.find literal "π proof") == some (3, 5)) "ASCII case/UTF-8 byte position"
  let byteRegex ← Native.matcher "." true false
  check ((← Native.find byteRegex "π") == some (0, 1)) "Regex did not use C-locale byte semantics"
  let asciiCase ← Native.matcher "Π" true true
  check ((← Native.find asciiCase "π") == none) "Regex unexpectedly folded non-ASCII letters"
  IO.println "PASS 100 generated corpora and varying shard boundaries"

private def externalDump (store : ObjectStore) (path : String) : IO Unit := do
  let request ← Import.document store path
  let prepared ← direct store (prepare (backend store) { request with shardBytes := MiB })
  let counted ← direct store (count (backend store) { dataset := prepared.dataset, vocabulary := #["the", "proof", "algorithm"] })
  IO.println ((toJson (prepared, counted)).pretty)

def main (args : List String) : IO Unit := do
  let store := objects (← Std.Mutex.new {})
  match args with
  | ["--dump", path] => externalDump store path
  | [] => generatedTests; nativeTests store
  | _ => throw (IO.userError "Usage: wiki_tests [--dump DUMP.xml[.bz2]]")
