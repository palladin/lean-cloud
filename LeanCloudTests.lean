import LeanCloudTests.Differential
import LeanCloudTests.Generated
import LeanCloudTests.Replay
import LeanCloudTests.Codecs
import LeanCloudTests.Backends
import LeanCloudTests.Pure
import LeanCloudTests.WorkQueue
import LeanCloudTests.Crash
import LeanCloudTests.LeaseQueue
import LeanCloudTests.LeasedReplay
import LeanCloudTests.JournalDb

namespace LeanCloudTests

def allCases : Array TestCase :=
  differentialCases ++ pureComputationCases ++ backendCases ++ codecCases ++ generatedCases ++ smallCompositions ++ replayCases ++
  Queue.cases ++ Queue.generatedCases ++ Crashes.cases ++ Crashes.generatedCases ++ Leases.cases ++
  LeasedReplay.cases ++ LeasedReplay.generatedCases ++ ImmutableJournal.cases

end LeanCloudTests
