import LeanCloudTests.Differential
import LeanCloudTests.Generated
import LeanCloudTests.Replay
import LeanCloudTests.Codecs
import LeanCloudTests.Backends
import LeanCloudTests.Pure
import LeanCloudTests.PureReplay
import LeanCloudTests.WorkQueue
import LeanCloudTests.Recovery
import LeanCloudTests.LeaseQueue
import LeanCloudTests.LeasedReplay
import LeanCloudTests.JournalDb
import LeanCloudTests.Simulation
import LeanCloudTests.ConcurrentJournal
import LeanCloudTests.ConcurrentRead
import LeanCloudTests.ConcurrentJoin
import LeanCloudTests.ConcurrentPublication
import LeanCloudTests.Worker
import LeanCloudTests.BackendContracts

namespace LeanCloudTests

def allCases : Array TestCase :=
  differentialCases ++ pureComputationCases ++ PureReplay.cases ++ backendCases ++ codecCases ++ generatedCases ++ smallCompositions ++ replayCases ++
  Queue.cases ++ Queue.generatedCases ++ RecoveryTests.cases ++ RecoveryTests.generatedCases ++ Leases.cases ++
  LeasedReplay.cases ++ ImmutableJournal.cases ++
  Simulated.cases ++ Simulated.generatedCases ++ ConcurrentJournal.cases ++ ConcurrentRead.cases ++ ConcurrentJoin.cases ++
  ConcurrentPublication.cases ++ WorkerTests.cases ++ WorkerTests.generatedCases ++ BackendContracts.cases

end LeanCloudTests
