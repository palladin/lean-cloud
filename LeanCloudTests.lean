import LeanCloudTests.Differential
import LeanCloudTests.Generated
import LeanCloudTests.Replay
import LeanCloudTests.Codecs
import LeanCloudTests.Backends
import LeanCloudTests.Pure
import LeanCloudTests.WorkQueue

namespace LeanCloudTests

def allCases : Array TestCase :=
  differentialCases ++ pureComputationCases ++ backendCases ++ codecCases ++ generatedCases ++ smallCompositions ++ replayCases ++
  Queue.cases ++ Queue.generatedCases

end LeanCloudTests
