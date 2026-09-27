import LeanCloudTests.Differential
import LeanCloudTests.Generated
import LeanCloudTests.Replay
import LeanCloudTests.Codecs
import LeanCloudTests.Backends
import LeanCloudTests.WorkQueue

namespace LeanCloudTests

def allCases : Array TestCase :=
  differentialCases ++ backendCases ++ codecCases ++ generatedCases ++ smallCompositions ++ replayCases ++
  Queue.cases ++ Queue.generatedCases

end LeanCloudTests
