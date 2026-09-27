import LeanCloudTests.Differential
import LeanCloudTests.Generated
import LeanCloudTests.Replay
import LeanCloudTests.Codecs
import LeanCloudTests.Backends

namespace LeanCloudTests

def allCases : Array TestCase :=
  differentialCases ++ backendCases ++ codecCases ++ generatedCases ++ smallCompositions ++ replayCases

end LeanCloudTests
