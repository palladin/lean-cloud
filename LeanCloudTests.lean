import LeanCloudTests.Generated
import LeanCloudTests.Coordination
import LeanCloudTests.Codecs
import LeanCloudTests.ProofExamples
import LeanCloudTests.ProgressWitness
import LeanCloudTests.SequentialReplay

namespace LeanCloudTests

def allCases : Array TestCase := codecCases ++ mailboxCases ++ coordinationCases ++ simulationBoundaryCases ++
  crashBoundaryCases ++ generatedCases ++ compositionCases ++ sequentialReplayCases

end LeanCloudTests
