import LeanCloudTests.Generated
import LeanCloudTests.Coordination
import LeanCloudTests.Codecs
import LeanCloudTests.ProofExamples
import LeanCloudTests.ProgressWitness
import LeanCloudTests.SequentialReplay
import LeanCloudTests.Replay
import LeanCloudTests.Console
import LeanCloudTests.ConsoleEffects
import LeanCloudTests.Shell
import LeanCloudTests.Project
import LeanCloudTests.DeploymentCommands
import LeanCloudTests.Streaming

namespace LeanCloudTests

def allCases : Array TestCase := codecCases ++ mailboxCases ++ coordinationCases ++ simulationBoundaryCases ++
  crashBoundaryCases ++ generatedCases ++ compositionCases ++ blobFailureCases ++ sequentialReplayCases ++ replayCases ++ consoleCases ++ consoleEffectCases ++ shellCases ++ projectCases ++ deploymentCommandCases ++ streamingCases

end LeanCloudTests
