import LeanCloudTests.Generated
import LeanCloudTests.Coordination
import LeanCloudTests.Codecs
import LeanCloudTests.ProofExamples
import LeanCloudTests.ProgressWitness
import LeanCloudTests.SequentialReplay
import LeanCloudTests.Replay
import LeanCloudTests.Console
import LeanCloudTests.Styled
import LeanCloudTests.ConsoleEffects
import LeanCloudTests.Shell
import LeanCloudTests.Project
import LeanCloudTests.DeploymentCommands
import LeanCloudTests.Streaming
import LeanCloudTests.ProcessLogging
import LeanCloudTests.Top
import LeanCloudTests.Help
import LeanCloudTests.Pool

namespace LeanCloudTests

def allCases : Array TestCase := codecCases ++ mailboxCases ++ coordinationCases ++ simulationBoundaryCases ++
  crashBoundaryCases ++ generatedCases ++ compositionCases ++ blobFailureCases ++ sequentialReplayCases ++ replayCases ++ consoleCases ++ styledCases ++ consoleEffectCases ++ shellCases ++ projectCases ++ deploymentCommandCases ++ streamingCases ++ processLoggingCases ++ topCases ++ helpCases ++ poolCases

end LeanCloudTests
