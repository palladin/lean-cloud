import LeanCloudTests.Generated
import LeanCloudTests.Coordination
import LeanCloudTests.Codecs
import LeanCloudTests.ProofExamples
import LeanCloudTests.ReplayDrivers
import LeanCloudTests.RestartingReplay
import LeanCloudTests.Replay
import LeanCloudTests.Console
import LeanCloudTests.BranchTree
import LeanCloudTests.Timing
import LeanCloudTests.Styled
import LeanCloudTests.ConsoleEffects
import LeanCloudTests.Shell
import LeanCloudTests.Project
import LeanCloudTests.DeploymentCommands
import LeanCloudTests.Clean
import LeanCloudTests.Streaming
import LeanCloudTests.ProcessLogging
import LeanCloudTests.Top
import LeanCloudTests.Help
import LeanCloudTests.Pool
import LeanCloudTests.PoolModel
import LeanCloudTests.Source
import LeanCloudTests.Stress
import LeanCloudTests.ExecutionConfig
import LeanCloudTests.Backup

namespace LeanCloudTests

def allCases : Array TestCase := codecCases ++ mailboxCases ++ coordinationCases ++ simulationBoundaryCases ++
  crashBoundaryCases ++ generatedCases ++ compositionCases ++ blobFailureCases ++ replayDriverCases ++ RestartingReplay.cases ++ replayCases ++ consoleCases ++ BranchTree.cases ++ Timing.cases ++ styledCases ++ consoleEffectCases ++ shellCases ++ projectCases ++ deploymentCommandCases ++ Clean.cases ++ streamingCases ++ processLoggingCases ++ topCases ++ helpCases ++ poolCases ++ PoolModel.cases ++ Source.cases ++ Stress.cases ++ ExecutionConfig.cases ++ Backup.cases

end LeanCloudTests
