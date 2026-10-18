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
import LeanCloudTests.Shell
import LeanCloudTests.Top
import LeanCloudTests.Help
import LeanCloudTests.Pool
import LeanCloudTests.PoolModel
import LeanCloudTests.Source
import LeanCloudTests.Stress
import LeanCloudTests.ExecutionConfig
import LeanCloudTests.DeploymentApi
import LeanCloudTests.Environment

namespace LeanCloudTests

def allCases : Array TestCase := codecCases ++ mailboxCases ++ coordinationCases ++ simulationBoundaryCases ++
  crashBoundaryCases ++ generatedCases ++ compositionCases ++ blobFailureCases ++ replayDriverCases ++ RestartingReplay.cases ++ replayCases ++ consoleCases ++ BranchTree.cases ++ Timing.cases ++ styledCases ++ shellCases ++ topCases ++ helpCases ++ poolCases ++ PoolModel.cases ++ Source.cases ++ Stress.cases ++ ExecutionConfig.cases ++ DeploymentApi.cases ++ Environment.cases

end LeanCloudTests
