# lean-cloud

[![CI](https://github.com/palladin/lean-cloud/actions/workflows/ci.yml/badge.svg)](https://github.com/palladin/lean-cloud/actions/workflows/ci.yml)
[![Lean 4](https://img.shields.io/badge/Lean-%E2%89%A5%204.35.0-blue)](https://leanprover.github.io/)
[![License: MIT](https://img.shields.io/badge/License-MIT-green)](LICENSE)

Parallel and distributed programming for Lean using the `Cloud` monad.

Write workflows with `cloud { ... }`, run independent computations with
`Cloud.parallel`, and combine their results using ordinary Lean code. Parallel
branches can use variables from their surrounding scope. The same workflow runs
on local workers or in the cloud.

For example, count error lines across log files in shared blob storage:

```lean
import LeanCloud

open LeanCloud

def summarizeLogs (files : Array String) : Cloud IO BlobRef := cloud {
  let counts ← Cloud.parallel (files.map fun name => cloud {
    let text ← CloudBlob.readTextByName name
    return ((text.splitOn "\n").filter (·.startsWith "ERROR")).length
  })

  let total := counts.foldl (· + ·) 0
  CloudBlob.putText s!"files={files.size}, errors={total}\n"
}
```

Each branch reads one file and counts its errors. The workflow combines the
counts and saves a report. Its type, `Cloud IO BlobRef`, tells us that the result
is a reference to that report in blob storage.

- [Run locally with Docker](deploy/README.md#local-docker)
- [Deploy and run the example on Azure](deploy/Azure.md)
- [Run your first log-processing workflow](deploy/README.md#run-the-log-processing-example)
