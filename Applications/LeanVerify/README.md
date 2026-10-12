# LeanVerify

Check a Lean project from GitHub using lean-cloud. Give it a repository, a revision,
and the modules or theorems you want checked. Independent modules run on different
workers; checked module artifacts and diagnostics are saved in global blob storage.

```json
{
  "repository": "https://github.com/palladin/lean-eff",
  "revision": "a9808ab3964376eedb54a3f9725d2e1c4c9fc800",
  "modules": ["LeanEff"],
  "theorems": []
}
```

`modules` are root modules. Their transitive source dependencies are included,
including Lake packages. `theorems` optionally requires named declarations in that
closure to exist and be theorems. For example, a project with `Final.lean` might use
`"modules": ["Final"]` and `"theorems": ["fermat_last_theorem"]`.

Use an immutable commit for reproducibility. A branch or tag is resolved once
in the preparation step and its actual commit is recorded in the report.

## How it runs

1. Fetch the revision into a private temporary workspace and resolve Lake dependencies.
2. Check the exact `lean-toolchain` and discover the source import graph using Lake.
3. Publish a source snapshot, excluding prebuilt module artifacts.
4. Run a batch of ready modules using `Cloud.parallel`. Each job restores the sources
   and its checked prerequisites into a separate workspace. Lake elaborates the module
   with the project's build options and prepares any required tactic/plugin artifacts.
5. Recheck that module's declarations with Lean's kernel, using the same replay
   operation as the bundled `leanchecker`. Include private/server module companions.
6. Publish the new artifacts and diagnostics. Start the next ready batch.
7. Return a report. A failed module blocks its dependents; unrelated modules still run.

For a diamond dependency graph, the execution is:

```text
Base → parallel [Left, Right] → Final
```

The application uses the existing cloud interpreter and scheduler. Only artifact
references and small job descriptions enter the replay journal. Completed effects
are reused after a worker restart. An interrupted external process may execute again.

The report has `success`, the resolved `commit`, the exact `toolchain`, and one
entry per module, the source snapshot and the allowed axioms. Each entry identifies its status, diagnostics, output manifest,
and any requested theorems and their axiom dependencies. Output manifests contain
content-addressed file references for `.olean`, its companions, and other Lake
artifacts. Checks reject changes to restored prerequisite artifacts and conflicting
artifacts from different modules.

## Local deployment

From the lean-cloud repository:

```sh
bash Applications/LeanVerify/build.sh lean-cloud-verify:dev
bash deploy/local.sh init .lean-cloud/verify lean-cloud-verify:dev verify 3 8080
bash deploy/local.sh up .lean-cloud/verify
lake exe lean_cloud
```

In the cloud console:

```text
connect verify http://127.0.0.1:8080 --token-file .lean-cloud/verify/client.token
programs
run lean-verify --input Applications/LeanVerify/example.json --id proofs
ps
watch proofs
result proofs
```

The same image can be deployed using the Kubernetes helpers or your own deployment
scripts. The console connects to the scheduler over HTTP in either case.

To read a module's diagnostics or artifact manifest, save its file-reference JSON
from the report, then run:

```sh
bash Applications/LeanVerify/local-files.sh .lean-cloud/verify ref.json
```

For a binary artifact use the application's `files download CONFIG REF OUTPUT`
command inside the deployed image and copy `OUTPUT` out. File transfers use the
configured global store and verify lengths and SHA-256 digests.

Remove the temporary deployment, including its stored data:

```sh
bash deploy/local.sh clean .lean-cloud/verify --yes
```

## Toolchains and verification boundary

The worker application and the checked project have separate toolchains. The image
ships the project's toolchain; jobs cannot select executable paths or install tools.
The default image and the checker helper are tested with **Lean 4.34.1**. A different
source toolchain can be installed with the second build argument:

```sh
bash Applications/LeanVerify/build.sh lean-cloud-verify:custom 4.34.1
```

The source project's version must match exactly. Other releases also need compatibility
validation of `Helper.lean`, which uses Lean/Lake APIs. Nightly toolchains are not
currently supported by the image builder.

This checks **trusted project source**. Lake configuration, build scripts, plugins,
and Lean metaprograms execute code. Run only repositories you trust in a dedicated
worker deployment: a temporary workspace and cleared subprocess environment are
not a security sandbox. This is Lean's own kernel rechecking generated artifacts,
not an independent checker or Comparator's adversarial verification protocol.

The pinned toolchain's standard libraries are trusted. Project source modules in the
requested closure are built and checked. Extra native support code needed by Lake is
not certified by this application. By default the only permitted axioms are `propext`,
`Classical.choice`, and `Quot.sound`; supply `allowedAxioms` explicitly for other
assumptions. `sorryAx` is always rejected, including in private declarations.

The request's optional `limits` controls per-command `seconds` (default 600),
`checkerMemoryMiB` (4096), total source/output `bytes` (2 GiB per snapshot or job),
and the module count (10,000). Each command's diagnostic output is capped at 16 MiB
per stream. Use container memory and disk quotas for hard limits on Lake, native
build tools, and temporary files; the checker memory option covers the helper only.

Public GitHub HTTPS repositories, ordinary Lake layouts, and dependencies contained
inside the snapshot are supported. Symlinks, Git submodules, and source dependencies
outside the checkout are rejected. Large Mathlib/FLT-scale performance has **not**
been validated. Batches have barriers, and workers currently restore temporary
workspaces rather than keeping imported environments resident.

## Tests

```sh
cd Applications/LeanVerify
export LEAN_VERIFY_TOOLCHAIN="$(lean --print-prefix)"
export LEAN_VERIFY_HELPER="$PWD/Helper.lean"
lake build cloud_app verify_local verify_tests
.lake/build/bin/verify_tests --native
```

Tests compare direct and replay execution on generated dependency graphs, check
replay reuse and failure propagation, and invoke the real compiler/kernel on a
diamond project. Negative cases cover invalid proofs, `sorry`, missing or non-theorem
declarations, and toolchain mismatch.

The optional container test fetches a pinned GitHub project and submits it through
the normal HTTP client to three workers. It cleans up its own deployment on exit:

```sh
bash Applications/LeanVerify/test-deployment.sh lean-cloud-verify:dev
```
