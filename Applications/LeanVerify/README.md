# LeanVerify

Check a Lean project from GitHub using lean-cloud. Give it a repository, a revision,
and the modules or theorems you want checked. Independent modules run on different
workers; checked module artifacts and diagnostics are saved in global blob storage.

```json
{
  "repository": "https://github.com/leanprover-community/batteries",
  "revision": "66e469188fe07963e5cf666c7d4433f45b8131c5",
  "modules": ["Batteries.Data.Nat.Bisect", "Batteries.Data.Nat.Bitwise.Lemmas"],
  "theorems": ["Nat.avg_comm"]
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
5. Export that module's safe declarations, including private declarations, and their
   dependencies using Lean's exporter. Run `lake check --from-export=...` on the
   resulting NDJSON. The checking process reads the export, not project `.olean` files.
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
entry per module, the source snapshot and the allowed axioms. Each entry identifies
its status, diagnostics, output manifest, and any requested theorems and their
axiom dependencies. Each checked module also
has an `exportFile` blob reference containing exactly the export accepted by
`lake check`. The report records the checker and whether `paranoid` mode was used.
Output manifests contain content-addressed file references for `.olean`, its companions, and other Lake
artifacts. Checks reject changes to restored prerequisite artifacts and conflicting
artifacts from different modules.

Add `"paranoid": true` to the request to require all bundled additional checkers:
`leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, and `con-ron`.
Any checker rejection or inability to run fails the module; no checker is skipped.

Plain `lake check` operates on a project's default targets. LeanVerify uses its
`--from-export` interface to preserve the requested module selection and distributed
jobs. Each module export includes its declaration dependencies, so shared dependencies
are rechecked across jobs. This costs more than a single whole-project check.

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
Source projects must use a stable **Lean 4.35.0 or later** release. `checker-toolchain`
selects the default image toolchain, currently **4.35.0**. To build for another release,
pass its exact version as the second argument to `build.sh`:

```sh
bash Applications/LeanVerify/build.sh lean-cloud-verify:dev 4.35.0
```

The source project's version must match the image's checker exactly; LeanVerify
does not rewrite its `lean-toolchain`. The image build type-checks the helper with
the selected release to detect API changes. **4.35.0 is currently tested**; accepting
a newer version does not guarantee its compatibility. Test its export/check pipeline
before deployment. The worker SDK uses its separate, pinned `lean-toolchain`.

This checks **trusted project source**. Lake configuration, build scripts, plugins,
and Lean metaprograms execute code. Run only repositories you trust in a dedicated
worker deployment: a temporary workspace and cleared subprocess environment are
not a security sandbox. The default image explicitly sets `LEAN_VERIFY_SANDBOX=0`
and invokes `lake check --inadvisably-no-sandbox`, without requiring Docker hosts
to permit the nested namespaces used by bubblewrap. This retains the application's
trusted-source boundary; it does not provide Lake's complete sandboxed build pipeline.

On Linux hosts configured for bubblewrap, set `LEAN_VERIFY_SANDBOX=1` to sandbox the
export checkers. Outside the supplied image this is the default. Failure to start
the sandbox is an error, never a fallback to unsandboxed checking. Source preparation
and compilation still require a trusted repository in either mode.

The default verification uses Lean's own kernel; `paranoid` adds other kernels and
the hardened Lean checker. Neither mode compares theorem statements with an external
specification, as Comparator does. An export alone does not establish source provenance:
the report ties it to the resolved commit, source snapshot, module and build artifacts.

Project source modules in the requested closure are built and checked. Toolchain
declarations referenced by their exports are rechecked too. Native support code,
unsafe implementations and compiler correctness are not certified by this application.
The only permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`, matching
`lake check`. `allowedAxioms` may restrict that set, including `[]` for no axioms;
it cannot extend it. `sorryAx` is always rejected in checked declarations, including
private ones. Unsafe runtime declarations are excluded, as in Lean's exporter.

The request's optional `limits` controls per-command `seconds` (default 600),
`checkerMemoryMiB` (4096), total source/output `bytes` (2 GiB per snapshot or job),
and the module count (10,000). Each NDJSON export is also bounded by `bytes`.
Each command's diagnostic output is capped at 16 MiB
per stream. Use container memory and disk quotas for hard limits on Lake, native
build tools, and temporary files; the checker memory option covers the helper only.

Public GitHub HTTPS repositories, ordinary Lake layouts, and dependencies contained
inside the snapshot are supported. File symlinks within the checkout are materialized
as ordinary files in the snapshot. Directory links, external symlinks, Git submodules,
and source dependencies outside the checkout are rejected. Large Mathlib/FLT-scale
performance has **not** been validated. Batches have barriers, and workers currently restore temporary
workspaces rather than keeping imported environments resident.

## Tests

```sh
cd Applications/LeanVerify
elan toolchain install "$(cat checker-toolchain)"
export LEAN_VERIFY_TOOLCHAIN="$(elan run "$(cat checker-toolchain)" lean --print-prefix)"
export LEAN_VERIFY_HELPER="$PWD/Helper.lean"
# Trusted test fixtures; also works on macOS without Linux namespaces.
export LEAN_VERIFY_SANDBOX=0
lake build cloud_app verify_local verify_tests
.lake/build/bin/verify_tests --native
```

Tests compare direct and replay execution on generated dependency graphs, check
replay reuse and failure propagation, and invoke the real compiler/kernel on a
diamond project. Tests also recheck published exports, corrupt a proof in valid NDJSON,
and exercise all paranoid checkers. They also verify modules containing unsafe/partial
runtime code and record source/artifact publication exceptions as execution failures,
without automatic retry or a false proof rejection. Negative cases cover invalid proofs, private
`sorry`, disallowed axioms, missing or non-theorem declarations, and toolchain mismatch.

The optional container test fetches a pinned GitHub project and submits it through
the normal HTTP client to three workers. It cleans up its own deployment on exit:

```sh
bash Applications/LeanVerify/test-deployment.sh lean-cloud-verify:dev
```
