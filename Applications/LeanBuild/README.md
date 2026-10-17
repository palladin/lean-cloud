# LeanBuild

Build a Lean project from GitHub on lean-cloud. Give it a repository, revision,
and Lake targets. Independent modules build on different workers; the completed
workspace, executables, and diagnostics are saved in blob storage.

```json
{
  "repository": "https://github.com/leanprover-community/batteries",
  "revision": "66e469188fe07963e5cf666c7d4433f45b8131c5",
  "targets": ["+Batteries.Data.Nat.Bisect", "+Batteries.Data.Nat.Bitwise.Lemmas"]
}
```

Omit `targets` (or use `[]`) to build the project's default Lake targets.
Use the same target names as `lake build`: for example `Mathlib`, `my_executable`,
`+My.Module:olean`, or `@dependency/Library`. Custom targets are supported too.
A branch or tag is resolved once; the actual commit is recorded in the result.
Use a commit hash when you want repeatable inputs.

## Request options

| Field | Meaning | Default |
| --- | --- | --- |
| `repository`, `revision` | Public GitHub HTTPS URL and Git revision | Required |
| `targets` | Arguments to `lake build` | Project's default targets |
| `subdirectory` | Lake project directory within the repository | `"."` |
| `options` | Lake configuration values, e.g. `{"feature": "enabled"}` passes `-Kfeature=enabled` | `{}` |
| `cache` | `"rebuild"` clears package build directories during preparation and disables external Lake artifact caches; `"reuse"` allows Lake's cache support | `"rebuild"` |
| `check` | Optional independent proof checking, described below | `{"mode": "none"}` |
| `limits` | Per-command and artifact limits | See below |

Native tools and system libraries belong in the deployment image. Jobs use the
project's exact Lean version and the worker's OS/architecture. The request does
not install toolchains or select a different execution platform.

## How it runs

1. Fetch the revision, load the Lake project, and resolve its dependencies and
   declared generated-source prerequisites. Publish the resolved source workspace.
2. Discover the module dependency graph for ordinary module, library, and
   executable targets using Lake's APIs.
3. Build ready modules with `Cloud.parallel`. Each job restores the sources and
   its prerequisites into a private workspace and publishes its new artifacts.
4. Restore those artifacts and pass **the original target list** to Lake's own
   build engine, the same one used by `lake build`.
   Lake completes native compilation, C FFI, linking, custom targets, and dynamic
   dependencies. Publish the complete workspace as one file manifest.
5. If requested, export the built modules together and run `lake check` once.

For a diamond dependency graph:

```text
prepare → Base → parallel [Left, Right] → Final → complete Lake targets → optional check
```

The module stage is distributed. The final target build and proof check each run
on one worker; Lake retains its own local parallelism. Custom targets and unusual
facets are delegated to that final build rather than guessing their dependencies.
Build hooks must work in a relocated workspace and declare their dependencies to
Lake. Module jobs preserve the prepared inputs and their prerequisites. Differing
artifacts produced at the same path by parallel jobs are rejected.

Only job inputs and artifact references enter the replay journal. Completed jobs
are reused after a worker crash. An interrupted job may execute again. A build
error, checker rejection, or ordinary IO exception is a failure outcome, not a
node-crash retry.

## Optional proof checking

Builds already elaborate Lean source and run its kernel. Independent checking is
an additional step; enable it with:

```json
"check": {
  "mode": "kernel",
  "theorems": ["Nat.avg_comm"],
  "allowedAxioms": ["propext", "Classical.choice", "Quot.sound"]
}
```

`kernel` checks a combined NDJSON export using `lake check --from-export`.
`paranoid` additionally requires all bundled checkers (`leanchecker-paranoid`,
`lean4lean`, `nanoda`, `con-leche`, and `con-ron`). No requested checker is skipped.
The export includes safe private declarations and their dependencies; shared
proof dependencies are exported once. The checker reads NDJSON, not `.olean` files.
Its module selection comes from Lake's build jobs, so unrelated files in a reused
cache do not enter the check. Custom targets should express their Lean dependencies
as Lake jobs for those modules to appear in the verification result.

`theorems` optionally requires particular declarations to exist and be theorems.
`allowedAxioms` defaults to the three shown above and may only restrict that set.
`sorryAx` is rejected during checking, including in private declarations.
A build can succeed while this additional verification fails. Build-only mode
preserves Lake's normal behavior, including its warnings about `sorry`.

This does not compare theorem statements with an external specification, certify
native code, or verify unsafe implementations and compiler correctness. The
report distinguishes the compiled artifacts from the independently checked export.

## Local deployment and first run

From the lean-cloud repository:

```sh
bash Applications/LeanBuild/build.sh lean-cloud-build:dev
bash deploy/local.sh configure .lean-cloud/build lean-cloud-build:dev build 3 8080
bash deploy/local.sh up .lean-cloud/build
lake exe lean_cloud
```

In the console:

```text
connect build http://127.0.0.1:8080 --token-file .lean-cloud/build/client.token
programs
run lean-build --input Applications/LeanBuild/example.json --id batteries
ps
watch batteries
result batteries
```

The supplied example requests a small pinned Batteries build plus kernel checking.
Remove its `check` field for build-only execution. The same image works with the
[Kubernetes helpers](../../deploy/README.md) and [Azure deployment](../../deploy/Azure.md);
the console uses the same HTTP connection in each environment.

The report contains:

- `commit`, `toolchain`, `platform`, and `source`: exact input provenance.
- `modules`: per-module status, diagnostics, duration, and new artifact manifests.
- `build`: final target status, diagnostics, duration, built modules, and an
  `artifacts` reference to the complete workspace manifest. This includes sources,
  Lake outputs, executables, and custom outputs outside `.lake/build`.
- `verification`: absent unless requested; contains checker mode, success,
  diagnostics, duration, theorem/axiom results, and the accepted `exportFile`.
- `success`: true only when the build and every requested check succeed.

To read diagnostics or a manifest, save its file-reference JSON from the report:

```sh
bash Applications/LeanBuild/local-files.sh .lean-cloud/build ref.json
```

Each workspace manifest entry gives a relative path, a packed-file reference
(pack, byte offset, length, and SHA-256), and an executable flag. Files from one
snapshot share a pack, avoiding a separate remote transfer for each small file.
The application's `files download CONFIG FILE_REF OUTPUT` command downloads a
top-level file reference, such as diagnostics or a workspace manifest;
`files restore CONFIG MANIFEST_REF DIRECTORY` restores the packed workspace into
a new directory. Run these inside the deployed image, where the storage
configuration is available. Transfers verify sizes and SHA-256 hashes.
Native executables require a compatible platform and runtime libraries.

The packed workspace format is used by `lean-build/v2`; old `v1` workspace
manifests require the old application image to restore.

Remove this test deployment and its stored data:

```sh
bash deploy/local.sh clean .lean-cloud/build --yes
```

## Deployment and limits

Source projects need a stable **Lean 4.35.0 or later** release. `source-toolchain`
selects the default image toolchain (currently 4.35.0). To select an exact release:

```sh
bash Applications/LeanBuild/build.sh lean-cloud-build:dev 4.35.0
```

The project's `lean-toolchain` must match the deployed toolchain exactly; it is
never rewritten. The image pins the official release's SHA-256 digest. On first
startup, each worker downloads that release directly from GitHub into
`/data/toolchains`, verifies its checksum, and type-checks the Lake helper before
becoming ready. Restarts reuse the installation. The toolchain is not uploaded
from your laptop as an image layer. First startup needs outbound GitHub access
and roughly 3.2 GB of persistent space for Lean 4.35.0, plus installation scratch
space. For Kubernetes, set `startupSeconds: 900` in `deployment.json` to allow
time for installation. The scheduler does not download a toolchain.

For an existing local installation, set `LEAN_BUILD_TOOLCHAIN` to its directory;
this bypasses downloading. `LEAN_BUILD_RELEASE` identifies the pinned release
JSON and `LEAN_BUILD_TOOLCHAINS` selects the installation cache directory.
**4.35.0 is tested**; future Lake API changes may require helper updates. The
lean-cloud worker SDK has its own separate, pinned toolchain.

Run trusted repositories in dedicated deployments: Lake configuration, build
hooks, plugins and metaprograms execute code. The default image explicitly sets
`LEAN_BUILD_SANDBOX=0` for checking trusted exports without nested namespaces.
Set it to `1` on Linux hosts configured for bubblewrap to sandbox export checking.
An unavailable requested sandbox fails the check; it never silently falls back.
This setting does not sandbox source compilation.

`limits` defaults to `seconds: 600` per command, `checkerMemoryMiB: 4096` for the
helper, `bytes: 2147483648` per workspace/export, and `modules: 10000`.
Each command's diagnostics are capped at 16 MiB per stream. Container CPU, memory,
and disk limits govern native tools and temporary files; the helper's memory
option is not a container memory limit.

Dependencies must be inside the repository snapshot. Internal file symlinks are
materialized; external links, directory links, Git submodules, and dependencies
outside the snapshot are rejected. Snapshot transfers currently restore private
workspaces for each job. The image caches immutable packs in `/data/build-cache`;
each hit is verified and copied, so a job cannot change another job's inputs.
Set `LEAN_BUILD_CACHE` to choose a cache directory and `LEAN_BUILD_CACHE_BYTES`
to bound it (default 4 GiB). Without `LEAN_BUILD_CACHE`, caching is disabled.
Packs larger than the budget use temporary files instead. Provision enough disk
for both the cache and the job's private workspace; the byte limit bounds cached
pack contents, not filesystem overhead or temporary files.

Large Mathlib/FLT performance has not been validated;
batch barriers and artifact transfer costs still apply.

## Tests

```sh
cd Applications/LeanBuild
elan toolchain install "$(cat source-toolchain)"
export LEAN_BUILD_TOOLCHAIN="$(elan run "$(cat source-toolchain)" lean --print-prefix)"
export LEAN_BUILD_HELPER="$PWD/Helper.lean"
export LEAN_BUILD_SANDBOX=0
lake build cloud_app build_local build_tests
.lake/build/bin/build_tests --native
```

Tests compare direct/replay execution on 80 generated module graphs and compare
native executable output with ordinary Lake. Fixtures cover library/default/module
and custom targets, generated sources, C FFI, configuration options, subdirectories,
replay reuse and durable failures. Checking tests cover combined exports, every
paranoid checker, corrupt proofs, private `sorry`, axiom policies and exact toolchains.

The optional container test fetches the pinned GitHub example through the normal
HTTP client and removes its temporary deployment on exit:

```sh
bash Applications/LeanBuild/test-deployment.sh lean-cloud-build:dev
```
