# Contribute a proof check

The index gives each of the 175,187 native Lean modules a stable ID for this archive version. There are 2,858 packets of at most 64 modules at the same project-import depth. Within a packet the modules can build concurrently after their prerequisites are ready. Reading the index and building a module require Python's standard library. Creating a claim with the CLI also requires an authenticated GitHub CLI.

When GitHub CLI is signed in to github.com, the tracker uses that account’s API quota to read open claims. Anonymous lookups are also supported.

## Choose and claim work

```bash
python3 tracker/tasks.py next
python3 tracker/tasks.py show M000001
```

For a worker with the pinned Mathlib cache and no project build outputs, run
`python3 tracker/tasks.py next --cold`. This lists individual modules with no
project imports, including available members of partially occupied packets.
It skips observed, assigned, and claimed modules. Suggestions first favor
modules that are the sole project import of more available tasks, then those
with more available direct consumers. These counts describe the source graph.
Use the displayed module ID to claim a single module.

Choose a packet from the live suggestions or a single open module. See [Choosing a task](#choosing-a-task) below for how depth affects build cost and how to work a partially completed packet. Replace the sample identifier below with your selection.

```bash
python3 tracker/tasks.py claim P0123
```

The claim command opens a public issue. You can also open an issue manually with a title of the form `Claim P0123` or `Claim M000001`. Check for overlapping claims after submitting. Wait for the claim-granted label and matching bot comment before starting. A serialized workflow preserves existing valid grants and processes simultaneous new requests in issue-number order. Close a claim if you stop working on it. The snapshot states in the index describe coordinator progress at the recorded time. Open claim issues supply the live volunteer assignments. The coordinator's full run also continues in the background.

The **Observe volunteer reservation times** workflow publishes a downloadable `claim-timing.tsv` every two hours. For each volunteer grant it measures wall time to the claimant’s first `Replay submission`, closure, or the current observation for an open claim. Open intervals are lower bounds. The longest silence column measures gaps between claimant comments on that issue, including time from grant and up to the observation endpoint. Work on a runner and updates posted on another issue can occur during those gaps. The workflow only reads claims.

## Choosing a task

Depth is project-import depth: it counts the chain of project modules a module imports. Mathlib arrives prebuilt from the pinned cache, but project modules do not. On a cold machine Lake builds the transitive project imports of your target locally before the target itself, so cold build cost grows quickly with depth. A shallow packet or a single shallow module is the right first task; a depth-100 packet can mean building thousands of project modules first. A first build on a new machine also pays the one-time prepare step: the archive download and the Mathlib cache fill a volume of roughly 11 GB.

`next` suggests packets whose modules are all still open. Once any module in a packet has evidence, the packet leaves those suggestions even though its remaining modules are still open work. Run

```bash
python3 tracker/tasks.py next --include-partial
```

to also list these partial packets, with open/total counts, shallowest and most-open first. Packets containing coordinator-assigned modules are not listed. A partial packet cannot be claimed as a packet: the claim bot reserves every module that already has evidence, so a whole-packet claim would conflict. Instead, list the packet's modules with `python3 tracker/tasks.py show P0123`, pick an open one, and claim it individually with `python3 tracker/tasks.py claim M000001`. The `--cold` listing already works this way: it lists individual open modules, including members of partial packets.

## Build a task

Use Linux with elan, Git, GNU tar, sha256sum, a C toolchain and adequate storage. Prepare a clean checkout using the original release and the pinned checksums. Keep the generated receipt directory outside the source tree.

```bash
./verify.sh /path/to/new/replay-volume --prepare-only
python3 tracker/tasks.py build P0123 /path/to/new/replay-volume/lean /path/to/new/receipt --bundle
```

The task command checks the selected sources and pinned mathlib revision, builds the targets with Lake, and saves the command, exit status, toolchain identity, output hashes and build transcript. The receipt also records UTC start and end times, elapsed seconds, the host's CPU count and memory, the peak memory of the largest build process, and `rebuilt_project_modules`: the project imports this run's Lake transcript reports as built, besides the requested targets. Lake will build missing imports locally. A module late in the dependency graph can require substantial work on a cold machine. The optional bundle contains the selected modules' generated output files, excluding `.setup.json` compiler inputs that Lake regenerates for compilation. Use `--fast-bundle` to package the same files with gzip level 1 when worker time matters more than transfer size. Both variants record the final archive's SHA-256 in the receipt. The public index lists direct project dependencies as task IDs.

## Build on Windows or macOS with Docker

The replay scripts expect Linux. On Windows or macOS, run them in a Docker container. Building the project runs Lean code from the archive, so do not mount host folders into the container. Use a named volume for the build.

```bash
docker volume create rhwork
docker run -d --name rhreplay -v rhwork:/work ubuntu:24.04 sleep infinity
docker exec -it rhreplay bash
```

Inside the container:

```bash
apt-get update && apt-get install -y curl git python3 build-essential ca-certificates
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh
sh /tmp/elan-init.sh -y --default-toolchain none
ln -s /root/.elan/bin/* /usr/local/bin/
git clone https://github.com/rohanarun/alpoge-rh-replay /work/repo
cd /work/repo
./verify.sh /work/vol --prepare-only
python3 tracker/tasks.py next --cold
```

The container has no GitHub login. Claim from the host instead, either on the website or with the GitHub CLI:

```bash
gh issue create --repo rohanarun/alpoge-rh-replay --title "Claim M000001" --body "I am working on M000001."
```

After the grant, build inside the container, then copy the receipt to the host for your submission:

```bash
python3 tracker/tasks.py build M000001 /work/vol/lean /work/receipt-M000001 --bundle
```

```bash
docker cp rhreplay:/work/receipt-M000001 .
```

Notes:

- Docker Desktop limits the container's memory. With the WSL 2 backend on Windows, the limit comes from WSL, which defaults to half of the host RAM. Raise it with `memory=` under `[wsl2]` in `%UserProfile%\.wslconfig`, then run `wsl --shutdown`. On macOS, use Docker Desktop's Resources settings. Run `free -g` in the container to see the limit.
- The prepare step downloads about 8,700 Mathlib cache files and can be slow. After that, a cold module builds in minutes. One took about 5 minutes on 16 vCPUs.
- `ubuntu:24.04` has no `/usr/bin/time`. Use the shell's `time` keyword to log elapsed time, or install the `time` package.
- In Git Bash on Windows, prefix `docker exec` and `docker cp` commands that contain container paths with `MSYS_NO_PATHCONV=1`. Otherwise Git Bash rewrites `/work/...` into a Windows path.
- Remove everything afterwards with `docker rm -f rhreplay` and `docker volume rm rhwork`.

## Run a persistent volunteer worker

Use a Linux or macOS controller with Python 3.9+, Docker and an authenticated GitHub CLI. The builder runs inside the prepared Linux container from the Docker instructions above. Use the same tracker revision on both sides. Keep GitHub credentials on the controller and use a named volume per native Lean toolchain and platform. An existing warm volume should already have known provenance. The first dispatcher build records its platform and pins under `.lake/build` and subsequent dispatcher builds check them.

Capture the worker's inventory inside the container. The inventory contains the archive and toolchain pins, the Lean target triple, and project module IDs present on that worker. Refresh the controller checkout before selecting work.

```bash
docker exec rhreplay python3 /work/repo/tracker/replay_evidence.py inventory /work/vol/lean > worker.json
python3 tracker/tasks.py next --warm worker.json --limit 20 > candidates.txt
awk '{print $1}' candidates.txt > assignments.txt
```

Supply `--primary-inventory primary.json` when the primary has provided a recent snapshot from the same inventory command. Warm suggestions omit targets on either machine, skip occupied reservations, and favor available direct consumers per estimated missing project build. Each suggestion has a disjoint set of missing imports within this list. The default maximum is three missing project modules per target, adjustable with `--max-builds`. Presence in an inventory guides scheduling. Lake checks actual reuse on the receiver.

Run the controller with your own evidence fork. This command opens public claims, uploads verified receipt, log and bundle assets to releases on your fork, and submits comments on granted claims.

```bash
python3 tracker/worker.py assignments.txt worker-state --jobs 2 \
  --container rhreplay --fork YOUR-LOGIN/alpoge-rh-replay
```

Assignments may contain individual module or packet IDs. The controller bounds outstanding reservations and parallel builds with `--jobs` (default 1). Choose a value that fits the container's memory. It waits for the grant label and the matching bot comment, and closes its own claim when the bot marks it as a conflict. Replay artifacts stay under `/work/receipts` on the persistent builder volume. The controller stores verified evidence and a journal in `worker-state`. Use `--container-repo`, `--checkout` and `--receipts` for other container paths.

Restart with the same command and state directory. A durable claim marker and issue history recover writes whose responses were lost. A builder lock and completed receipt let the controller reconnect after an interruption. After a conflict or failure, inspect `worker-state/state.json`, the issue and the numbered local log. Close abandoned claims. After resolving a recoverable error, add `--retry M000001` for that task. If the journal reports an unconfirmed public write, check the issue history before explicitly retrying. An interrupted or failed compiler attempt keeps its evidence on the builder.

### Check evidence and measure receiver progress

Verify an archived bundle independently with the controller's tracker. To check source and installed object hashes too, pass the prepared checkout. Older unbundled receipts require this checkout.

```bash
python3 tracker/replay_evidence.py verify M000001 path/to/receipt
```

When a requested module already exists in the worker cache and has no build line, the builder runs the pinned Lean kernel checker against its imported environment. It checks the installed object against the receipt before and after replay. The submission links `kernel-replay.json` alongside the receipt, bundle and Lake log. The record includes the exact command, per-module transcript, successful exit status and the SHA-256 of the receipt. Download it with the other assets for offline verification.

Cached-target replay uses one checker process by default. To use spare CPUs, set `REPLAY_KERNEL_JOBS` to a positive integer in the builder environment, for example by adding `-e REPLAY_KERNEL_JOBS=4` when creating the builder container. This splits the requested cached targets into contiguous batches and runs at most that many pinned checker processes, with one Lean thread each. Each process loads an imported environment, so choose the count to fit the builder's memory and concurrent source builds. Parallel records list each actual command, exit status and transcript in `replays`; use an updated tracker to verify them. Single-process records keep the existing format. These are module-level checks against imported environments; the final fresh replay of `Main` remains separate.

For a transfer, capture the primary's inventory before installing reviewed, platform-compatible artifacts using the coordinator's existing procedure. On the primary, run the following inside its prepared environment.

```bash
python3 tracker/replay_evidence.py inventory /work/vol/lean > before.json
# Install the reviewed artifacts, then check the exact granted target.
python3 tracker/replay_evidence.py reuse-check M000001 /work/imported/receipt \
  --checkout /work/vol/lean --before before.json
```

The receiver checks the native platform, pins, source and object hashes, then runs the original Lake targets with rebuilding and remote cache downloads disabled. Successful JSON output lists the checked targets and those absent from the before-inventory. Timed receipts also report new targets per producer Lake hour. For a wave, count distinct accepted new IDs and sum producer build times once per receipt. This measures target reuse. The final Main build, axiom audit and fresh kernel replay remain separate milestones.

### Diagnose overlapping archive members

Before combining bundles, compare them offline using the expected `bundle_sha256` values from their producer receipts:

```bash
python3 tracker/bundle_preflight.py \
  --archive worker-a.tar.gz EXPECTED_A_SHA256 \
  --archive worker-b.tar.gz EXPECTED_B_SHA256 > overlap-report.json
```

The tool streams gzip tar archives, verifies their compressed SHA-256 digests, and reports differing file hashes grouped by module, with archive provenance. It never extracts or installs files. Accepted files must be under `lib/lean/` or `ir/`; safe directory entries and leading `./` prefixes are allowed. Duplicate file paths, traversal, links, devices and malformed inputs are rejected.

Exit **0** means no differing artifact members other than `.trace` or `.setup.json`; **1** reports other differing members; **2** means invalid input. Raw `.trace` and generated `.setup.json` input differences appear separately as informational `trace_differences` and `setup_differences`, since path and log metadata can differ without preventing reuse. The tool does not interpret that metadata. Even differing `.olean` bytes alone do not establish invalid proofs or failed reuse, and a clear report does not establish compatibility. This diagnostic neither repairs the Google aggregate reuse failure nor replaces native-platform, pinned-input, receiver `--no-build --no-cache`, or final Main kernel checks.

### Export matching project dependencies

A target bundle contains the selected targets. A receiver with different prerequisite artifacts can still require rebuilding them or the target. To preserve a completed build's full project import closure, export a supplemental bundle from the producer after its standard receipt passes verification:

```bash
python3 tracker/dependency_bundle.py export P0123 /work/receipts/P0123 \
  /work/vol/lean /work/exports/P0123 --jobs 8
python3 tracker/dependency_bundle.py verify P0123 /work/exports/P0123
```

The output directory must be new, and the receipt must include `targets.tar.gz` and any required `kernel-replay.json`. The exporter copies indexed sources and matching artifacts into a separate receiver, packages the project artifacts in parallel gzip shards, and runs all requested targets with rebuilding and downloads disabled. It checks source, configuration and artifact digests on both sides afterward. Generated `.setup.json` inputs and `.trace.nobuild` diagnostics are omitted. A failed reuse check preserves its log without producing a successful transfer receipt.

Publish `dependency-manifest.json`, `transfer-result.json`, `receiver-no-build.log`, all `dependencies-*.tar.gz` shards, and the files in `receipt/`, preserving that subdirectory when downloaded. `verify` checks the standard receipt, exact indexed dependency closure, archive member digests and reuse record without extracting archives. It works without the local `receiver/` snapshot, which need not be published. The standard submission format is unchanged; link this supplemental export on the existing granted claim.

This exports the full project closure, including cached prerequisites, so its module count is not a count of newly compiled modules. It needs disk space for the receiver snapshot and compressed archives. Package caches and the toolchain are shared with the producer during this check and are not bundled. A different host must prepare compatible pinned dependencies, verify the downloaded export, install the artifacts using the coordinator's transfer procedure, and run its own no-build check. Mixing closures from different producers can still invalidate Lake traces. This export records artifact reuse, not a fresh kernel replay or the final verification of Main.

## Troubleshoot a Lean version mismatch

If `Cache/Requests.lean` reports a missing `Lake.PackageEntrySrc.path` case and the trace shows Lean 4.35.0, update your checkout. The replay uses Lean 4.33.1, and the verifier now calls that version explicitly through elan. Keep elan on PATH, then retry in a new directory on the build volume.

```sh
git pull --ff-only
elan --version
./verify.sh /path/to/fresh-replay --prepare-only
```

The run prints its Lean version near the start of the cache step. If it still fails, share that version and the first failing excerpt from the new directory's `replay.log` on your claim.

## Submit evidence

Begin a comment on your claim with `Replay submission` on its own first line. Include the task or packet ID, exit status, elapsed time, and links to the receipt and log. For a large bundle, attach it to a release on your fork and include its SHA-256 digest. Check logs for personal paths before publishing. The README credits you while your evidence is pending. Keep the claim open for review. Maintainers check the grant, pinned toolchain and inputs, exact target list, successful transcript, and artifact digests before marking a volunteer build complete. Reviewed receipts go in `evidence/volunteers/` and appear in the README and module ledger. Maintainers close accepted claims as completed. Any later reuse or kernel replay is recorded separately. If a build fails, include the first Lean error, file and line, resource limits, and reproduction command.

### Check a submission before posting

Most pending submissions fail one of these checks. Run all of them before you post.

1. **Use one release per claim.** Publish each claim's assets in its own release on your fork, tagged `replay-<ID>-issue-<NUMBER>`; `tracker/worker.py` does this for you. Don't reuse one release for many claims. GitHub caps a release at 1,000 assets, and files uploaded after that point are never stored, even though the upload command may appear to finish.
2. **Download every link you post.** For each URL in the comment, run `curl -fL -o FILE URL` and compare `sha256sum FILE` with the receipt or the digest you state. Don't post until every link returns the file with the matching digest.
3. **Include `build.log`.** Link the Lake log from the same run as `receipt.json`. The receipt's `log_sha256` must match it.
4. **Cover every claimed target.** The log needs a `Built` or `Replayed` line for each requested target. If a target was already in your cache and has no build line, also link the `kernel-replay.json` that the builder writes.
5. **State attachment digests.** For an uploaded attachment or zip, include its SHA-256 in the comment. A missing or mismatched checksum stays pending.

If a check fails, fix the assets and post a new `Replay submission` comment on the same claim. Your grant stays in place while the claim is open.

The final acceptance record separately checks the standard RH proposition, its axiom dependencies and the fresh kernel replay of Main. Module receipts are evidence of partial progress.

For work on new proofs, the [proof reuse example](examples/proof-reuse/README.md)
includes a duplicate-proof scanner, two reusable Lean lemmas and a pinned
compiler check against 33 archive declarations.

## Coordinator and cloud helpers

A targeted cloud helper uses the same public claim queue as volunteers. Open a standard module or packet claim and wait for both the `claim-granted` label and the matching GitHub Actions bot comment. Before provisioning, the coordinator runs `python3 tracker/check_grant.py BATCH.json ISSUE_NUMBER` using the GitHub account that opened the claim. The batch's `targets` must exactly match the claimed module or packet. When a worker has multiple grants, pass every issue number. GitHub lookup failures stop provisioning.

Post each helper's replay submission on its claim and keep the issue open while the evidence is reviewed. Close abandoned claims so others can pick them up. Lake may compile prerequisites along the way, and the primary still walks the full dependency graph for the end-to-end replay.
