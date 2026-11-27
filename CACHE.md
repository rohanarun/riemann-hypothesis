# Build cache

This branch is the readable edition (`grh/`) of https://github.com/lsernau/grh-lean commit
72fead102f663d5c7a407964a13dc0cf9d977207, moved to the repository root, plus configuration and
scripts for a shared build cache. No file under `src`, and no `Challenge.lean`, `comparator.json`,
`lake-manifest.json` or `lean-toolchain`, is changed. The additions are `CACHE.md`, a note at the
top of `README.md`, the marked lines in `lakefile.toml`, `Cache.lean`, `lake-cache-get.sh`,
`ci-cache-get.py`, `ci-cache-stage.py`, `publish-ci-cache.py`, `ci-github.py`,
`fetch-artifacts.py`, `tauceti-cache-get.py`, `cache-baseline.json`, `runner/` and `tests/` in
`scripts`, and the workflows `.github/workflows/build.yml` and
`.github/workflows/publish-ci-cache.yml`. The Tau Ceti dependency (below) adds one entry to
`lake-manifest.json`. The scripts are copied or adapted from
`scripts/` of the earlier `main` branch of https://github.com/leanprover-community/riemann-hypothesis
(now the branch `alpoge`).

**The cached files were built from an unverified third-party proof, and the cache does not verify
anything.** The checks in the scripts only establish that you have the bytes which were published
for your exact build inputs. To check the proof, build it from source yourself, without this cache.

## Use

    lake exe cache get
    lake build

This needs Python 3.11 or newer and curl 7.71 or newer, and no credential. It fetches Mathlib's
cache, then Tau Ceti's, then this project's, and unpacks them. It ends with `lake build --no-build`, which must report
that nothing needs compiling. `lake exe mathlib/cache get` fetches Mathlib alone.

A change to the sources, `lakefile.toml`, `lake-manifest.json` or `lean-toolchain` gives different
build inputs; `lake exe cache get` then says that no cache matches.

## Baseline

When no record matches, `python3 scripts/ci-cache-get.py --baseline origin/main` (after
`lake exe cache get` has fetched Mathlib) restores a baseline instead: the record of the nearest
commit on `origin/main`'s first-parent history (up to 200 commits) that has one, else the record
pinned in `scripts/cache-baseline.json`. Each candidate is looked up by its own input
fingerprint, computed from Git objects with the same code as for the current inputs, and only
candidates with the current `lean-toolchain` and `lake-manifest.json` are tried. The baseline's
map, module manifest and artifacts get the same SHA-256 checks as an exact match. `lake build`
then compiles only the modules whose inputs differ from the baseline's, and the modules whose
imports changed as a result; it reuses the rest. The script exits 4 when it has restored a
baseline. `python3 -I scripts/tests/test_ci_cache_baseline.py` tests the selection.

For a pull request, CI starts this search at the base commit recorded in the event. The test
merge contains that base even if newer batches land on `main` before a runner picks up the job.

## CI

Pull requests land through GitHub's merge queue. `.github/workflows/build.yml` has one job,
`lake build`, the queue's required check. It builds every pull request to `main` from a fork on
the self-hosted `rh-pr-fork` runners, every pull request from a branch of this repository not
starting with `batch/` on the self-hosted `rh-pr-trusted` runners, and every merge queue group
(`merge_group`), push to `main`, manual run and pull request from a `batch/` branch of this
repository on the self-hosted `rh-big` runner (all described below), with the exact record if
there is one and the baseline otherwise. It
fails if `lake build` fails, if the build log contains `` declaration uses `sorry` ``, or if
`scripts/PrintAxioms.lean` reports any axiom other than `propext`, `Classical.choice` and
`Quot.sound` for the five theorems. It never publishes anything.

On the `rh-big` runner, except for pull requests, which upload nothing, the job builds with
`lake build -o`, then `scripts/ci-cache-stage.py` writes the map, the module manifest and the
artifacts that the public cache does not have yet, and the job uploads them as the Actions
artifact `cache-<commit>`. The push build of a commit
that the merge queue has already built stops after checking that (`scripts/ci-github.py
queue-tested`).

`.github/workflows/publish-ci-cache.yml` publishes them. On each push to `main` it finds the
build of that commit (the `merge_group` run, since the queue moves `main` to the exact commit it
built; else the push build of the commit, once it has finished), and checks its artifact with the
code of `main` on a fresh GitHub-hosted runner, running nothing from the artifact or the commit:
the record is computed from the commit's Git objects, the map and manifest must pass
`ci-cache-get.py`'s checks for those inputs, the modules must be exactly the source files under
`src`, and every artifact (staged, or else downloaded from the public cache) must have the
manifest's SHA-256, be named by its stock Lake content hash, and extract with stock leantar.
Only then does the job, in the environment `ci-cache-publish` (deployable from `main` only),
read `R2_ACCOUNT_TOKEN` and write the new artifacts, the map, the manifest and the record, each
with `If-None-Match`, so nothing is overwritten. A second fresh runner then runs
`lake exe cache get` on the commit, and `lake build --no-build` must succeed. A manual run
(`workflow_dispatch`, inputs `sha`, optionally `run_id`, and `publish`) publishes any successful
self-hosted build of a given commit, or with `publish` false only verifies it. After this,
`python3 scripts/ci-cache-get.py --print-identity`, run on a published commit, gives new contents
for `scripts/cache-baseline.json`, which is only needed if the history to the newest record is
longer than 200 commits.

The publisher cannot check that an artifact is what a module's input hash produces: that would
need building it. So the cache trusts the `rh-big` runner's builds, as it trusted the hand
publisher's builds before.

## Self-hosted runners

There are three kinds of self-hosted runner, so that the merge queue never waits behind other
pull requests:

- `rh-big`, one runner on a 64-vCPU host, runs the merge queue (`merge_group`), pushes to
  `main`, manual runs and pull requests from a branch of this repository whose name starts with
  `batch/` (the batcher's batch pull requests). Only its builds are published (see above).
- `rh-pr-trusted`, several runners on a shared host, run every other pull request from a branch
  of this repository. Each is confined to its own CPUs and memory, and uploads nothing.
- `rh-pr-fork`, several runners on each of two 96-vCPU hosts, run pull requests from forks.
  (GitHub does not pass repository variables to pull requests from forks, so `build.yml` names
  the label itself; changing it to `ubuntu-latest` there sends them back to GitHub-hosted
  runners.) They assume hostile code: the hosts hold no credential at all (no R2 or
  AWS credential, no GitHub token beyond each runner's one-time configuration), and the
  instances' metadata endpoint is disabled in EC2 (`http-endpoint disabled`), so not even root
  can fetch the instance role's credentials. They upload nothing.

The `rh-big` and `rh-pr-trusted` hosts hold no credential of the project either, and build only
code that is queued to land on `main` or already on it, or that someone with write access has
pushed to a branch of this repository (a pull request from such a branch, or a manual run). The
setup of all three is in `scripts/runner/`:

- `setup-host.sh` (run as root, idempotent) creates the unprivileged runner user (no sudo, no
  other groups), installs a pinned, checksummed copy of the GitHub Actions runner owned by root,
  blocks the metadata service and private address ranges for that user's uid on IPv4 and IPv6
  (a `ghrunner-firewall` service, iptables owner rules), sets `kernel.yama.ptrace_scope=1`, and
  installs the runner's service. `bash setup-host.sh` sets up the `rh-big` runner: user
  `ghrunner`, `rh-runner.service`. `bash setup-host.sh <instance> <label> <cpus> <memory-max>`
  sets up one of several runners on a shared host: user `ghrunner-<instance>`,
  `rh-runner@<instance>.service`, `ghrunner-firewall-<instance>.service`, and the label, cpuset
  and memory limit in `/etc/rh-runner/<instance>.env`. The `rh-pr-trusted` runners are
  `bash setup-host.sh pr1 rh-pr-trusted 0-37 150G`, `pr2 rh-pr-trusted 38-74 150G` and
  `pr3 rh-pr-trusted 75-111 150G` on a 192-vCPU host whose CPUs 112 to 191 run other builds.
  The `rh-pr-fork` runners are `f1`, `f2` and `f3`, with 32 vCPUs and `200G` each, on each fork
  host (on a host with two threads per core and two NUMA nodes, each cpuset keeps whole cores
  together, as in `f1 rh-pr-fork 0-15,48-63 200G`).
- `loop.sh` (that service) runs one ephemeral just-in-time runner per job. For each job it gives
  the runner user a new, empty home directory with a fresh copy of the runner, runs it in a
  transient systemd unit (read-only system, other home directories, `/srv` and `/etc/rh-buildq`
  hidden, private `/tmp`, other users' processes hidden from `/proc`, no new privileges, the same
  addresses denied to the unit's cgroup, and for an instance its cpuset and memory limit, with
  `LEAN_NUM_THREADS` set to its CPU count),
  and after the job kills whatever is left and deletes the home directory, workspace included.
  Each instance has its own user, so this never touches another instance's job.
- `job-started.sh` is the runners' job-started hook. Pull requests can change the workflow they
  run, so one could ask for any runner; the hook fails every job before it starts unless it is
  `build.yml` of this repository and one of the jobs `build.yml` sends to the runner's label
  (which `loop.sh` passes in `RH_RUNNER_LABEL`). On `rh-big`: a `merge_group` on `main`'s queue, a
  push to `main`, a `workflow_dispatch` (which needs write access), or a `pull_request` whose
  `pull_request.head.repo.full_name` in the event payload (`$GITHUB_EVENT_PATH`, written by
  GitHub) is this repository and whose `pull_request.head.ref` starts with `batch/`. On
  `rh-pr-trusted`: a `pull_request` whose head repository is this repository. Both refuse a pull
  request from a fork, or one whose payload has no head repository. On `rh-pr-fork`: a
  `pull_request` whose head repository is not this repository (a fork, or a deleted fork). After
  a change to the hook it must be installed again (`setup-host.sh` does that, or
  `install -m 0755 job-started.sh /opt/rh-runner/job-started.sh`, which leaves a running job
  alone).
- `mint-jit.sh` runs every minute on a trusted workstation whose `gh` is logged in as a
  repository admin (systemd user timers): `mint-jit.sh <host> 4` for `rh-big`, and
  `mint-jit.sh <host> 2 <instance> rh-pr-trusted` for each `rh-pr-trusted` instance, and
  `mint-jit.sh <host> 2 <instance> rh-pr-fork` for each `rh-pr-fork` instance (runners named
  `<label>-<host>-<instance>-<time>-<random>`). It keeps
  that many one-time runner configurations from
  `POST /repos/{owner}/{repo}/actions/runners/generate-jitconfig` (labels `self-hosted`, `linux`
  and the runner's label) in the runner's root-only spool, and deletes those older than 20 hours
  with their registrations. Each configuration can register one runner for one job, and is good
  for nothing else, so the hosts never hold a GitHub token. If the workstation stops, each runner
  runs the jobs its spool still allows (within 20 hours), then waits.

## Tau Ceti

The project depends on [Tau Ceti](https://github.com/TauCetiProject/TauCeti), pinned in `lakefile.toml`
at a toolchain tag or at a commit of its main branch for which Tau Ceti has published a cache
(check `https://cache.taucetiproject.org/revisions/TauCetiProject/TauCeti/tc/<toolchain>/<rev>.jsonl`). Tau Ceti publishes its oleans in its own public cache, the
service `tauceti-public` in `lakefile.toml`, which neither Mathlib's cache nor this project's
covers. `scripts/tauceti-cache-get.py`, which `lake exe cache get` (and CI) runs after Mathlib's
cache:

- stops unless Tau Ceti's own `lake-manifest.json` pins the same Mathlib commit as ours, since
  otherwise none of its cached oleans match;
- stops if `src/Statements.lean`, `src/Main.lean` or `Challenge.lean` imports a Tau Ceti module,
  so that the five statements keep depending on Mathlib alone;
- downloads Tau Ceti's mappings for the pinned revision (about 135 MB the first time);
- runs `lake build` on the Tau Ceti modules imported under `src` together with every Tau Ceti
  module they import in turn, publicly or privately, which downloads exactly those oleans into
  `.lake/packages/TauCeti`. Lake restores a cached module without the modules it imports only
  privately, but a later `lake build --no-build` checks them too.

After adding an import of a new Tau Ceti module, rerun `lake exe cache get`; otherwise Lake
compiles that module and its Tau Ceti dependencies from source. The Tau Ceti and Mathlib pins move
together: pick the Tau Ceti tag (or cached main commit) for the new Lean release, and check that its manifest pins the
Mathlib commit chosen here. A change of either pin changes the build inputs of every module that
imports Tau Ceti, directly or not.

Tau Ceti is the one dependency from outside leanprover-community and leanprover. The
challenge-files check trusts it by its exact address, `TRUSTED_REPOS` in
`.github/workflows/challenge-files.yml`; moving it to another address fails that check. Another
such dependency needs its address added there first, by a maintainer, in a pull request of its own.

For a con-leche `--compare` run, Tau Ceti's `.lake/packages/TauCeti/.lake/build/lib/lean` belongs
on the untrusted `--search-path`, with the project's, so that its declarations are checked rather
than trusted.

## Keys

The keys in the bucket behind https://rh-cache.taucetiproject.org are shared with the `grh/`
project of branch `grh-lean-cache`, which has the same modules:

- `artifacts/leanprover-community/riemann-hypothesis-grh-lean/grh/<hash>.art`: Lake's `.ltar` files,
  named by Lake's content hash;
- `grh-lean/grh/inputs/<fingerprint>.json`: the record for one set of build inputs (Git tree of
  `src`, `lakefile.toml`, `lake-manifest.json` and toolchain);
- `grh-lean/grh/maps/<sha256>.jsonl` and `grh-lean/grh/module-manifests/<sha256>.jsonl.gz`: Lake's
  map and the list of modules, with the SHA-256 of every artifact.

The keys of the earlier `main` branch's cache are separate and unchanged.
