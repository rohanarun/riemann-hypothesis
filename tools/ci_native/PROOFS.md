`native-proof` lends a registered runner to a ready batch rather than a whole PR.
The policy pins #134's `57bcce43` snapshot, source `2f36319`, and its 149,211
affected-module list. The immutable public branch `build-snapshots/pr134-source2f`
retains that exact producer commit when the author's PR branch is rebased.

The coordinator supplies `seed.json` (`snapshot`, `missing`, `input_manifest`,
`input_archive_sha256`), the sorted worklist, and a dependency ZIP. An operator
uploads them under `ci/proof-leases/<SHA>/{seed.json,worklist.txt,inputs.zip}` in
the existing public cache, then dispatches `build-pr.yml` on main with
`mode=native-proof`, `pr_number=134`, and `proof_seed_sha256=<seed SHA>`.
Donors need no cloud token or SSH access. The runner group remains restricted
to this exact main workflow and only the dedicated approved label is eligible.

The runner restores only five explicitly named unchanged modules from the pinned public #150 cache.
The allowlist excludes both 149,211 affected modules and 180 deleted modules
before applying current dependency deltas. Only those five baseline archives
are downloaded; the complete released manifest/map remain SHA-verified.
Stock Lake checks imports with `noBuild=true`
before compiling explicit targets. Batches have at most 256 targets; small
machines are refused. Package metadata uses private overlays or private copies.

Returns retain the existing Actions provenance, lease and per-file SHA checks.
`rpc.py accept` verifies transport; the coordinator owns promotion and merging.
Lost leases are retained for operator recovery. The proxy retains prior outputs
and includes their needed closure when a later job starts in a fresh workspace.

Run unit tests with `python3 -m unittest discover -s tools/ci_native -p 'test_*.py'`.
`pilot_proofs.py` exercises real stock proof compilation and the missing-import
guard. `pilot_mathlib_sandbox.py` checks the namespace and writable package
metadata with a real Mathlib import.

The unchanged baseline expands once into a sealed, snapshot-specific state directory.
A cold expansion runs in its own network-free namespace and publishes its seal only
on success. Later leases mount that tree read-only beneath a private build overlay;
older Bubblewrap versions use private copy/reflink inodes. Failed partial expansions
remain available for inspection and are never mistaken for a completed base.

The current donor policy builds PR185 with stock Lean4.37.0-rc1 and no project baseline.
A planner accepts only an exact source snapshot on the open PR’s ancestry, with policy-pinned raw configuration and a sealed full worklist.
The worker checks that exact source again inside its network-free sandbox.
The maximum lease is4096ready modules; the first operational lease uses1024Mathlib-only roots and64compiler jobs.
Dependency preparation uses official4.37Mathlib caches;4.36project outputs are never restored.
Main’s released toolchain/cache settings remain separate until the port is merged.
