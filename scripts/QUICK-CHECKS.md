Small runners run **changed-module diagnostics**, never a full PR build.
Use Build PR → Run workflow → `quick-check`, select a registered small host and PR; the scheduler also pins its head.
The trusted workflow resolves a merge onto main and refuses stale heads, other toolchains or changed configurations.
Each host gets at most8CPU,4jobs,64GiB,20minutes of compilation and30minutes total execution.
A check includes at most8changed Lean roots and2000project ancestors; larger work is deferred.
Stock Lake runs inside the existing offline Bubblewrap sandbox with private dependency/build copies.
Results say changed_roots_pass, changed_roots_fail or deferred; none attests a full build or publishes a cache.
Source-bound raw work remains private on the runner for possible later verified reuse; output paths are in the result artifact.
Operators run `python3 scripts/quick-schedule.py --state /private/path` to queue open PRs, one per small host; priority134/150 stay on big machines.
The scheduler uses one120second GitHub watcher per run, preserves known run IDs across restart and holds uncertain outcomes for review.
