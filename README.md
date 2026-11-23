# riemann-hypothesis

[![checks](https://github.com/leanprover-community/riemann-hypothesis/actions/workflows/checks.yml/badge.svg)](https://github.com/leanprover-community/riemann-hypothesis/actions/workflows/checks.yml)


A community-led effort to clean up and maintain a Lean formalization of the Riemann Hypothesis,
and of GRH for Dirichlet L-functions. The `original` branch contains the first commit as retrieved on 2026-11-20 from <https://alpo.ge/remark.pdf>

## Theorem Statements

`src/Main.lean` proves the following theorems (see [`src/Challenge.lean`](src/Challenge.lean)):

| Theorem | Statement |
|---|---|
| `riemannHypothesis` | Mathlib's `RiemannHypothesis` |
| `LFunction_ne_zero_of_half_lt_re` | L(χ, s) ≠ 0 for Re s > 1/2, for every modulus and every Dirichlet character, except the trivial character at s = 1 |
| `LFunction_eq_zero_re` | every zero of L(χ, s) with 0 < Re s < 1 has Re s = 1/2 |

 states the same five with `sorry` in place of the
proofs, in a file that imports only Mathlib. Comparator checks that `Main.lean` proves exactly
those statements, that it uses no axioms other than `propext`, `Quot.sound` and
`Classical.choice`, and that Lean's kernel and nanoda both accept the proof.

## Cache

A full build takes hours, so you should use the cache:

```bash
lake exe cache get
lake build --no-build
```

## Checking the proof

To check the proof yourself, without the cache, take a fresh clone on a Linux machine with
[bubblewrap](https://github.com/containers/bubblewrap) installed and run:

```bash
MATHLIB_CACHE_GET_URL=https://cache.mathlib.org/mathlib4 lake exe mathlib/cache get
lake comparator
```

The first command fetches Mathlib's compiled files and nothing of ours. Don't use
`lake exe cache get` here, because that also downloads our prebuilt copy of the submission. The
second reads `comparator.json`, builds `Challenge` and `Main` in a sandbox with no network, and
makes the checks described under [What is claimed](#what-is-claimed).

```bash
export LEAN_ABORT_ON_PANIC=1        # as Comparator does
export LAKE_ARTIFACT_CACHE=false    # in case cache-env.sh was sourced

# in a clone where the submission has not been compiled
lake build Challenge
lake env leanexport Challenge -- $(cat export-targets.txt) > challenge.export

# wherever you build the submission
lake build Main
lake env leanexport Main -- $(cat export-targets.txt) > solution.export

# from an empty directory, with the same Lean release and comparator.json from the first clone
lake comparator --config comparator.json \
  --challenge-from-export challenge.export --solution-from-export solution.export
```

The published source was written for Lean 4.33.1, which has neither `lake comparator` nor
`leanexport`, so checking `40e56bab` itself takes two toolchains.
[An older version of this README](https://github.com/leanprover-community/riemann-hypothesis/blob/7cce738ba719a32964ca3822d0994f4c6952c7ae/README.md#checking-it)
has those steps.

## CI

If you have a Linux machine with
plenty of memory and disk to spare, [CI-RUNNERS.md](verification/CI-RUNNERS.md) explains how to
lend it. The scripts behind all this are in [`scripts/`](scripts/) and
[`tools/ci_native/`](tools/ci_native/README.md).

## License

The submission belongs to its author and was published without a license. It is mirrored here
so that it can be checked. Commit `40e56bab` is the unmodified copy.

