# Generate the PR 120 interface repair

Rohan Arun created the wrapper collapse and the section-isolated bundles in community PR 120. Roy7 asked how to detect a build that silently selects a different declaration. This generator keeps the source and bundle boundaries from that work where members can share the selected interfaces. [Community PR 120](https://github.com/leanprover-community/riemann-hypothesis/pull/120) · [Partition generator on the author's fork](https://github.com/rohanarun/riemann-hypothesis/pull/15)

Run either command in a checkout with the integration history. Each command writes a Git patch against the input commit and a two-column map from original member to output module. The program uses a temporary Git index and object directory.

```sh
python3 scripts/prepare_pr120_interfaces.py --patch /tmp/pr120-interfaces.patch --locations /tmp/locations.tsv
python3 scripts/prepare_pr120_interfaces.py --with-instance-providers --patch /tmp/pr120-instances.patch --locations /tmp/instances.tsv
```

Fetch the integration history with `git fetch https://github.com/aliromman/riemann-hypothesis.git codex/pr120-integration-4.36` if the local checkout does not contain it. The default input is `6ec20f6d0853449aab15a8750b916889ba9c2620`. It includes the Lean 4.36 main sources from `e555d432490cfbc9c8cf11db753fd0fc757b1046`. To use later integration fixes, set `--integration <revision>` and check the resulting source. The program checks both exact output trees for the default input.

| Selected original providers | Output source modules | Output Git tree |
|---|---:|---|
| 62 providers of 37 conflicting declarations | 60,894 | `b9d25efbcdaff5b40623b877cc878c828c5fddeb` |
| The same 62 and seven diagnosed instance providers | 63,550 | `51da130f72ebd4fe8ee1bcb5dad2171df71ee92d` |

Lean can import two theorems with the same name and different argument labels or binder annotations. The selected interface can depend on import order. The generator preserves access to each selected provider and preserves the relative order of the providers for each of the 37 names. It retains the submitted header order when those conditions allow it.

Some earlier fixes deleted local duplicate declarations. The generator checks whether the remaining provider is still accessible after the split. Its inventory covers 303 public and 44 private commands in 168 original name groups. Each record includes the original member, the submitted bundle, the declaration token, its visibility, a reviewed private rename if present, and the original compiler range. Ranges use zero-based line numbers and UTF-16 columns from the original `.ilean` at `c7791603122c0328f79e49f6be5d7d4402effc53`. The program validates the ranges against Git and checks both the member scope and its public exports.

With either profile, 12 original public commands are absent before this check. Seven have a reachable public supplier. The program restores the other five commands in four original members. This recovers 202 original member/name pairs that lost access in each of the public and module-body views. Compile the affected closures and check the five protected conclusions on the resulting tree. Unselected names and instances can gain exposure during consolidation.

`restore_interfaces.patch` restores the original interfaces and caller spellings where previous repairs selected a single common interface. It reverses the interface changes in `c2a9e3168fe`, `e2cab574182`, `4bc2ce98a7e`, `1193e891b41` and `e0e48c7cc4f`. From `3db0c5faccf` it restores 20 declarations and 14 calls. It retains the seven private renames that separate different statements. The program applies these source edits, the import changes and the five required declarations in a single patch.

To test the public calling conventions, run the next command after a stock Lake build. Each external client runs `#check @name`, inspects the exported argument labels and binder annotations, and applies the declaration. The expected signatures come from Lean 4.36 on the 62 original providers and two original clients that import competing providers. The latter two clients check the winning signature for three names. A missing artifact is reported as pending and causes exit status 2.

```sh
python3 scripts/check_pr120_interfaces.py --locations /tmp/locations.tsv --project . --emit-clients /tmp/pr120-clients
```

## Updated author and main revisions

To include Rohan Arun’s follow-up commits through `7010be8895c6678a4ee638c3afbb0d00ded0240e` and the ten confirmed instance and duality providers, use the merged input below. The integration includes community main `51d9b1a28026d458aef9c9af3df8b083276e3d2d`. [Author changes](https://github.com/leanprover-community/riemann-hypothesis/compare/f94106583626ad6b48ac6e239e0b2e5ffc879555...7010be8895c6678a4ee638c3afbb0d00ded0240e)

```sh
python3 scripts/prepare_pr120_interfaces.py --integration 6c06c6a7d99d500e16e88fb9597eef80fdf7bfbe --with-all-confirmed-providers --patch /tmp/current.patch --locations /tmp/current-locations.tsv
```

The output has 64,934 source modules and Git tree `faef8e5bbf9b68d7d9f56aacf6bd6cb48497136b`. Relative to the 149,397 original source modules on this main, it removes 84,463. The ten additional providers comprise the seven in `confirmed_instance_providers.txt`, the two double-coset measure modules, and the neutral local fields duality module.

Rohan added eight public import lines in seven files at `b4f6cadc`. Four repeat an existing destination. Three refer to statement wrappers removed by PR 120. `author_imports.tsv` records each original member and surviving supplier. The three recovered supplier declarations are `GlobalTheory.FN.germ_main`, `GlobalTheory.Phase.Calc.calculus`, and `GlobalTheory.gramDet_closed_forms`. The other new import in `IsKummerCharacterAtLevelAddZeroCongr` is a shortcut. Only `GlTwoPosRatMobiusBasicLaws` from its destination bundle was reachable from that original consumer. Six lines were removed in `3a0aee48`. The other two obsolete wrapper imports were removed in the integration. The generator follows each surviving addition and accepts a previously translated wrapper import. It checks all protected access modes and orders after it routes those lines. On the earlier integration `95b530edbcf4c5132f8c51c27fa1264c99449fa1`, the current generator emits tree `60839da7b582fbf6ea2ef7e8de2f051d345942e6`.

The graph restores both historical binder interfaces. Four derivative calls in `FlatLoc` and `RhGradFPf` acquired all six arguments during author-side repairs. The generator retains these argument lists and uses Lean’s explicit application syntax at these sites. The three affected applications in `FlatLoc` then produce the same native types and proof terms as the original source when compiled against the same dependencies. When the partition restores previously removed helpers in `CrossMSmulRight`, `LocDensCnt`, and `LocDensHH`, it keeps the complete qualified declarations from Rohan’s revision. The original compiler references resolve to `Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR` in all three members.
