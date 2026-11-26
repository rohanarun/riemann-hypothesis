"""Generate the source patch for the PR 120 interface partitions.

Rohan Arun created the wrapper and bundle transformation in community PR 120.
This program reuses those bundles and the partition generator from author PR 15.
"""
import argparse
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from route_author_imports import AUTHOR_REVISION, check_original_routes, read_routes, restore_imports, take_imports
from required_duplicate_providers import read_origins, restore_providers, retain_author_qualifications, retain_calling_conventions
from partition_bundles import Partition, atomic_output, git, read_graph, read_order_groups, write_outputs


HERE = Path(__file__).resolve().parent
DATA = HERE / "pr120_interface_data"
ORIGINAL = "e555d432490cfbc9c8cf11db753fd0fc757b1046"
INTEGRATION = "6ec20f6d0853449aab15a8750b916889ba9c2620"
EXPECTED = {False: "b9d25efbcdaff5b40623b877cc878c828c5fddeb",
            True: "51da130f72ebd4fe8ee1bcb5dad2171df71ee92d"}


def output(repo, *args):
    return subprocess.check_output(git(repo, *args), text=True).strip()


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--repo", type=Path, default=Path("."))
    cli.add_argument("--integration", default=INTEGRATION, help="integration revision with the reviewed 4.36 fixes")
    cli.add_argument("--with-instance-providers", action="store_true",
                     help="also preserve access to the seven confirmed instance providers")
    cli.add_argument("--with-all-confirmed-providers", action="store_true",
                     help="also preserve the seven prior providers, both measure providers and the duality provider")
    cli.add_argument("--patch", type=Path, required=True, help="write a single patch against the integration revision")
    cli.add_argument("--locations", type=Path, help="write the destination of each retained original module")
    args = cli.parse_args()
    revision = output(args.repo, "rev-parse", "--verify", "--end-of-options", args.integration + "^{commit}")
    subprocess.run(git(args.repo, "merge-base", "--is-ancestor", ORIGINAL, revision), check=True)
    objects = output(args.repo, "rev-parse", "--path-format=absolute", "--git-path", "objects")
    groups = read_order_groups(HERE / "pr120_conflicting_interfaces.tsv")
    names = [name for group in groups for name in group]
    if args.with_instance_providers or args.with_all_confirmed_providers:
        names.extend((DATA / "confirmed_instance_providers.txt").read_text().splitlines())
    if args.with_all_confirmed_providers:
        names.extend((DATA / "measure_and_duality_providers.txt").read_text().splitlines())
    providers = list(dict.fromkeys(names))
    known_author = subprocess.run(git(args.repo, "rev-parse", "--verify", "--quiet", AUTHOR_REVISION + "^{commit}"),
                                  stdout=subprocess.DEVNULL).returncode == 0
    includes_author = known_author and subprocess.run(
        git(args.repo, "merge-base", "--is-ancestor", AUTHOR_REVISION, revision)).returncode == 0
    routes = read_routes(DATA / "author_imports.tsv") if includes_author else {}

    qualified_author = "3a0aee48cdd75aa5c839d279c32b3673841232df"
    has_qualifications = subprocess.run(git(args.repo, "rev-parse", "--verify", "--quiet", qualified_author + "^{commit}"),
                                         stdout=subprocess.DEVNULL).returncode == 0 and subprocess.run(
        git(args.repo, "merge-base", "--is-ancestor", qualified_author, revision)).returncode == 0

    with TemporaryDirectory() as directory:
        work = Path(directory)
        repo = work / "objects.git"
        subprocess.run(["git", "init", "--quiet", "--bare", str(repo)], check=True)
        (repo / "objects/info/alternates").write_text(objects + "\n")
        subprocess.run(git(repo, "read-tree", revision), check=True)
        # Restore the original declarations and caller arguments before computing their import scopes.
        subprocess.run(git(repo, "apply", "--cached", "--3way", str(DATA / "restore_interfaces.patch")), check=True)
        origins = read_origins(DATA / "duplicate_origins.tsv")
        if has_qualifications:
            retain_author_qualifications(repo, output(repo, "write-tree"), qualified_author, origins,
                                         DATA / "restored_qualifications.tsv")
        retain_calling_conventions(repo, output(repo, "write-tree"), DATA / "full_argument_calls.tsv")
        if routes:
            replacements = dict(line.split("\t") for line in (DATA / "removed_author_imports.tsv").read_text().splitlines())
            routes = take_imports(repo, output(repo, "write-tree"), routes, replacements)
        source = output(repo, "write-tree")
        original = read_graph(repo, ORIGINAL)
        if routes:
            check_original_routes(original, routes)
        plan = Partition(original, read_graph(repo, source), providers, groups)
        generated = work / "partition.patch"
        with generated.open("w") as file:
            write_outputs(plan, repo, source, [], file, None)
        subprocess.run(git(repo, "apply", "--cached", "--whitespace=nowarn", str(generated)), check=True)
        staged = output(repo, "write-tree")
        if routes:
            restore_imports(repo, staged, routes, plan, providers, groups)
            staged = output(repo, "write-tree")
        restored = restore_providers(repo, staged, original, plan, origins, work)
        tree = output(repo, "write-tree")
        if revision == INTEGRATION and not args.with_all_confirmed_providers and tree != EXPECTED[args.with_instance_providers]:
            raise ValueError(f"Unexpected source tree {tree}")

        current_profiles = {
            "95b530edbcf4c5132f8c51c27fa1264c99449fa1": "60839da7b582fbf6ea2ef7e8de2f051d345942e6",
            "6c06c6a7d99d500e16e88fb9597eef80fdf7bfbe": "faef8e5bbf9b68d7d9f56aacf6bd6cb48497136b",
        }
        if args.with_all_confirmed_providers and revision in current_profiles and tree != current_profiles[revision]:
            raise ValueError(f"Unexpected current integration source tree {tree}")

        with atomic_output(args.patch) as patch:
            subprocess.run(git(repo, "diff", "--binary", "--no-renames", "--full-index", revision, tree, "--", "src"),
                           stdout=patch, check=True)
        if args.locations:
            with atomic_output(args.locations) as locations:
                for name, dest in sorted(plan.location.items()):
                    print(name, dest, sep="\t", file=locations)
        for entry in restored:
            print(f"Restored {entry.name} in {entry.member}")
        print(f"Input {revision}\nOutput tree {tree}")
        print(f"{len(providers)} providers, {len(groups)} ordered groups, {len(plan.members)} source modules")


if __name__ == "__main__":
    main()
