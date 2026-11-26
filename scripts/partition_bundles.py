"""Partition existing consolidation bundles by their original access to selected modules."""

import argparse
from collections import Counter, defaultdict, deque
from contextlib import contextmanager
from dataclasses import dataclass, field
from difflib import unified_diff
from functools import cache
from graphlib import TopologicalSorter
from pathlib import Path
import os
import re
import subprocess
import tempfile
from typing import NamedTuple


HEADER = re.compile(r"^([ \t]*(?:(?:public|private|meta)[ \t]+)*import[ \t]+(?:all[ \t]+)?)([^\s/]+)([ \t]*(?:(?:--|/-)[^\n]*)?\n?)$")
MEMBER = re.compile(r"^-- bundled from (\S+)\n", re.M)
GIT_HEADER = r"^[[:space:]]*((public|private|meta)[[:space:]]+)*import[[:space:]]+|^-- bundled from "

PUBLIC = 1
ALL = 2
META = 4


def import_mode(prefix):
    words = prefix.split()
    return ((PUBLIC if "public" in words else 0) | (ALL if "all" in words else 0) |
            (META if "meta" in words else 0))


def with_mode(prefix, mode):
    if import_mode(prefix) == mode:
        return prefix
    indent = prefix[:len(prefix) - len(prefix.lstrip())]
    return (indent + ("public " if mode & PUBLIC else "") + ("meta " if mode & META else "") +
            "import " + ("all " if mode & ALL else ""))


@dataclass
class Source:
    imports: list = field(default_factory=list)
    members: list = field(default_factory=list)
    # Store exceptions to the project's usual public import.
    modes: dict = field(default_factory=dict)


def path_of(name):
    return "src/" + name.replace(".", "/") + ".lean"


def module_of(path):
    return path[4:-5].replace("/", ".")


def git(repo, *args):
    return ["git", "-C", str(repo), *args]


def stage_sources(repo, changed):
    index = []
    for module, text in sorted(changed.items()):
        oid = subprocess.check_output(git(repo, "hash-object", "-w", "--stdin"), input=text, text=True).strip()
        index.append("100644 " + oid + "\t" + path_of(module) + "\n")
    if index:
        subprocess.run(git(repo, "update-index", "--index-info"), input="".join(index), text=True, check=True)


def read_graph(repo, revision):
    paths = subprocess.check_output(git(repo, "ls-tree", "-rz", "--name-only", revision, "--", "src"))
    modules = {module_of(p): Source() for p in paths.decode().split("\0") if p.endswith(".lean")}
    with subprocess.Popen(git(repo, "grep", "--no-color", "-Iz", "-E", GIT_HEADER, revision, "--", "src"),
                            stdout=subprocess.PIPE) as proc:
        for row in proc.stdout:
            path, command = row.decode().split("\0", 1)
            source = modules.get(module_of(path.split(":", 1)[1]))
            if source is None:
                continue
            member = MEMBER.fullmatch(command)
            if member:
                source.members.append(member[1])
            else:
                match = HEADER.fullmatch(command)
                if not match:
                    raise ValueError(f"Unsupported import line in {path}: {command!r}")
                target = match[2]
                mode = import_mode(match[1])
                if target in source.imports:
                    mode |= source.modes.get(target, PUBLIC)
                source.imports.append(target)
                if mode == PUBLIC:
                    source.modes.pop(target, None)
                else:
                    source.modes[target] = mode
        if proc.wait() != 0:
            raise RuntimeError(f"Cannot read the imports at {revision}")
    return modules


class Access(NamedTuple):
    reachable: int
    exported: int
    available: int
    private_data: int


def visibility(imports, modes, provider_bits):
    masks = {}
    for module in TopologicalSorter(imports).static_order():
        reachable = exported = available = private_data = provider_bits.get(module, 0)
        for dependency in imports[module]:
            other = masks[dependency]
            mode = modes[module].get(dependency, PUBLIC)
            reachable |= other.reachable
            if mode & PUBLIC:
                exported |= other.exported
            # A regular import exposes the dependency's public imports. An all import also
            # exposes its private imports and can follow further all imports for private data.
            if mode & ALL:
                available |= other.available
                private_data |= other.private_data
            else:
                available |= other.exported
        masks[module] = Access(reachable, exported, available, private_data)
    return masks


def internal(graph):
    return {name: [d for d in source.imports if d in graph] for name, source in graph.items()}


def ordered_profiles(imports, modes, provider_ids, groups, preferred=None):
    """Project dependency-first visits onto each group of competing providers.

    With candidate headers, choose the submitted order if it gives the required
    group profiles. Return the names of the modules that can keep this order.
    """
    all_selected = len(groups) == 1 and len(groups[0]) == len(provider_ids)
    groups_by_id = defaultdict(list)
    for group_id, group in enumerate(groups):
        for provider in group:
            groups_by_id[provider_ids[provider]].append(group_id)

    @cache
    def project(order):
        if all_selected:
            return order
        by_group = defaultdict(list)
        for provider in order:
            for group_id in groups_by_id[provider]:
                by_group[group_id].append(provider)
        # The access mask already records all single providers.
        return tuple((g, tuple(values)) for g, values in sorted(by_group.items()) if len(values) > 1)

    @cache
    def join(chunks, provider):
        seen = dict.fromkeys(item for chunk in chunks for item in chunk)
        if provider is not None:
            seen[provider] = None
        return tuple(seen)

    orders = {}
    profiles = {}
    kept = set()

    def read(name, dependencies):
        reachable, exported, available, private_data = [], [], [], []
        for dependency in dependencies:
            child = orders[dependency]
            mode = modes[name].get(dependency, PUBLIC)
            reachable.append(child[0])
            if mode & PUBLIC:
                exported.append(child[1])
            if mode & ALL:
                available.append(child[2])
                private_data.append(child[3])
            else:
                available.append(child[1])
        provider = provider_ids.get(name)
        return tuple(join(tuple(part for part in scope if part), provider)
                     for scope in (reachable, exported, available, private_data))

    for name in TopologicalSorter(imports).static_order():
        if preferred is not None:
            dependencies, required = preferred[name]
            candidate = read(name, dependencies)
            profile = tuple(map(project, candidate))
            if profile == required:
                orders[name], profiles[name] = candidate, profile
                kept.add(name)
                continue
        orders[name] = read(name, imports[name])
        profiles[name] = tuple(map(project, orders[name]))
    return profiles, kept


class Partition:
    def __init__(self, original, bundled, providers, order_groups=()):
        self.order_groups = order_groups
        self.bundled = bundled
        self.owner = {}
        for bundle, source in bundled.items():
            for member in source.members or [bundle]:
                if member not in original or member in self.owner:
                    raise ValueError(f"Expected one original source for {member}")
                self.owner[member] = bundle
        if len(set(providers)) != len(providers) or any(n not in self.owner for n in providers):
            raise ValueError("Each provider must be a distinct, retained original module")

        bits = {n: 1 << i for i, n in enumerate(providers)}
        dependencies = internal(original)
        modes = {n: source.modes for n, source in original.items()}
        original_mask = visibility(dependencies, modes, bits)
        ids = {name: i for i, name in enumerate(providers)}
        prior_order = {}
        if order_groups:
            prior_order, _ = ordered_profiles(dependencies, modes, ids, order_groups)
        self.members = {}
        self.location = {}
        self.previous = {}
        for bundle, source in bundled.items():
            partitions = defaultdict(list)
            for member in source.members or [bundle]:
                partitions[(original_mask[member], prior_order.get(member))].append(member)
            largest = max(partitions, key=lambda mask: len(partitions[mask]))
            for mask, group in partitions.items():
                destination = bundle if mask == largest else group[0]
                if destination in self.members:
                    raise ValueError(f"Bundle name collision at {destination}")
                self.members[destination] = group
                self.previous[destination] = bundle
                self.location.update((member, destination) for member in group)

        @cache
        def expand(name, mode):
            if name in self.owner or name not in original:
                return ((name, mode),)
            leaves = []
            for d in original[name].imports:
                child = original[name].modes.get(d, PUBLIC)
                if not (mode & ALL or child & PUBLIC):
                    raise ValueError(f"Direct imports cannot express the private edge {name} -> {d} "
                                     "through a removed wrapper")
                combined = (mode & child & (PUBLIC | ALL)) | ((mode | child) & META)
                leaves.extend(expand(d, combined))
            return tuple(dict.fromkeys(leaves))

        self.replacements = {}
        self.imports = {}
        self.modes = {}
        submitted_headers = {}
        prior_edges = defaultdict(set)
        for destination, group in self.members.items():
            parent = self.previous[destination]
            replacements = defaultdict(list)
            modes = {}
            for member in group:
                for dependency in original[member].imports:
                    mode = original[member].modes.get(dependency, PUBLIC)
                    for leaf, leaf_mode in expand(dependency, mode):
                        before = self.owner.get(leaf, leaf)
                        after = self.location.get(leaf, leaf)
                        if before == parent and after != destination:
                            raise ValueError(f"Dependent members in the original bundle {parent}")
                        if before != parent:
                            prior_edges[parent].add(before)
                        if after != destination:
                            modes[after] = modes.get(after, 0) | leaf_mode
                            if after not in replacements[before]:
                                replacements[before].append(after)
            self.replacements[destination] = replacements
            self.modes[destination] = {d: mode for d, mode in modes.items() if mode != PUBLIC}
            submitted = [d for old in bundled[parent].imports for d in replacements[old]]
            if order_groups:
                submitted_headers[destination] = submitted
                # modes has the first-seen order of the original, expanded dependencies.
                multiplicity = Counter(submitted)
                self.imports[destination] = [d for d in modes for _ in range(multiplicity[d])]
            else:
                self.imports[destination] = submitted
        for parent, source in bundled.items():
            if prior_edges[parent] != set(source.imports):
                raise ValueError(f"Wrapper expansion does not reproduce the submitted imports of {parent}")

        def relocated(mapping):
            masks = defaultdict(int)
            for provider, bit in bits.items():
                masks[mapping[provider]] |= bit
            return masks

        before = visibility(internal(bundled), {n: s.modes for n, s in bundled.items()}, relocated(self.owner))
        self.graph = {n: [d for d in deps if d in self.members] for n, deps in self.imports.items()}
        after = visibility(self.graph, self.modes, relocated(self.location))
        self.differences = {m: (original_mask[m].reachable, before[parent].reachable)
                            for m, parent in self.owner.items() if original_mask[m].reachable != before[parent].reachable}
        self.scope_counts = Access(*(sum(original_mask[m][i] != before[parent][i]
                                         for m, parent in self.owner.items()) for i in range(len(Access._fields))))
        for member, target in self.location.items():
            if after[target] != original_mask[member]:
                raise ValueError(f"The partition changed provider access for {member} in {target}")

        if order_groups:
            relocated_ids = {self.location[name]: i for name, i in ids.items()}
            if len(relocated_ids) != len(ids):
                raise ValueError("Ordered providers must have distinct output modules")
            preferred = {n: ([d for d in deps if d in self.members], prior_order[self.members[n][0]])
                         for n, deps in submitted_headers.items()}
            actual_order, kept = ordered_profiles(self.graph, self.modes, relocated_ids,
                                                  [[self.location[n] for n in group] for group in order_groups],
                                                  preferred)
            for target in kept:
                self.graph[target] = preferred[target][0]
                self.imports[target] = submitted_headers[target]
            for member, target in self.location.items():
                if actual_order[target] != prior_order[member]:
                    raise ValueError(f"The partition changed provider order for {member} in {target}")

    def changed(self, n):
        parent = self.previous[n]
        old = self.bundled[parent]
        return (n != parent or self.members[n] != (old.members or [parent]) or
                self.imports[n] != old.imports or self.modes[n] != old.modes)

    def render(self, n, raw):
        if not self.changed(n):
            return raw
        markers = list(MEMBER.finditer(raw))
        header = raw[:markers[0].start()] if markers else raw
        lines = []
        for line in header.splitlines(keepends=True):
            match = HEADER.fullmatch(line)
            if match:
                for dep in self.replacements[n][match[2]]:
                    mode = self.modes[n].get(dep, PUBLIC)
                    same_mode = self.bundled[self.previous[n]].modes.get(match[2], PUBLIC) == mode
                    # Keep separate public and import-all lines when their joint access stays the same.
                    prefix = match[1] if self.order_groups and same_mode else with_mode(match[1], mode)
                    lines.append(prefix + dep + match[3])
            else:
                lines.append(line)
        if self.order_groups:
            slots = [i for i, line in enumerate(lines) if HEADER.fullmatch(line)]
            by_target = defaultdict(deque)
            for i in slots:
                by_target[HEADER.fullmatch(lines[i])[2]].append(lines[i])
            if {dep: len(items) for dep, items in by_target.items()} != Counter(self.imports[n]):
                raise ValueError(f"Cannot reproduce the ordered import header of {n}")
            for i, target in zip(slots, self.imports[n]):
                lines[i] = by_target[target].popleft()
        if markers:
            keep = set(self.members[n])
            for j, marker in enumerate(markers):
                if marker[1] in keep:
                    end = markers[j + 1].start() if j + 1 < len(markers) else len(raw)
                    lines.append(raw[marker.start():end])
        return "".join(lines)

    def cone(self, targets):
        seen = set()
        pending = list(targets)
        while pending:
            current = pending.pop()
            if current not in seen:
                seen.add(current)
                pending.extend(self.graph[current])
        return seen


def write_outputs(plan, repo, ref, targets, patchfile, output):
    cone = plan.cone(targets) if output else set()
    changed = {n for n in plan.members if plan.changed(n)} if patchfile else set()
    pipe = subprocess.Popen(git(repo, "cat-file", "--batch"), stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    try:
        for n in sorted(cone | changed):
            parent = plan.previous[n]
            pipe.stdin.write(f"{ref}:{path_of(parent)}\n".encode())
            pipe.stdin.flush()
            fields = pipe.stdout.readline().split()
            if len(fields) != 3 or fields[1] != b"blob":
                raise ValueError(f"Missing source {parent}")
            raw = pipe.stdout.read(int(fields[2])).decode()
            pipe.stdout.read(1)
            updated = plan.render(n, raw)
            if n in cone:
                path = output / path_of(n)
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(updated)
            if n in changed:
                old = raw if n == parent else ""
                prior = "a/" + path_of(n) if n == parent else "/dev/null"
                patchfile.writelines(unified_diff(old.splitlines(True), updated.splitlines(True),
                                                  fromfile=prior, tofile="b/" + path_of(n)))
    finally:
        pipe.stdin.close()
        pipe.stdout.close()
        pipe.wait()


@contextmanager
def atomic_output(path):
    # Replace the output only after all its records are ready.
    tmp = tempfile.NamedTemporaryFile(mode="w", dir=path.parent, delete=False)
    try:
        with tmp:
            yield tmp
        os.replace(tmp.name, path)
    finally:
        Path(tmp.name).unlink(missing_ok=True)


def changed_providers(mask, providers):
    while mask:
        bit = mask & -mask
        yield providers[bit.bit_length() - 1]
        mask ^= bit


def read_order_groups(path):
    groups = {}
    for line in path.read_text().splitlines():
        if not line.strip():
            continue
        label, *names = line.split("\t")
        if not label or label in groups or len(set(names)) != len(names) or len(names) < 2 or "" in names:
            raise ValueError(f"Expected a unique label and at least two distinct providers in {line!r}")
        groups[label] = names
    if not groups:
        raise ValueError("The order group file is empty")
    return list(groups.values())


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--repo", type=Path, default=Path("."))
    cli.add_argument("--base", required=True, help="revision before the wrapper and bundle passes")
    cli.add_argument("--consolidated", required=True, help="revision containing the submitted bundles")
    cli.add_argument("--provider", action="append", default=[], help="original module to protect")
    order = cli.add_mutually_exclusive_group()
    order.add_argument("--preserve-order", action="store_true",
                       help="preserve the relative visit order of all selected providers")
    order.add_argument("--order-groups", type=Path,
                       help="select providers and preserve order within each labeled tab-separated group")
    cli.add_argument("--provider-list", type=Path, help="file with one original provider module per line")
    cli.add_argument("--patch", type=Path, help="write the complete source patch")
    cli.add_argument("--affected", type=Path, help="write one TSV row per original module with a changed provider set")
    cli.add_argument("--target", action="append", default=[], help="retained original module to inspect")
    cli.add_argument("--materialize", type=Path, help="write the source closure of the selected targets here")
    args = cli.parse_args()
    providers = args.provider.copy()
    if args.provider_list:
        providers.extend(s for line in args.provider_list.read_text().splitlines() if (s := line.strip()))
    groups = read_order_groups(args.order_groups) if args.order_groups else []
    if groups:
        known = set(providers)
        for group in groups:
            for name in group:
                if name not in known:
                    providers.append(name)
                    known.add(name)
    elif args.preserve_order:
        groups = [providers]
    if not providers:
        cli.error("specify at least one provider with --provider or --provider-list")
    if args.materialize and not args.target:
        cli.error("--materialize requires --target")
    base, consolidated = (subprocess.check_output(
        git(args.repo, "rev-parse", "--verify", "--end-of-options", rev + "^{commit}"), text=True).strip()
        for rev in (args.base, args.consolidated))
    original = read_graph(args.repo, base)
    bundled = read_graph(args.repo, consolidated)
    plan = Partition(original, bundled, providers, groups)
    print(f"Source modules: {len(bundled)} -> {len(plan.members)}")
    print(f"Provider reachability differences across {len(plan.location)} retained origins: {len(plan.differences)} -> 0")
    print(f"Provider access differences by scope: public exports {plan.scope_counts.exported} -> 0, "
          f"module bodies {plan.scope_counts.available} -> 0, private data {plan.scope_counts.private_data} -> 0")
    if groups:
        print(f"Verified provider order in {len(groups)} groups across {len(plan.location)} retained origins")
    print(f"New or changed source files: {sum(plan.changed(n) for n in plan.members)}")
    destinations = []
    for target in args.target:
        if target not in plan.location:
            cli.error(f"{target} is not a retained original module")
        destination = plan.location[target]
        destinations.append(destination)
        print(f"{target} -> {destination} ({len(plan.cone([destination]))} project modules)")
    if args.affected:
        with atomic_output(args.affected) as report:
            print("origin", "submitted_module", "corrected_module", "added_in_submitted", "missing_in_submitted",
                  sep="\t", file=report)
            for n, (prior, submitted) in sorted(plan.differences.items()):
                added = changed_providers(submitted & ~prior, providers)
                missing = changed_providers(prior & ~submitted, providers)
                print(n, plan.owner[n], plan.location[n], ",".join(added), ",".join(missing), sep="\t", file=report)
    if args.patch:
        with atomic_output(args.patch) as patch:
            write_outputs(plan, args.repo, consolidated, destinations, patch, args.materialize)
    elif args.materialize:
        write_outputs(plan, args.repo, consolidated, destinations, None, args.materialize)


if __name__ == "__main__":
    main()
