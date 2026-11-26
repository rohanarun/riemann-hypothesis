"""Move the eight additional PR 120 imports with their original consumers."""

from collections import defaultdict
import subprocess

from partition_bundles import HEADER, PUBLIC, git, internal, import_mode, ordered_profiles, path_of, stage_sources, visibility


BASE_AUTHOR_REVISION = "f94106583626ad6b48ac6e239e0b2e5ffc879555"
AUTHOR_REVISION = "b4f6cadcb41210ca3480d16021fd981cdca551a0"


def read_routes(file):
    routes = defaultdict(lambda: defaultdict(list))
    for line in file.read_text().splitlines():
        consumer, added, original, provider = line.split("\t")
        routes[consumer][added].append((original, provider))
    return routes


def source(repo, revision, module):
    return subprocess.check_output(git(repo, "show", revision + ":" + path_of(module)), text=True)


def check_original_routes(original, routes):
    providers = list(dict.fromkeys(provider for by_dep in routes.values() for pairs in by_dep.values()
                                   for _, provider in pairs))
    bits = {name: 1 << i for i, name in enumerate(providers)}
    scopes = visibility(internal(original), {name: source.modes for name, source in original.items()}, bits)
    for by_dep in routes.values():
        for pairs in by_dep.values():
            for member, provider in pairs:
                if not scopes[member].exported & bits[provider]:
                    raise ValueError(f"{provider} was not a public dependency of the original {member}")


def take_imports(repo, stage, routes, replacements=None):
    """Take only surviving author additions out of their submitted headers."""
    changed = {}
    active = {}
    for module, additions in routes.items():
        raw = source(repo, stage, module)
        before = source(repo, BASE_AUTHOR_REVISION, module)
        pinned = source(repo, AUTHOR_REVISION, module)
        first = "public import Mathlib\n"
        actual = []
        selected = {}
        for dep, original_uses in additions.items():
            line = "public import " + dep + "\n"
            if pinned.splitlines(keepends=True).count(line) != before.splitlines(keepends=True).count(line) + 1:
                raise ValueError(f"Cannot identify the original author addition of {dep} in {module}")
            candidates = [dep]
            if replacements and dep in replacements:
                candidates.append(replacements[dep])
            retained = []
            for name in candidates:
                command = "public import " + name + "\n"
                difference = raw.splitlines(keepends=True).count(command) - before.splitlines(keepends=True).count(command)
                if difference == 1:
                    retained.append(command)
                elif difference != 0:
                    raise ValueError(f"The number of imports of {name} in {module} changed unexpectedly")
            if len(retained) > 1:
                raise ValueError(f"Both spellings of the author import of {dep} occur in {module}")
            if retained:
                actual.extend(retained)
                selected[dep] = original_uses
        if actual:
            header = first + "".join(actual)
            if raw.count(header) != 1:
                raise ValueError(f"The reviewed author import positions have changed in {module}")
            changed[module] = raw.replace(header, first, 1)
            active[module] = selected
    stage_sources(repo, changed)
    return active


def restore_imports(repo, stage, routes, plan, providers, groups):
    """Put each author import into the output file of its original source member."""
    additions = defaultdict(list)
    for old_target, entries in routes.items():
        for old_dependency, pairs in entries.items():
            destinations = defaultdict(dict)
            for member, provider in pairs:
                if plan.owner[member] != old_target:
                    raise ValueError(f"{old_target} has no original member {member}")
                # Three author lines name wrappers that PR 120 removed.
                if old_dependency in plan.bundled and plan.owner[provider] != old_dependency:
                    raise ValueError(f"{old_dependency} does not supply {provider}")
                target = plan.location[member]
                dep = plan.location[provider]
                if target != dep:
                    destinations[target][dep] = None
            for target, deps in destinations.items():
                additions[target].extend(deps)

    bits = {plan.location[p]: 1 << i for i, p in enumerate(providers)}
    ids = {plan.location[p]: i for i, p in enumerate(providers)}
    order_groups = [[plan.location[p] for p in group] for group in groups]
    before_scope = visibility(plan.graph, plan.modes, bits)
    before_order, _ = ordered_profiles(plan.graph, plan.modes, ids, order_groups)
    changed = {}
    for target, deps in additions.items():
        raw = source(repo, stage, target)
        marker = "public import Mathlib\n"
        if raw.count(marker) != 1:
            raise ValueError(f"Cannot locate the import header in {target}")
        source_text = raw.replace(marker, marker + "".join("public import " + dep + "\n" for dep in deps), 1)
        imports = []
        modes = {}
        for line in source_text.splitlines(keepends=True):
            if match := HEADER.fullmatch(line):
                dep = match[2]
                modes[dep] = modes.get(dep, 0) | import_mode(match[1])
                imports.append(dep)
        plan.imports[target] = imports
        plan.graph[target] = [dep for dep in imports if dep in plan.members]
        plan.modes[target] = {dep: flag for dep, flag in modes.items() if flag != PUBLIC}
        changed[target] = source_text

    after_scope = visibility(plan.graph, plan.modes, bits)
    after_order, _ = ordered_profiles(plan.graph, plan.modes, ids, order_groups)
    for target in plan.members:
        if before_scope[target] != after_scope[target] or before_order[target] != after_order[target]:
            raise ValueError(f"The new imports change the protected choices in {target}")
    stage_sources(repo, changed)
    return dict(additions)
