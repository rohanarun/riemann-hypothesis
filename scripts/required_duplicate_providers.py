"""Check which original duplicate declarations are available after a bundle split."""
from collections import defaultdict
from dataclasses import dataclass
from functools import cache
from graphlib import TopologicalSorter
import re
import subprocess

from partition_bundles import ALL, MEMBER, PUBLIC, git, internal, path_of, stage_sources


# The original compiler ranges refer to these Git blobs.
DECLARATION_SOURCE = "c7791603122c0328f79e49f6be5d7d4402effc53"
BEFORE_DUPLICATE_CLEANUP = "4793b67cd48b6dc62be9240999af7465ef7499b2"


@dataclass(frozen=True)
class Origin:
    name: str
    member: str
    bundle: str
    token: str
    public: bool
    rename: str
    bounds: tuple[int, int, int, int]


def read_origins(file):
    origins = defaultdict(list)
    for line in file.read_text().splitlines():
        name, member, bundle, token, visibility, rename, *bounds = line.split("\t")
        if visibility not in {"public", "private"} or len(bounds) != 4:
            raise ValueError(f"Invalid original declaration record for {name}")
        origins[member].append(Origin(name, member, bundle, token, visibility == "public", rename,
                                      tuple(map(int, bounds))))
    return origins


def member_bounds(source, member):
    markers = list(MEMBER.finditer(source))
    if not markers:
        return 0, len(source)
    for i, mark in enumerate(markers):
        if mark[1] == member:
            end = markers[i + 1].start() if i + 1 < len(markers) else len(source)
            return mark.start(), end
    raise ValueError(f"Missing member {member}")


# Lean block comments can nest. Ignore quoted text when looking for a comment opener.
TRIVIA = re.compile(r'/-|--[^\n]*|(?<![\w\'])r(?P<hashes>#+)"|"(?:[^"\\]|\\[\s\S])*"|«[^»]*»')
COMMENT = re.compile(r"/-|-/")
COMMAND = (r"^[ \t]*(?:@\[[^\]\n]+\][ \t]*)*"
           r"(?P<modifiers>(?:(?:public|private|protected|noncomputable|unsafe|partial)\s+)*)"
           r"(?:theorem|lemma|def|abbrev|opaque|axiom|inductive|structure|class|instance)\s+")


def source_commands(text):
    pieces = []
    offset = 0
    while match := TRIVIA.search(text, offset):
        pieces.append(text[offset:match.start()])
        end = match.end()
        if match[0] == "/-":
            depth = 1
            for mark in COMMENT.finditer(text, end):
                depth += 1 if mark[0] == "/-" else -1
                if not depth:
                    end = mark.end()
                    break
            else:
                raise ValueError("Unclosed Lean block comment")
        elif match["hashes"]:
            closing = '"' + match["hashes"]
            stop = text.find(closing, end)
            if stop < 0:
                raise ValueError("Unclosed Lean raw string")
            end = stop + len(closing)
        pieces.append(" " + "\n" * text.count("\n", match.start(), end))
        offset = end
    return "".join(pieces) + text[offset:]


def declaration_visibility(source, token):
    matches = list(re.finditer(COMMAND + re.escape(token) + r"(?![\w'.])", source_commands(source), re.M))
    if len(matches) > 1:
        raise ValueError(f"Ambiguous source declaration {token}")
    return "private" not in matches[0]["modifiers"].split() if matches else None


def declared(source, token):
    return declaration_visibility(source, token) is not None


def inherited(dependencies, modes, known):
    exported = available = 0
    for dep in dependencies:
        public, body = known[dep]
        flag = modes.get(dep, PUBLIC)
        if flag & PUBLIC:
            exported |= public
        available |= body if flag & ALL else public
    return exported, available


def command_at(source, bounds):
    lines = source.splitlines(keepends=True)
    def offset(line, units):
        column = len(lines[line].encode("utf-16-le")[:2 * units].decode("utf-16-le"))
        return sum(map(len, lines[:line])) + column
    return source[offset(*bounds[:2]):offset(*bounds[2:])]


def retain_calling_conventions(repo, stage, file):
    """Use the author's full argument list with either original binder convention."""
    edited = {}
    for line in file.read_text().splitlines():
        physical, member, original_call, full_call = line.split("\t")
        current = edited.get(physical)
        if current is None:
            current = subprocess.check_output(git(repo, "show", stage + ":" + path_of(physical)), text=True)
        start, end = member_bounds(current, member)
        body = current[start:end]
        explicit = "@" + full_call
        original_count, full_count = body.count(original_call), body.count(full_call)
        if (original_count, full_count) == (1, 0):
            continue
        if (original_count, full_count) != (0, 1):
            raise ValueError(f"Cannot identify the reviewed application of {full_call} in {member}")
        if explicit in body:
            continue
        edited[physical] = current[:start] + body.replace(full_call, explicit, 1) + current[end:]
    stage_sources(repo, edited)


def retain_author_qualifications(repo, stage, author, origins, table, location=None):
    """Use the author's complete qualified command when restoring a removed helper."""
    edited = {}
    for line in table.read_text().splitlines():
        member, name, short, qualified = line.split("\t")
        entries = [o for o in origins[member] if o.name == name]
        if len(entries) != 1:
            raise ValueError(f"Cannot identify the original declaration {name} in {member}")
        origin = entries[0]
        old = subprocess.check_output(git(repo, "show", DECLARATION_SOURCE + ":" + path_of(member)), text=True)
        original = command_at(old, origin.bounds)
        token = r"(?<![\w'.])" + re.escape(short) + r"(?![\w'.])"
        updated = re.sub(token, qualified, original)
        author_body = subprocess.check_output(git(repo, "show", author + ":" + path_of(origin.bundle)), text=True)
        a, b = member_bounds(author_body, member)
        if updated == original or author_body[a:b].count(updated) != 1:
            raise ValueError(f"The author command for {name} no longer matches the reviewed qualification")
        target = location[member] if location else origin.bundle
        raw = edited.get(target)
        if raw is None:
            raw = subprocess.check_output(git(repo, "show", stage + ":" + path_of(target)), text=True)
        a, b = member_bounds(raw, member)
        body = raw[a:b]
        if updated in body:
            continue
        if body.count(original) != 1:
            raise ValueError(f"Cannot locate the restored original command for {name} in {target}")
        edited[target] = raw[:a] + body.replace(original, updated, 1) + raw[b:]
    stage_sources(repo, edited)


def restore_providers(repo, stage, original, plan, origins, work):
    """Restore a declaration when the resulting public scope has no supplier for it."""
    @cache
    def read(ref, module):
        return subprocess.check_output(git(repo, "show", ref + ":" + path_of(module)), text=True)

    names = sorted({entry.name for rows in origins.values() for entry in rows})
    bits = {name: 1 << i for i, name in enumerate(names)}
    dependency_graph = internal(original)
    expected = {}
    for n in TopologicalSorter(dependency_graph).static_order():
        public, body = inherited(dependency_graph[n], original[n].modes, expected)
        for entry in origins.get(n, []):
            if entry.public:
                public |= bits[entry.name]
                body |= bits[entry.name]
        expected[n] = public, body

    for member, entries in origins.items():
        source = read(DECLARATION_SOURCE, member)
        for entry in entries:
            command = command_at(source, entry.bounds)
            if declaration_visibility(command, entry.token) != entry.public:
                raise ValueError(f"Original compiler range does not contain {entry.name} in {member}")

    changes = defaultdict(list)
    covered = {}
    for target in TopologicalSorter(plan.graph).static_order():
        public, body = inherited(plan.graph[target], plan.modes[target], covered)
        for m in plan.members[target]:
            if m not in origins:
                continue
            raw = read(stage, target)
            start, end = member_bounds(raw, m)
            text = raw[start:end]
            for entry in origins[m]:
                bit = bits[entry.name]
                if entry.rename and declared(text, entry.rename):
                    continue
                local_visibility = declaration_visibility(text, entry.token)
                if local_visibility is not None and local_visibility != entry.public:
                    raise ValueError(f"Declaration visibility changed for {entry.name} in {member}")
                present = local_visibility is not None
                if present and entry.public and public & bit:
                    raise ValueError(f"Duplicate declaration {entry.name} in {target}")
                available = public if entry.public else body
                if not present and not available & bit:
                    if entry.public and body & bit:
                        raise ValueError(f"Only a private import supplies {entry.name} in {target}")
                    changes[m].append(entry)
                    present = True
                if present and entry.public:
                    public |= bit
                    body |= bit
        covered[target] = public, body

    for member, target in plan.location.items():
        if any(before & ~after for before, after in zip(expected[member], covered[target])):
            raise ValueError(f"Missing original duplicate declarations in {member} from {target}")

    edited = {}
    for member, missing in changes.items():
        target = plan.location[member]
        current = edited.get(target, read(stage, target))
        lo, hi = member_bounds(current, member)
        prior = read(BEFORE_DUPLICATE_CLEANUP, missing[0].bundle)
        start, end = member_bounds(prior, member)
        historical = prior[start:end]
        without = historical
        for entry in missing:
            command = command_at(read(DECLARATION_SOURCE, member), entry.bounds)
            if not declared(command, entry.token) or without.count(command) != 1:
                raise ValueError(f"Cannot locate the original command {entry.name} in {member}")
            left, right = without.split(command, 1)
            if right.startswith("\n\n"):
                right = right[2:]
            elif right.startswith("\n"):
                right = right[1:]
            without = left + right
        inputs = [work / name for name in ("current.lean", "without.lean", "original.lean")]
        for file, text in zip(inputs, (current[lo:hi], without, historical)):
            file.write_text(text)
        command = ["git", "merge-file", "-p", *map(str, inputs)]
        merged = subprocess.run(command, capture_output=True, text=True)
        if merged.returncode:
            raise ValueError(f"Cannot restore the original declaration in {member}")
        for entry in missing:
            if not declared(merged.stdout, entry.token):
                raise ValueError(f"The merged source lacks {entry.name}")
        edited[target] = current[:lo] + merged.stdout + current[hi:]

    stage_sources(repo, edited)
    return [entry for entries in changes.values() for entry in entries]
