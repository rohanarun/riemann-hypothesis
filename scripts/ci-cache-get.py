#!/usr/bin/env python3
"""Restore the published build cache for the current clean build inputs of this project.

Adapted from scripts/ci-cache-get.py of leanprover-community/riemann-hypothesis (main). The
differences are: records, maps, module manifests and artifacts are read from a namespace of
their own (grh-lean/grh/ and artifacts/<repo>-grh-lean/grh/), shared with the grh/ project of
branch grh-lean-cache and separate from the keys of the earlier main branch; the project may be
a subdirectory of its Git repository; and records are looked up by input fingerprint only.

With --baseline <ref>, a miss falls back to a baseline: the record of the
nearest first-parent ancestor of <ref> that has one, else the record pinned in
scripts/cache-baseline.json. Candidates are looked up by their own input fingerprint, computed
from Git objects with the same code, and must have the current toolchain and lake-manifest.json
(otherwise no module would be reused). The baseline's map and module manifest are checked
exactly as for an exact match, but against the baseline's inputs. Its modules are unpacked, and
`lake build` then compiles the modules whose inputs differ (Lake compares each module's trace
with its current inputs) and keeps the rest. Exit 4 means a baseline was restored.

The record's immutable map and module manifest are checked against its SHA-256 values and
against each other. Then, at the same time, the map is registered with `lake cache add` in
parallel shards and the missing artifacts are downloaded by one 500-way curl process, each
checked against the manifest's SHA-256 before it enters the cache (fetch-artifacts.py). Then one
stock leantar process unpacks every module (after path checks), and `lake build --no-build`
confirms that nothing would have to be compiled.

The cache does not verify any proof: it only holds what a build produced for these inputs.

Exit 3 means no record for these inputs was found. Other failures must not silently fall back:
a matching record with corrupt bytes is an error.
"""
import argparse
import gzip
import hashlib
import http.client
import importlib.util
import io
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time
import tomllib
import urllib.error
import urllib.request

PUBLIC_BASE = "https://rh-cache.taucetiproject.org"
PROJECT = "grh"
REPOSITORY = "leanprover-community/riemann-hypothesis"
SCOPE = f"{REPOSITORY}-grh-lean/{PROJECT}"  # artifacts/<SCOPE>/<hash>.art
PREFIX = f"grh-lean/{PROJECT}"  # records, maps and module manifests
FIELDS = ("source_tree", "build_roots", "lakefile_sha256", "manifest_sha256", "toolchain")
SHA40 = re.compile(r"[0-9a-f]{40}\Z")
SHA256 = re.compile(r"[0-9a-f]{64}\Z")
HASH = re.compile(r"[0-9a-f]{16}\Z")
ARTIFACT = re.compile(r"[0-9a-f]{16}\.ltar\Z")
MODULE = re.compile(r"[\w']+(?:\.[\w']+)*\Z")  # Unicode names occur in the tree.
SCHEMA = "2026-03-17"
USER_AGENT = "RiemannHypothesisCache/1.0"
SHARDS = 16
MAX_JSON = 64 * 1024 * 1024
MAX_RECEIPT = 2 * 1024 * 1024
MAX_MODULES = 500000

FETCH_ARTIFACTS = Path(__file__).resolve().with_name("fetch-artifacts.py")

def digest(value):
    return hashlib.sha256(value).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()


def fingerprint(identity):
    return digest(canonical({key: identity[key] for key in FIELDS}))


def _pairs(pairs):
    value = {}
    for key, item in pairs:
        if key in value:
            raise ValueError(f"duplicate JSON field: {key}")
        value[key] = item
    return value


def decode(value):
    return json.loads(value, object_pairs_hook=_pairs)


def local_path(root, relative, checked):
    """Reject unsafe parts and symlinks in a path below root, including existing leaves.

    Populate the ancestor-closed ``checked`` set only through this helper.
    """
    if any(part in ("", ".", "..") or "/" in part or "\\" in part
           for part in relative.parts):
        raise ValueError("unsafe module path")
    path = root / relative
    pending = []
    current = path
    while current != root and current not in checked:
        pending.append(current)
        current = current.parent
    for current in reversed(pending):
        if current.is_symlink():
            raise ValueError(f"symlink in source/output path: {current}")
        checked.add(current)
    return path


def git(root, *args, quiet=False):
    return subprocess.check_output(["git", "-C", str(root), *args], text=True,
                                   stderr=subprocess.DEVNULL if quiet else None).strip()


def current_identity(root):
    """Bind actual files and the clean Git src tree, without the initial archive's pins."""
    checked = set()
    files = {}
    for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
        path = local_path(root, Path(name), checked)
        if not path.is_file() or path.stat().st_size > MAX_JSON:
            raise ValueError(f"expected a bounded regular input: {name}")
        files[name] = path.read_bytes()
    local_path(root, Path("src"), checked)
    subprocess.run(["git", "-C", str(root), "diff", "--no-ext-diff", "--no-textconv", "--quiet",
                    "HEAD", "--", "src", *files], check=True)
    if git(root, "ls-files", "--others", "--", "src"):
        raise ValueError("untracked source files differ from HEAD")
    config = tomllib.loads(files["lakefile.toml"].decode())
    if (config.get("srcDir", ".") != "src" or config.get("extern_lib")
            or any(key in config for key in ("buildDir", "leanLibDir", "irDir", "packagesDir", "manifestFile"))
            or any(lib.get("srcDir", ".") != "." for lib in config.get("lean_lib", []) if lib.get("name") != "Challenge")):
        raise ValueError("public CI restoration currently supports the attested src/default build layout")
    identity = {
        "source_tree": git(root, "rev-parse", "HEAD:./src"), "build_roots": {},
        "lakefile_sha256": digest(files["lakefile.toml"]),
        "manifest_sha256": digest(files["lake-manifest.json"]),
        "toolchain": files["lean-toolchain"].decode().strip(),
    }
    if not SHA40.fullmatch(identity["source_tree"]):
        raise ValueError("invalid current src Git tree")
    return identity


def fetch(key, maximum=MAX_JSON):
    """GET a public key; None on 404. Retries CDN 5xx and transport errors."""
    request = urllib.request.Request(
        PUBLIC_BASE + "/" + key,
        headers={"User-Agent": USER_AGENT, "Cache-Control": "no-cache"})
    for attempt in range(6):
        try:
            with urllib.request.urlopen(request, timeout=60) as response:
                if response.status != 200:
                    raise ValueError(f"unexpected cache HTTP status: {response.status}")
                data = response.read(maximum + 1)
            break
        except urllib.error.HTTPError as error:
            if error.code == 404:
                return None
            if error.code < 500 or attempt == 5:
                raise
        except (urllib.error.URLError, TimeoutError, ConnectionError, http.client.HTTPException) as error:
            if attempt == 5:
                raise ValueError(f"could not fetch {key}: {error}") from error
        time.sleep(2 ** attempt)
    if len(data) > maximum:
        raise ValueError(f"public metadata exceeds size limit: {key}")
    return data


def matching_record(data, identity):
    record = decode(data)
    if (not isinstance(record, dict) or type(record.get("schema")) is not int or record["schema"] != 1
            or record.get("repository") != REPOSITORY or record.get("project") != PROJECT):
        raise ValueError("unexpected public CI receipt scope/schema")
    code = record.get("build_exit_code")
    if type(code) is not int or not 0 <= code <= 255:
        raise ValueError("invalid CI build exit code")
    if code != 0 or any(record.get(key) != identity[key] for key in FIELDS):
        return None
    if record.get("input_fingerprint") != fingerprint(identity):
        raise ValueError("successful CI receipt input fingerprint mismatch")
    for key in ("candidate_head", "candidate_tree"):
        if not isinstance(record.get(key), str) or not SHA40.fullmatch(record[key]):
            raise ValueError(f"invalid CI receipt {key}")
    for field, prefix, suffix in (("map", PREFIX + "/maps/", ".jsonl"),
                                  ("module_manifest", PREFIX + "/module-manifests/", ".jsonl.gz")):
        value = record.get(field + "_sha256")
        if (not isinstance(value, str) or not SHA256.fullmatch(value)
                or record.get(field + "_key") != prefix + value + suffix):
            raise ValueError(f"invalid immutable CI {field} identity")
    size = record.get("module_manifest_bytes")
    if type(size) is not int or not 0 < size <= MAX_JSON:
        raise ValueError("invalid CI module manifest size")
    nested = record.get("receipt")
    if nested is not None:
        if not isinstance(nested, dict) or any(nested.get(key) != record[key]
                for key in (*FIELDS, "candidate_head", "candidate_tree", "input_fingerprint", "build_exit_code")):
            raise ValueError("nested CI receipt differs from its public identity")
    return record


def find_record(identity, fetcher=fetch):
    data = fetcher(f"{PREFIX}/inputs/{fingerprint(identity)}.json", MAX_RECEIPT)
    return None if data is None else matching_record(data, identity)


def blob_sha256(root, revision, name, memo):
    """SHA-256 and bytes of a file at a revision, memoised by blob id."""
    oid = git(root, "rev-parse", "--verify", "--quiet", f"{revision}:{name}", quiet=True)
    if oid not in memo:
        if git(root, "cat-file", "-t", oid) != "blob" or int(git(root, "cat-file", "-s", oid)) > MAX_JSON:
            raise ValueError(f"expected a bounded file: {name} at {revision}")
        data = subprocess.check_output(["git", "-C", str(root), "cat-file", "blob", oid])
        memo[oid] = (digest(data), data)
    return memo[oid]


def identity_at(root, revision, memo):
    """The build inputs of a commit, from Git objects, in the form of current_identity."""
    tree = git(root, "rev-parse", "--verify", "--quiet", f"{revision}:src", quiet=True)
    if not SHA40.fullmatch(tree):
        raise ValueError(f"invalid src Git tree at {revision}")
    return {
        "source_tree": tree, "build_roots": {},
        "lakefile_sha256": blob_sha256(root, revision, "lakefile.toml", memo)[0],
        "manifest_sha256": blob_sha256(root, revision, "lake-manifest.json", memo)[0],
        "toolchain": blob_sha256(root, revision, "lean-toolchain", memo)[1].decode().strip(),
    }


BASELINE_FILE = Path(__file__).resolve().with_name("cache-baseline.json")


def pinned_identity(path=BASELINE_FILE):
    """The identity pinned in scripts/cache-baseline.json, checked against its fingerprint."""
    pinned = decode(path.read_bytes())
    if not isinstance(pinned, dict) or set(pinned) != {*FIELDS, "input_fingerprint"}:
        raise ValueError(f"unexpected fields in {path.name}")
    identity = {key: pinned[key] for key in FIELDS}
    if (not SHA40.fullmatch(str(identity["source_tree"])) or identity["build_roots"] != {}
            or not all(SHA256.fullmatch(str(identity[key])) for key in ("lakefile_sha256", "manifest_sha256"))
            or not isinstance(identity["toolchain"], str)
            or pinned["input_fingerprint"] != fingerprint(identity)):
        raise ValueError(f"{path.name} is malformed or its input_fingerprint does not match its fields")
    return identity


def baseline_candidates(root, identity, ref, depth):
    """Identities to try as a baseline, nearest first, each with a description.

    The first-parent ancestors of ref (as many as are fetched, at most depth), then the pinned
    identity. Only identities with the current toolchain and lake-manifest.json are useful."""
    memo, seen = {}, {fingerprint(identity)}
    listed = subprocess.run(["git", "-C", str(root), "rev-list", "--first-parent", f"--max-count={depth}",
                             ref, "--"], capture_output=True, text=True)
    if listed.returncode:
        print(f"Cannot list the history of {ref}: {listed.stderr.strip()}", flush=True)
    revisions = listed.stdout.split() if listed.returncode == 0 else []
    candidates = ((revision, lambda revision=revision: identity_at(root, revision, memo)) for revision in revisions)
    for label, compute in (*candidates, (BASELINE_FILE.name, lambda: pinned_identity(BASELINE_FILE))):
        try:
            candidate = compute()
        except subprocess.CalledProcessError:
            continue  # A commit without this project layout (src, lakefile.toml, ...).
        key = fingerprint(candidate)
        if (key not in seen and candidate["toolchain"] == identity["toolchain"]
                and candidate["manifest_sha256"] == identity["manifest_sha256"]):
            seen.add(key)
            yield label, candidate


def find_baseline(root, identity, ref, depth, fetcher=fetch):
    tried = 0
    for label, candidate in baseline_candidates(root, identity, ref, depth):
        tried += 1
        record = find_record(candidate, fetcher)
        if record is not None:
            print(f"Baseline: the record for {label} (input fingerprint {record['input_fingerprint']}),"
                  f" found after looking up {tried} distinct build inputs.", flush=True)
            return record, candidate
    print(f"No baseline: none of {tried} candidate build inputs with this toolchain and"
          " lake-manifest.json has a record.", flush=True)
    return None, None


def validated_blobs(record, identity, fetcher=fetch):
    contents = fetcher(record["map_key"], MAX_JSON)
    manifest = fetcher(record["module_manifest_key"], MAX_JSON)
    if contents is None or digest(contents) != record["map_sha256"]:
        raise ValueError("successful CI receipt's immutable map is missing or corrupt")
    if (manifest is None or digest(manifest) != record["module_manifest_sha256"]
            or len(manifest) != record["module_manifest_bytes"]):
        raise ValueError("successful CI receipt's immutable module manifest is missing or corrupt")
    lines = contents.splitlines()
    if not lines or decode(lines[0]) != SCHEMA or not 0 < len(lines) - 1 <= MAX_MODULES:
        raise ValueError("unsupported or empty CI Lake map")
    entries = {}
    for line in lines[1:]:
        row = decode(line)
        if (not isinstance(row, list) or len(row) != 2 or not all(isinstance(x, str) for x in row)
                or not HASH.fullmatch(row[0]) or not ARTIFACT.fullmatch(row[1]) or row[0] in entries):
            raise ValueError("invalid or duplicate CI map entry")
        entries[row[0]] = row[1]
    with gzip.GzipFile(fileobj=io.BytesIO(manifest)) as stream:
        plain = stream.read(MAX_JSON + 1)
    if len(plain) > MAX_JSON:
        raise ValueError("CI module manifest exceeds decompressed size limit")
    rows = plain.splitlines()
    header = decode(rows[0]) if rows else None
    if (not isinstance(header, dict) or type(header.get("schema")) is not int or header["schema"] != 1
            or any(header.get(key) != identity[key] for key in FIELDS)
            or header.get("input_fingerprint") != fingerprint(identity)
            or header.get("map_sha256") != record["map_sha256"]
            or type(header.get("modules")) is not int or header["modules"] != len(entries)):
        raise ValueError("CI module manifest is not bound to the current inputs and immutable map")
    shas = {}
    names = set()
    modules = []
    for line in rows[1:]:
        row = decode(line)
        if not isinstance(row, list) or len(row) != 4 or not all(isinstance(x, str) for x in row):
            raise ValueError("invalid CI module record")
        name, input_hash, artifact, sha256 = row
        if (not MODULE.fullmatch(name) or name in names or not SHA256.fullmatch(sha256)
                or entries.pop(input_hash, None) != artifact or shas.setdefault(artifact, sha256) != sha256):
            raise ValueError("CI module manifest does not uniquely cover its immutable map")
        names.add(name)
        modules.append((name, input_hash, artifact))
    if entries:
        raise ValueError("CI module manifest does not completely cover its immutable map")
    return contents, shas, modules


def published(artifact):
    """True/False if the public cache does/doesn't have the artifact; None if that is unclear."""
    request = urllib.request.Request(f"{PUBLIC_BASE}/artifacts/{SCOPE}/{artifact[:-5]}.art", method="HEAD",
                                     headers={"User-Agent": USER_AGENT})
    try:
        with urllib.request.urlopen(request, timeout=30):
            return True
    except urllib.error.HTTPError as error:
        return False if error.code == 404 else None
    except (urllib.error.URLError, TimeoutError, ConnectionError, http.client.HTTPException, ValueError):
        return None


def registered(cache, entries):
    """Map entries already registered in this cache with the same artifact
    (outputs/<scope>/<hash>.json naming it). Others are (re)written by `lake cache add`."""
    wanted = dict(entries)
    have = set()
    for directory, _, files in os.walk(cache / "outputs"):
        for name in files:
            input_hash = name[:-5]
            if name.endswith(".json") and input_hash in wanted and input_hash not in have:
                try:
                    text = (Path(directory) / name).read_text()
                except (OSError, UnicodeDecodeError):
                    continue
                if wanted[input_hash][:-5] in text:
                    have.add(input_hash)
    return have


def write_map(path, items):
    path.write_text(json.dumps(SCHEMA) + "\n" + "".join(json.dumps(item) + "\n" for item in items))


def register(root, env, service, temporary, items, shards=SHARDS):
    """`lake cache add` in parallel shards. Lake writes one file per mapping, so shards cannot
    conflict; a small first shard runs alone so that one process creates the outputs directory."""
    command = ["lake", "-q", "cache", "add", "--scope", SCOPE]
    if service:
        command += ["--service", service]
    first, rest = items[:100], items[100:]
    shards = max(1, min(shards, len(rest) // 2000 or 1))
    write_map(temporary / "add-0.jsonl", first)
    subprocess.run([*command, str(temporary / "add-0.jsonl")], cwd=root, env=env, check=True)
    processes = []
    for index in range(shards):
        part = rest[index::shards]
        if part:
            path = temporary / f"add-{index + 1}.jsonl"
            write_map(path, part)
            processes.append(subprocess.Popen([*command, str(path)], cwd=root, env=env))
    codes = [process.wait() for process in processes]
    if any(codes):
        raise subprocess.CalledProcessError(max(codes), command)


def unpack_jobs(root, cache, modules, baseline=False):
    """leantar jobs for every module, refusing unsafe or symlinked source/output paths.

    For a baseline, modules without a source now (removed since) are skipped."""
    jobs, checked = [], set()
    for name, input_hash, artifact in modules:
        module = Path(*name.split("."))
        if not local_path(root, Path("src") / module.with_suffix(".lean"), checked).is_file():
            if baseline:
                continue
            raise ValueError(f"missing source for {name}")
        archive = cache / "artifacts" / artifact
        if archive.is_symlink() or not archive.is_file():
            raise ValueError(f"missing cached archive: {archive}")
        bases = []
        for directory, suffixes in (("lib/lean", (".trace", ".olean", ".ilean")), ("ir", (".c",))):
            relative = Path(".lake/build") / directory / module
            for suffix in suffixes:
                local_path(root, relative.with_suffix(suffix), checked)
            bases.append(str(root / relative.parent))
        jobs.append({"file": str(archive), "hash": input_hash, "base": bases})
    return jobs


def clear_output_hashes(root, modules):
    """Remove Lake's saved hashes of the outputs that leantar is about to replace.

    Lake reads ``X.hash`` instead of hashing ``X`` unless given ``--rehash``, and
    leantar replaces ``X`` only. This is the list in Lake's ``Module.clearOutputHashes``.
    Call it after ``unpack_jobs`` has checked the paths.
    """
    stems_by_directory = {}
    for name, *_ in modules:
        *parents, stem = name.split(".")
        stems_by_directory.setdefault(tuple(parents), set()).add(stem)
    for directory, suffixes in (("lib/lean", ("olean", "olean.server", "olean.private", "ilean", "ir.sig", "ir")),
                                ("ir", ("c", "bc", "ltar"))):
        base = root / ".lake/build" / directory
        hash_suffixes = {suffix + ".hash" for suffix in suffixes}
        for parents, stems in stems_by_directory.items():
            try:
                entries = os.scandir(base.joinpath(*parents))
            except FileNotFoundError:
                continue
            with entries:
                for entry in entries:
                    stem, _, suffix = entry.name.partition(".")
                    if suffix in hash_suffixes and stem in stems:
                        try:
                            os.unlink(entry.path)
                        except FileNotFoundError:
                            pass


def download_failure(code, report):
    """Why fetch-artifacts.py failed, from its --report, and whether rerunning can help."""
    if not isinstance(report, dict):
        return f"the downloader exited {code} without a report (see its output above)"
    errors = [group for group in report.get("curl_errors") or []
              if isinstance(group, list) and len(group) == 2 and type(group[0]) is int and isinstance(group[1], str)]
    curl, mismatches = report.get("curl_exit"), report.get("sha256_mismatches")
    parts = []
    if curl:
        shown = "; ".join(line for _, line in errors[:3])
        parts.append(f"curl exited {curl}" + (f": {shown}" if shown else ""))
    if mismatches:
        parts.append(f"{mismatches} of the downloads did not match the manifest's SHA-256")
    reason = ", and ".join(parts) or f"the downloader exited {code}"
    if any(line.endswith(": is unknown") for _, line in errors):
        advice = "this curl is too old: lake exe cache get needs curl 7.71 or newer"
    elif curl == 23:
        advice = "writing the files failed: check free disk space and that .lake/cache is writable"
    elif mismatches:
        advice = "please report it: the public copies may be bad"
    else:
        advice = "if this was a network problem, rerun lake exe cache get"
    return f"{reason}. {advice[0].upper()}{advice[1:]}"


def consume(root, cache, record, identity, workers=24, fetcher=fetch, baseline=None):
    """Restore record, built for identity, or for the baseline identity if one is given."""
    contents, shas, modules = validated_blobs(record, baseline or identity, fetcher)
    if current_identity(root) != identity:
        raise ValueError("project inputs changed during cache lookup")
    local_path(root, Path(".lake"), set()).mkdir(exist_ok=True)
    (cache / "artifacts").mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    for key in list(env):
        if (key.startswith(("AWS_", "CLOUDFLARE_", "CF_"))
                or key in ("LAKE_CACHE_KEY", "LAKE_CACHE_ARTIFACT_ENDPOINT", "LAKE_CACHE_REVISION_ENDPOINT",
                           "LAKE_CACHE_SERVICE", "GH_TOKEN", "GITHUB_TOKEN", "HF_TOKEN",
                           # A writable artifact cache would copy every unpacked file into it.
                           "LAKE_ARTIFACT_CACHE")):
            env.pop(key)
    env.update(LAKE_CONFIG=str(root / "lakefile.toml"), LAKE_CACHE_DIR=str(cache),
               LAKE_RESTORE_ARTIFACTS="true", ELAN_TOOLCHAIN=identity["toolchain"])
    env["RUST_MIN_STACK"] = str(max(int(env.get("RUST_MIN_STACK", "0")), 8388608))
    service = tomllib.loads((root / "lakefile.toml").read_text()).get("cache", {}).get("defaultService")
    entries = [decode(line) for line in contents.splitlines()[1:]]
    have = registered(cache, entries)
    fresh = [entry for entry in entries if entry[0] not in have]
    print(f"Fetching {PROJECT} build cache {record['candidate_head']} for "
          f"{'baseline' if baseline else 'current'} build inputs: "
          f"{len(entries)} modules, {len(fresh)} not yet registered...", flush=True)
    with tempfile.TemporaryDirectory(prefix="ci-cache-", dir=root / ".lake") as temporary:
        temporary = Path(temporary)
        (temporary / "outputs.jsonl").write_bytes(contents)
        (temporary / "sha256.json").write_text(json.dumps(shas))
        downloads = subprocess.Popen(
            [sys.executable, "-I", str(FETCH_ARTIFACTS), str(temporary / "outputs.jsonl"), str(cache),
             "--sha256", str(temporary / "sha256.json"), "--verify-existing",
             "--base-url", f"{PUBLIC_BASE}/artifacts/{SCOPE}/", "--user-agent", USER_AGENT,
             "--report", str(temporary / "downloads.json")])
        try:
            if fresh:
                register(root, env, service, temporary, fresh)
        finally:
            code = downloads.wait()
        try:
            report = json.loads((temporary / "downloads.json").read_text())
        except (OSError, ValueError):
            report = None
    if code:
        missing = sorted({artifact for _, artifact in entries if not (cache / "artifacts" / artifact).is_file()})
        absent = [artifact for artifact in missing[:20] if published(artifact) is False]
        shown = ", ".join(missing[:20]) + (f" and {len(missing) - 20} more" if len(missing) > 20 else "")
        if absent:
            raise ValueError(f"{len(missing)} artifacts of the selected cache record are not in the public cache"
                             f" (HTTP 404: {', '.join(absent)}); rerunning will not help, please report it."
                             f" Missing or unverified: {shown}")
        raise ValueError(f"{len(missing)} cached artifacts could not be downloaded and verified ({shown});"
                         f" {download_failure(code, report)}")
    if current_identity(root) != identity:
        raise ValueError("project inputs changed before restoration")
    jobs = unpack_jobs(root, cache, modules, baseline is not None)
    for directory in dict.fromkeys(base for job in jobs for base in job["base"]):
        Path(directory).mkdir(parents=True, exist_ok=True)
    clear_output_hashes(root, modules)
    lean = Path(subprocess.check_output(["elan", "which", "lean"], cwd=root, env=env, text=True).strip())
    print(f"Unpacking {len(jobs)} modules with stock leantar ({workers} workers)...", flush=True)
    subprocess.run([str(lean.with_name("leantar")), "--jobs", str(workers), "-f", "-x", "-j", "-"],
                   input=json.dumps(jobs), text=True, cwd=root, env=env, check=True)
    if baseline:
        print(f"Restored {len(jobs)} of {len(modules)} baseline modules; lake build compiles those whose"
              " inputs changed since the baseline, and the modules that import them.", flush=True)
        return
    print("Checking with lake build --no-build...", flush=True)
    result = subprocess.run(["lake", "-q", "--log-level=error", "build", "--no-build"], cwd=root, env=env)
    if result.returncode:
        raise ValueError(f"lake build --no-build exited {result.returncode} after restoring the cache"
                         " (exit 3: some modules would need compiling)")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=Path.cwd())
    parser.add_argument("--cache-dir", type=Path)
    parser.add_argument("--jobs", type=int, default=24)
    parser.add_argument("--baseline", metavar="REF",
                        help="on a miss, restore the nearest record on REF's first-parent history (exit 4)")
    parser.add_argument("--baseline-depth", type=int, default=200, help="commits of REF to try (default 200)")
    parser.add_argument("--print-identity", action="store_true",
                        help="print the current build inputs in the form of scripts/cache-baseline.json, and stop")
    args = parser.parse_args()
    if args.jobs < 1 or not 1 <= args.baseline_depth <= 1000:
        parser.error("jobs must be positive; baseline depth must be 1..1000")
    root = args.project.resolve()
    identity = current_identity(root)
    if args.print_identity:
        print(json.dumps({**identity, "input_fingerprint": fingerprint(identity)}, indent=2))
        return 0
    record, baseline = find_record(identity), None
    if record is None:
        print("No equivalent successful cache found for the current build inputs.", flush=True)
        if args.baseline is None:
            return 3
        record, baseline = find_baseline(root, identity, args.baseline, args.baseline_depth)
        if record is None:
            return 3
    cache = (args.cache_dir or Path(os.environ.get("LAKE_CACHE_DIR", str(root / ".lake/cache")))).resolve()
    consume(root, cache, record, identity, args.jobs, baseline=baseline)
    return 0 if baseline is None else 4


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, OSError, EOFError, subprocess.CalledProcessError) as error:
        sys.exit(f"CI cache restore stopped: {error}")
