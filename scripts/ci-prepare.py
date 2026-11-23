#!/usr/bin/env python3
"""Trusted CI identity resolution and host-side downloads; never runs PR code."""
import argparse
import base64
import contextlib
import fcntl
import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import resource
import shutil
import subprocess
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request

REPO = "leanprover-community/riemann-hypothesis"
BASE = "https://rh-cache.taucetiproject.org"

_SETTINGS_SPEC = importlib.util.spec_from_file_location("rh_cache_settings", Path(__file__).with_name("cache-settings.py"))
settings = importlib.util.module_from_spec(_SETTINGS_SPEC)
_SETTINGS_SPEC.loader.exec_module(settings)
TOOLCHAIN = settings.TOOLCHAIN
MANIFEST_SHA = settings.MANIFEST_SHA
MAP_SHA = settings.MAP_SHA
REVISION = settings.REVISION
HEX = re.compile(r"[0-9a-f]{40}\Z")
LTAR = re.compile(r"[0-9a-f]{16}\.ltar\Z")

_SPEC = importlib.util.spec_from_file_location("rh_ci_publication", Path(__file__).with_name("publish-ci-cache.py"))
publication = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(publication)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def get(url, *, github=False, missing=False, maximum=100_000_000):
    headers = {"User-Agent": "RiemannHypothesisCI/1.0"}
    if github:
        token = os.environ.get("GH_TOKEN", os.environ.get("GITHUB_TOKEN"))
        if token:
            headers["Authorization"] = "Bearer " + token
        headers["Accept"] = "application/vnd.github+json"
    try:
        with urllib.request.urlopen(urllib.request.Request(url, headers=headers), timeout=90) as response:
            data = response.read(maximum + 1)
    except urllib.error.HTTPError as error:
        if missing and error.code == 404:
            return None
        raise RuntimeError(f"Download failed (HTTP {error.code})") from None
    if len(data) > maximum:
        raise ValueError("Download exceeds expected bound")
    return data


def api(path):
    return json.loads(get("https://api.github.com/repos/" + REPO + "/" + path, github=True))


def identity(revision, *, allow_historical=False):
    if not HEX.fullmatch(revision):
        revision = api("commits/" + urllib.parse.quote(revision, safe=""))["sha"]
    commit = api("git/commits/" + revision)
    tree = {row["path"]: row for row in api("git/trees/" + commit["tree"]["sha"])["tree"]}
    def blob(name):
        row = tree[name]
        if row["type"] != "blob" or row["mode"] not in ("100644", "100755"):
            raise ValueError("Unsafe build configuration input")
        return base64.b64decode(api("git/blobs/" + row["sha"])["content"])
    result = {"schema": 1, "candidate_head": revision, "candidate_tree": commit["tree"]["sha"],
              "source_tree": tree["src"]["sha"], "build_roots": {},
              "lakefile_sha256": digest(blob("lakefile.toml")),
              "manifest_sha256": digest(blob("lake-manifest.json")),
              "toolchain": blob("lean-toolchain").decode().strip()}
    selected = settings.for_toolchain(result["toolchain"])
    if (not allow_historical and selected.TOOLCHAIN != TOOLCHAIN) or tree["src"]["type"] != "tree":
        raise ValueError("CI requires the active pinned stock toolchain and src tree")
    fields = {key: result[key] for key in ("source_tree", "build_roots", "lakefile_sha256", "manifest_sha256", "toolchain")}
    result["input_fingerprint"] = digest(json.dumps(fields, sort_keys=True, separators=(",", ":")).encode())
    return result


def resolve(args):
    selected_head = args.head
    for attempt in range(5):
        pr = api("pulls/" + str(args.pr))
        if getattr(args, "require_main", False) and pr.get("base", {}).get("ref") != "main":
            raise ValueError("quick checks require a PR targeting main")
        selected_head = selected_head or pr["head"]["sha"]
        if pr["head"]["sha"] != selected_head:
            raise ValueError("PR head changed before this job started; a newer run will build it")
        if pr.get("mergeable") is False and not pr.get("merged"):
            raise ValueError("PR has no available merge result")
        revision = pr.get("merge_commit_sha")
        if revision and (pr.get("mergeable") is True or pr.get("merged") is True):
            if not isinstance(revision, str) or not HEX.fullmatch(revision):
                raise ValueError("Invalid candidate merge revision")
            commit = api("git/commits/" + revision)
            parents = {parent["sha"] for parent in commit["parents"]}
            # GitHub can report mergeable=true while merge_commit_sha still
            # names the previous head/base combination. Wait for both parents.
            if selected_head in parents and (pr.get("merged") or pr["base"]["sha"] in parents):
                break
        if attempt == 4:
            raise ValueError("GitHub has not finished computing the PR merge result; retry this job")
        time.sleep(2 * (attempt + 1))
    result = identity(revision)
    request = {"repository": REPO, "run_id": int(os.environ.get("GITHUB_RUN_ID", "0")),
               "pr_number": args.pr, "pr_head": pr["head"]["sha"], "base_head": pr["base"]["sha"], "base_ref": pr["base"].get("ref"), "expected": result}
    reused = get(f"{BASE}/ci/inputs/{result['input_fingerprint']}.json", missing=True, maximum=2_000_000)
    if reused is not None:
        reused = json.loads(reused)
        validate_record(reused)
        if (reused.get("build_exit_code") != 0 or
                reused.get("input_fingerprint") != result["input_fingerprint"]):
            raise ValueError("Invalid reusable build receipt")
        request["reuse_from"] = reused["candidate_head"]
    Path(args.output).write_text(json.dumps(request, indent=2) + "\n")
    print(json.dumps({"candidate": revision, "pr_head": request["pr_head"], "fingerprint": result["input_fingerprint"],
                      "reuse_from": request.get("reuse_from", "")}))


def clean_env():
    keep = ("PATH", "HOME", "ELAN_HOME", "SSL_CERT_FILE", "SSL_CERT_DIR", "NIX_SSL_CERT_FILE",
            "HTTP_PROXY", "HTTPS_PROXY", "NO_PROXY")
    return {key: os.environ[key] for key in keep if key in os.environ}


def mapping(data):
    return publication.parse_map(data)


def validate_record(record, *, allow_historical=False):
    publication.identity_fields(record, toolchain=record.get("toolchain") if allow_historical else TOOLCHAIN)
    if (record.get("repository") != REPO or
            record.get("input_fingerprint") != publication.fingerprint(record) or
            type(record.get("build_exit_code")) is not int or not 0 <= record["build_exit_code"] <= 255):
        raise ValueError("Invalid published CI cache metadata")
    for field, prefix, suffix in (("map_sha256", "ci/maps/", ".jsonl"),
                                  ("module_manifest_sha256", "ci/module-manifests/", ".jsonl.gz")):
        value = record.get(field, "")
        key = "map_key" if field == "map_sha256" else "module_manifest_key"
        if not isinstance(value, str) or not publication.SHA256.fullmatch(value) or record.get(key) != prefix + value + suffix:
            raise ValueError("Invalid published CI content address")


def manifest_hashes(data, entries, map_data, identity=None):
    header, rows = publication.parse_manifest(data, entries, identity)
    if header.get("map_sha256") != digest(map_data):
        raise ValueError("Module manifest does not match its output map")
    result = {}
    for row in rows.values():
        if row[2] in result and result[row[2]] != row[3]:
            raise ValueError("Conflicting archive digests in module manifest")
        result[row[2]] = row[3]
    return result


def select_module_entries(manifest, entries, names):
    _, rows = publication.parse_manifest(manifest, entries)
    return {row[1]: row[2] for row in rows.values() if row[0] in names}


def downloads(cache, entries, sha256s):
    artifacts = cache / "artifacts"
    if artifacts.is_symlink():
        raise ValueError("Cache artifacts must be a real directory")
    artifacts.mkdir(parents=True, exist_ok=True)
    missing = []
    for name in sorted(set(entries.values())):
        path = artifacts / name
        if (not LTAR.fullmatch(name) or not isinstance(sha256s.get(name), str) or
                not publication.SHA256.fullmatch(sha256s[name])):
            raise ValueError("Invalid archive filename or missing manifest digest")
        if path.is_file() and not path.is_symlink():
            with path.open("rb") as stream:
                valid = hashlib.file_digest(stream, "sha256").hexdigest() == sha256s[name]
            if valid:
                continue
        missing.append(name)
    if not missing:
        return
    print(f"Downloading {len(missing)} cache archives", flush=True)
    with tempfile.TemporaryDirectory(prefix="downloads-", dir=cache) as temp:
        temp = Path(temp)
        config = temp / "curl.conf"
        config.write_text("".join(f'url = "{BASE}/artifacts/{REPO}/{name[:-5]}.art"\noutput = {json.dumps(str(temp / name), ensure_ascii=False)}\n'
                                  for name in missing))
        subprocess.run(["curl", "--disable", "--fail", "--silent", "--show-error", "--location",
                        "--retry", "3", "--parallel", "--parallel-max", "500", "--config", str(config)],
                       env=clean_env(), check=True)
        for name in missing:
            path = temp / name
            if not path.is_file() or not path.stat().st_size:
                raise ValueError("Missing downloaded archive")
            if name in sha256s:
                with path.open("rb") as stream:
                    if hashlib.file_digest(stream, "sha256").hexdigest() != sha256s[name]:
                        raise ValueError("Downloaded archive SHA256 mismatch")
            else:
                raise ValueError("Archive missing manifest digest")
            path.chmod(0o444)
            os.replace(path, artifacts / name)


def previous_cache_revisions(candidate, request):
    head, merge = request["pr_head"], request["expected"]["candidate_head"]
    if not HEX.fullmatch(head) or not HEX.fullmatch(merge):
        raise ValueError("Invalid immutable cache discovery revision")
    def git(*arguments):
        return subprocess.check_output(["git", "-C", str(candidate), *arguments], text=True).splitlines()
    if git("rev-parse", "HEAD") != [merge]:
        raise ValueError("Cache discovery checkout differs from the resolved candidate")
    if head == merge:
        # Operator prewarm/probe requests can name a direct commit rather than
        # a proposed PR merge. Preserve their ordinary ancestry discovery.
        return git("log", "-50", "--format=%H", merge)
    parents = git("rev-list", "--parents", "-n", "1", merge)[0].split()
    if len(parents) != 3 or parents[0] != merge or head not in parents[1:]:
        raise ValueError("Cache discovery requires the resolved PR merge parents")
    base = next(parent for parent in parents[1:] if parent != head)
    # Search the PR's own history before date-ordered merge history. Exclude
    # base ancestors so an old shared baseline cannot shadow a newer fallback.
    branch = git("log", "--first-parent", "-50", "--format=%H", head, "--not", base)
    fallback = git("log", "-50", "--format=%H", merge)
    return list(dict.fromkeys([head, *branch, *fallback]))


def restore_previous_cache(candidate, request, cache):
    for revision in previous_cache_revisions(candidate, request):
        record_data = get(f"{BASE}/ci/revisions/{revision}.json", missing=True, maximum=2_000_000)
        if record_data is None:
            continue
        record = json.loads(record_data)
        validate_record(record, allow_historical=True)
        if record["toolchain"] != TOOLCHAIN:
            continue
        map_key, manifest_key = record["map_key"], record["module_manifest_key"]
        data = get(BASE + "/" + map_key)
        module_data = get(BASE + "/" + manifest_key)
        if digest(data) != record["map_sha256"] or digest(module_data) != record["module_manifest_sha256"]:
            raise ValueError("Published CI cache integrity mismatch")
        latest = mapping(data)
        extra_hashes = manifest_hashes(module_data, latest, data, record)
        downloads(cache, latest, extra_hashes)
        selected = cache / "latest.jsonl"
        selected.write_bytes(data)
        print(f"Reusing previous CI cache {revision}", flush=True)
        return selected
    return None


def preparation_state(directory):
    state = Path(directory).expanduser().resolve()
    # Keep the deployed 4.33 cache warm; only later releases need a new namespace.
    return state if TOOLCHAIN == "leanprover/lean4:v4.33.1" else state / settings.TOOLCHAIN_DIR


def prepare(args):
    trusted = Path(args.trusted).resolve()
    settings.require_baseline()
    state = preparation_state(args.state)
    state.mkdir(parents=True, exist_ok=True)
    with (state / "prepare.lock").open("w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        env = clean_env()
        env["ELAN_TOOLCHAIN"] = TOOLCHAIN
        soft, hard = resource.getrlimit(resource.RLIMIT_NOFILE)
        resource.setrlimit(resource.RLIMIT_NOFILE, (65536 if hard == resource.RLIM_INFINITY else min(65536, hard), hard))
        subprocess.run(["elan", "toolchain", "install", TOOLCHAIN], env=env, check=True)
        deps = state / "dependencies"
        deps.mkdir(exist_ok=True)
        for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
            shutil.copyfile(trusted / name, deps / name)
        (deps / "src").mkdir(exist_ok=True)
        (deps / ".lake").mkdir(exist_ok=True)
        env["MATHLIB_CACHE_GET_URL"] = "https://cache.mathlib.org/mathlib4"
        subprocess.run(["lake", "exe", "mathlib/cache", "get"], cwd=deps, env=env, check=True)
        cache = state / "baseline"
        cache.mkdir(exist_ok=True)
        map_data = get(f"{BASE}/revisions/{REPO}/tc/{settings.TOOLCHAIN_DIR}/{REVISION}.jsonl")
        manifest = get(f"{BASE}/bootstrap/{REVISION}/modules.jsonl.gz")
        if digest(map_data) != MAP_SHA or digest(manifest) != MANIFEST_SHA:
            raise ValueError("Pinned baseline integrity mismatch")
        (cache / "outputs.jsonl").write_bytes(map_data)
        (cache / "modules.jsonl.gz").write_bytes(manifest)
        entries = mapping(map_data)
        hashes = manifest_hashes(manifest, entries, map_data)
        quick_plan = getattr(args, "quick_plan", None)
        if quick_plan:
            plan = json.loads(Path(quick_plan).read_text())
            request = json.loads(Path(args.request).read_text())
            if plan.get("candidate_head") != request["expected"]["candidate_head"] or plan.get("status") != "ready":
                raise ValueError("quick plan does not bind the resolved candidate")
            names = set(plan["closure"])
            if not names or len(names) > 2000:
                raise ValueError("quick plan exceeds its dependency budget")
            entries = select_module_entries(manifest, entries, names)
        downloads(cache, entries, hashes)
        request = json.loads(Path(args.request).read_text())
        selected = None if quick_plan else restore_previous_cache(args.candidate, request, cache)
        paths = {"packages": str(deps / ".lake/packages"), "baseline_cache": str(cache),
                 "baseline_manifest": str(cache / "modules.jsonl.gz"), "baseline_map": str(cache / "outputs.jsonl"),
                 "latest_map": str(selected) if selected else ""}
        Path(args.output).write_text(json.dumps(paths, indent=2) + "\n")


def expected(args):
    request = json.loads(Path(args.request).read_text())
    result = request["expected"]
    result.update(pr_head=request["pr_head"], pr_number=request["pr_number"],
                  base_revision=REVISION, base_map_sha256=MAP_SHA, build_exit_code=args.exit_code)
    Path(args.output).write_text(json.dumps(result, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    resolve_command = commands.add_parser("resolve")
    resolve_command.add_argument("--pr", type=int, required=True)
    resolve_command.add_argument("--head")
    resolve_command.add_argument("--output", required=True)
    resolve_command.set_defaults(function=resolve)
    prep = commands.add_parser("prepare")
    for name in ("trusted", "candidate", "state", "request", "output"):
        prep.add_argument("--" + name, required=True)
    prep.add_argument("--quick-plan", type=Path)
    prep.set_defaults(function=prepare)
    exp = commands.add_parser("expected")
    exp.add_argument("--request", required=True)
    exp.add_argument("--exit-code", type=int, required=True)
    exp.add_argument("--output", required=True)
    exp.set_defaults(function=expected)
    args = parser.parse_args()
    args.function(args)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        raise SystemExit(f"CI preparation failed: {error}")
