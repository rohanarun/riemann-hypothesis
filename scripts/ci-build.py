#!/usr/bin/env python3
"""Trusted CI controller: build one candidate offline and stage its cache delta.

Run this file from the trusted workflow checkout, never from the PR checkout.
Candidate code/configuration runs only inside Bubblewrap. Dependencies and the
stock toolchain must already be prepared by the trusted runner.
"""
import argparse
import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import re
import resource
import shutil
import signal
import stat
import subprocess
import sys
import tarfile
import tempfile
import tomllib


_SETTINGS_SPEC = importlib.util.spec_from_file_location("rh_cache_settings", Path(__file__).with_name("cache-settings.py"))
settings = importlib.util.module_from_spec(_SETTINGS_SPEC)
_SETTINGS_SPEC.loader.exec_module(settings)
TOOLCHAIN = settings.TOOLCHAIN
DEPENDENCIES = settings.DEPENDENCIES
BASE_MANIFEST = settings.MANIFEST_SHA
HASH = re.compile(r"[0-9a-f]{16}\Z")
SHA = re.compile(r"[0-9a-f]{64}\Z")
MODULE = re.compile(r"[\w']+(?:\.[\w']+)*\Z")
SCHEMA = "2026-03-17"
HASH_SOURCE = '''import Lake.Build.Trace
import Lean.Data.Json.FromToJson
open Lake Lean
def main (args : List String) : IO Unit := do
  let [jobs, output] := args | throw <| IO.userError "expected jobs and output"
  let input ← IO.FS.Handle.mk jobs .read
  let out ← IO.FS.Handle.mk output .write
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let .ok job := Json.parse line | throw <| IO.userError "invalid job"
    let .ok file := job.getObjValAs? String "file" | throw <| IO.userError "missing file"
    let actual := (← computeBinFileHash file).toString
    out.putStrLn (Json.mkObj [("file", toJson file), ("actual", toJson actual)]).compress
'''


def sha256(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def trusted_env():
    return {"PATH": os.environ.get("PATH", "/usr/bin:/bin"),
            "GIT_CONFIG_GLOBAL": "/dev/null", "GIT_CONFIG_NOSYSTEM": "1"}


def build_resources(memory_gib, tasks_max):
    """Host-only systemd connection details never enter the clearenv sandbox."""
    environment = trusted_env()
    if memory_gib is None:
        return [], environment
    if not shutil.which("systemd-run") or not shutil.which("systemctl"):
        raise ValueError("requested memory limit requires systemd-run and a user manager")
    for key in ("XDG_RUNTIME_DIR", "DBUS_SESSION_BUS_ADDRESS"):
        if key in os.environ:
            environment[key] = os.environ[key]
    probe = subprocess.run(["systemctl", "--user", "show-environment"], env=environment,
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    if probe.returncode:
        raise ValueError("requested memory limit requires an available systemd user manager")
    unit = f"rh-ci-{os.getpid()}-{os.urandom(4).hex()}.scope"
    return ["systemd-run", "--user", "--scope", "--quiet", "--unit=" + unit,
            "--property=MemoryMax=" + str(memory_gib * 1024**3),
            "--property=TasksMax=" + str(tasks_max), "--"], environment


def normalized_exit_code(code):
    return 128 - code if code < 0 else code


def choose_work_directory(output, override=None):
    # /tmp may be a small RAM-backed filesystem. Proof caches belong on the
    # persistent CI workspace beside staging unless the operator overrides it.
    directory = (override if override is not None else output.parent).expanduser()
    directory.mkdir(parents=True, exist_ok=True)
    if not directory.is_dir():
        raise ValueError("CI work directory must be a directory")
    return directory.resolve()


class DurableBuildWork:
    """Raw completed work survives every exit until a trusted upload acknowledgement."""
    def __init__(self, parent, output, identity, adopt=None):
        parent.mkdir(parents=True, exist_ok=True)
        if adopt is None:
            self.path = Path(tempfile.mkdtemp(prefix="run-", dir=parent))
        else:
            self.path = adopt.absolute()
            if (self.path.parent != parent or not self.path.name.startswith("run-") or self.path.is_symlink()
                    or not self.path.is_dir() or self.path.stat().st_uid != os.getuid()):
                raise ValueError("recovered work must be an owned run-* directory in the durable work parent")
            previous = self.path / "checkpoint.json"
            if previous.exists() or previous.is_symlink():
                previous = safe_file(self.path, "checkpoint.json")
                if previous.stat().st_size > 2 * 1024**2:
                    raise ValueError("existing checkpoint exceeds its metadata bound")
                contents = previous.read_bytes()
                recorded = json.loads(contents)
                if (recorded.get("schema") != 1 or not isinstance(recorded.get("identity"), dict) or
                        any(recorded["identity"].get(key) != value for key, value in identity.items())):
                    raise ValueError("existing checkpoint identity differs from the requested recovery")
                backup = self.path / f"checkpoint-before-recovery-{os.getpid()}-{os.urandom(4).hex()}.json"
                backup.write_bytes(contents)
        self.output, self.identity, self.state = output, identity, "preparing"
        self.exit_code = None

    def checkpoint(self, state, exit_code=None):
        self.state, self.exit_code = state, exit_code
        record = {"schema": 1, "state": state, "build_exit_code": exit_code,
                  "controller_pid": os.getpid(), "work": str(self.path), "staging": str(self.output),
                  "identity": self.identity}
        temporary = self.path / "checkpoint.json.writing"
        with temporary.open("w") as stream:
            stream.write(json.dumps(record, sort_keys=True, indent=2) + "\n")
            stream.flush()
            os.fsync(stream.fileno())
        temporary.replace(self.path / "checkpoint.json")

    def __enter__(self):
        self.checkpoint("preparing")
        (self.output / "work-checkpoint.json").write_text(json.dumps({"checkpoint": str(self.path / "checkpoint.json")}) + "\n")
        return self

    def __exit__(self, kind, value, traceback):
        if kind is not None:
            self.checkpoint("interrupted" if issubclass(kind, (KeyboardInterrupt, SystemExit)) else "failed", self.exit_code)
        print(f"Retained CI work: {self.path / 'checkpoint.json'}", flush=True)
        # Intentionally no destructor/rmtree, including after SIGKILL or an
        # upload failure. Acknowledged successful uploads may release it later.


def build_log_link(primary, visible):
    try:
        os.link(primary, visible)
    except OSError as error:
        import errno
        if error.errno != errno.EXDEV:
            raise
        # The durable state volume and disposable workspace may differ. Keep
        # the durable file authoritative; mirror it while the process runs.
        shutil.copyfile(primary, visible)


def sync_visible_log(log, visible):
    if visible is None or os.path.samefile(log.name, visible):
        return
    log.flush()
    with open(log.name, "rb") as source, visible.open("ab") as destination:
        source.seek(destination.tell())
        shutil.copyfileobj(source, destination, 1024 * 1024)


def release_uploaded_work(checkpoint, artifact_id, artifact_digest):
    checkpoint = checkpoint.absolute()
    record = json.loads(safe_file(checkpoint.parent, checkpoint.name).read_text())
    if (record.get("schema") != 1 or record.get("state") != "staged" or record.get("build_exit_code") != 0 or
            record.get("work") != str(checkpoint.parent) or not checkpoint.parent.name.startswith("run-") or
            artifact_id <= 0 or not SHA.fullmatch(artifact_digest)):
        raise ValueError("only a fully staged successful build with an acknowledged durable upload can be released")
    if checkpoint.parent.stat().st_uid != os.getuid():
        raise ValueError("retained work is not owned by this runner account")
    acknowledgement = {"schema": 1, "work": str(checkpoint.parent), "identity": record["identity"],
                       "uploaded_artifact_id": artifact_id, "uploaded_artifact_digest": artifact_digest}
    marker = checkpoint.parent.parent / (checkpoint.parent.name + ".uploaded.json")
    marker.write_text(json.dumps(acknowledgement, sort_keys=True, indent=2) + "\n")
    shutil.rmtree(checkpoint.parent)


def verify_quiesced_controller(pid, proc=Path("/proc")):
    if pid <= 1 or b"ci-build.py" not in (proc / str(pid) / "cmdline").read_bytes():
        raise ValueError("recovery requires the original trusted CI controller")
    pending, seen = [pid], set()
    while pending:
        current = pending.pop()
        if current in seen:
            continue
        seen.add(current)
        if len(seen) > 10000:
            raise ValueError("unexpectedly large controller process tree")
        try:
            status = (proc / str(current) / "status").read_text()
            state = next(line.split()[1] for line in status.splitlines() if line.startswith("State:"))
            if state not in ("T", "t", "Z"):
                raise ValueError(f"controller/candidate process {current} is not quiesced")
            for task in (proc / str(current) / "task").iterdir():
                thread = (task / "status").read_text()
                thread_state = next(line.split()[1] for line in thread.splitlines() if line.startswith("State:"))
                if thread_state not in ("T", "t", "Z"):
                    raise ValueError(f"controller/candidate thread {task.name} is not quiesced")
                pending.extend(map(int, (task / "children").read_text().split()))
        except FileNotFoundError:
            if current == pid:
                raise ValueError("original controller exited before recovery completed") from None
    return sorted(seen)


def stop_build_process(process, command, environment):
    unit = next((argument.removeprefix("--unit=") for argument in command if argument.startswith("--unit=")), None)
    def send(signum):
        if unit:
            try:
                subprocess.run(["systemctl", "--user", "kill", "--kill-whom=all", "--signal=" + signal.Signals(signum).name, unit],
                               env=environment, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=10)
            except (OSError, subprocess.TimeoutExpired):
                pass
        try:
            os.killpg(process.pid, signum)
        except ProcessLookupError:
            pass
    send(signal.SIGTERM)
    try:
        return process.wait(timeout=10)
    except subprocess.TimeoutExpired:
        send(signal.SIGKILL)
        return process.wait()


def supervised_build(command, environment, log, filesystems, reserve_gib, visible_log=None, timeout_seconds=None):
    import time
    started = time.monotonic()
    reserve = reserve_gib * 1024**3
    if any(shutil.disk_usage(path).free < reserve for path in filesystems):
        raise ValueError("insufficient free disk for the CI build reserve")
    process = subprocess.Popen(command, env=environment, stdout=log, stderr=subprocess.STDOUT,
                               start_new_session=True)
    while True:
        try:
            code = process.wait(timeout=2)
            sync_visible_log(log, visible_log)
            return normalized_exit_code(code)
        except KeyboardInterrupt:
            log.write(b"\nCI controller: interrupted; stopping candidate and retaining raw work.\n")
            log.flush()
            stop_build_process(process, command, environment)
            sync_visible_log(log, visible_log)
            return 130
        except subprocess.TimeoutExpired:
            sync_visible_log(log, visible_log)
            if timeout_seconds is not None and time.monotonic() - started >= timeout_seconds:
                log.write(b"\nCI controller: quick-check budget expired; retaining partial work.\n")
                log.flush()
                stop_build_process(process, command, environment)
                sync_visible_log(log, visible_log)
                return 124
            if all(shutil.disk_usage(path).free >= reserve for path in filesystems):
                continue
            log.write(b"\nCI controller: free disk fell below the reserve; terminating candidate.\n")
            log.flush()
            code = stop_build_process(process, command, environment)
            sync_visible_log(log, visible_log)
            return normalized_exit_code(code) or 143


def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args], env=trusted_env(), text=True).strip()


def safe_file(root, relative):
    # The caller's root may itself sit below a PR-writable symlink (for example
    # .lake/build/lib/lean). Never resolve that link in the host controller.
    for ancestor in (root, *root.parents):
        if ancestor.is_symlink():
            raise ValueError(f"symlink is not a CI input/output root: {ancestor}")
    path = root
    for component in PurePosixPath(relative).parts:
        if component in ("", ".", "..") or "/" in component or "\\" in component:
            raise ValueError("unsafe file path")
        path = path / component
        if path.is_symlink():
            raise ValueError(f"symlink is not a CI input/output: {path}")
    if not stat.S_ISREG(path.stat().st_mode):
        raise ValueError(f"not a regular file: {path}")
    return path


def snapshot(candidate, head, destination):
    # Expose only attested build inputs, not PR scripts, docs, Git config, or caches.
    command = ["git", "-C", str(candidate), "archive", head, "--", "src", "lakefile.toml",
               "lake-manifest.json", "lean-toolchain"]
    process = subprocess.Popen(command, stdout=subprocess.PIPE, env=trusted_env())
    try:
        with tarfile.open(fileobj=process.stdout, mode="r|") as archive:
            for item in archive:
                relative = PurePosixPath(item.name)
                if relative.is_absolute() or ".." in relative.parts or ".lake" in relative.parts:
                    raise ValueError("unsafe archived source path")
                target = destination.joinpath(*relative.parts)
                if item.isdir():
                    target.mkdir(parents=True, exist_ok=True)
                elif item.isfile():
                    target.parent.mkdir(parents=True, exist_ok=True)
                    with archive.extractfile(item) as source, target.open("wb") as output:
                        shutil.copyfileobj(source, output)
                    target.chmod(0o755 if item.mode & 0o111 else 0o644)
                else:
                    raise ValueError("source symlinks and special files are not supported")
    finally:
        process.stdout.close()
        code = process.wait()
    if code:
        raise ValueError("could not snapshot candidate commit")
    verify_snapshot(candidate, head, destination)


def verify_snapshot(candidate, head, destination):
    # Git archive applies .gitattributes. Verify actual Git blobs so export-ignore
    # cannot omit inputs and export-subst cannot change the attested source tree.
    inventory = subprocess.check_output(["git", "-C", str(candidate), "ls-tree", "-r", "-z", head,
                                        "--", "src", "lakefile.toml", "lake-manifest.json", "lean-toolchain"],
                                       env=trusted_env())
    expected = {}
    for entry in inventory.split(b"\0"):
        if not entry:
            continue
        metadata, raw_path = entry.split(b"\t", 1)
        mode, kind, blob = metadata.decode().split()
        if kind != "blob" or mode not in ("100644", "100755"):
            raise ValueError("source symlinks, submodules and special files are not supported")
        expected[raw_path.decode()] = (mode, blob)
    source_paths = (destination / "src").rglob("*")
    actual = {path.relative_to(destination).as_posix() for path in source_paths if not path.is_dir() or path.is_symlink()}
    actual.update(name for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain")
                  if (destination / name).exists() or (destination / name).is_symlink())
    if actual != set(expected):
        raise ValueError("archived input inventory differs from Git blobs (check export-ignore attributes)")
    for relative, (mode, blob) in expected.items():
        path = safe_file(destination, relative)
        digest = hashlib.sha1(f"blob {path.stat().st_size}\0".encode())
        with path.open("rb") as stream:
            while block := stream.read(1024 * 1024):
                digest.update(block)
        executable = bool(path.stat().st_mode & 0o111)
        if digest.hexdigest() != blob or executable != (mode == "100755"):
            raise ValueError("archived input differs from its Git blob (check export-subst attributes)")


def validate_inputs(project, expected_dependencies):
    config = tomllib.loads(safe_file(project, "lakefile.toml").read_text())
    if safe_file(project, "lean-toolchain").read_text().strip() != TOOLCHAIN:
        raise ValueError(f"candidate must use the trusted stock toolchain {TOOLCHAIN}")
    if sha256(safe_file(project, "lake-manifest.json")) != expected_dependencies:
        raise ValueError("dependency manifest changed; prepare and attest its dependency cache first")
    if config.get("srcDir", ".") != "src" or config.get("extern_lib"):
        raise ValueError("CI only attests the src build-input root")
    for key in ("buildDir", "leanLibDir", "irDir", "packagesDir", "manifestFile"):
        if key in config:
            raise ValueError(f"custom {key} is outside the attested layout")
    libraries = {lib["name"]: lib for lib in config.get("lean_lib", [])}
    targets = config.get("defaultTargets", [])
    if not targets or any(target not in libraries for target in targets):
        raise ValueError("default targets must be attested source libraries")
    for lib in libraries.values():
        if lib.get("srcDir", ".") != ".":
            raise ValueError("additional library source roots are not attested")
        for name in [lib["name"], *lib.get("roots", [])]:
            if not MODULE.fullmatch(name):
                raise ValueError("invalid library module root")
    return sha256(project / "lakefile.toml")


def load_map(path):
    if path.stat().st_size > 64 * 1024**2:
        raise ValueError("Lake map exceeds the CI controller metadata bound")
    lines = path.read_bytes().splitlines()
    if not lines or json.loads(lines[0]) != SCHEMA:
        raise ValueError("unsupported stock Lake map schema")
    result = {}
    for line in lines[1:]:
        row = json.loads(line)
        if (not isinstance(row, list) or len(row) != 2 or
                not all(isinstance(value, str) for value in row) or
                not HASH.fullmatch(row[0]) or not row[1].endswith(".ltar") or
                not HASH.fullmatch(row[1][:-5]) or row[0] in result):
            raise ValueError("invalid stock Lake map entry")
        result[row[0]] = row[1]
    return result


def validate_packages(project, packages):
    manifest = json.loads((project / "lake-manifest.json").read_text())
    for package in manifest.get("packages", []):
        name = package.get("name", "")
        if not MODULE.fullmatch(name) or package.get("type") != "git" or package.get("subDir"):
            raise ValueError("CI dependencies must be separately attested Git packages")
        directory = packages / name
        if directory.is_symlink() or git(directory, "rev-parse", "HEAD") != package["rev"]:
            raise ValueError(f"dependency checkout differs from its locked revision: {name}")
        subprocess.run(["git", "-C", str(directory), "diff", "--no-ext-diff", "--no-textconv", "--quiet", "HEAD", "--"],
                       env=trusted_env(), check=True)


def package_overrides(project, control):
    """Use validated private dependency views without exposing Git data."""
    overrides = []
    for package in json.loads((project / "lake-manifest.json").read_text()).get("packages", []):
        entry = {key: value for key, value in package.items()
                 if key not in ("url", "rev", "inputRev", "subDir")}
        entry.update(type="path", dir="/work/project/.lake/packages/" + package["name"])
        overrides.append(entry)
    path = control / "packages.json"
    path.write_text(json.dumps({"version": "1.2.0", "packages": overrides}))
    return "/control/packages.json"


def private_package_builds(project, packages, destination):
    """Private dependency view: custom targets also write beside source files."""
    destination.mkdir()
    for package in json.loads((project / "lake-manifest.json").read_text()).get("packages", []):
        source = packages / package["name"]
        if source.is_symlink():
            raise ValueError("dependency directory must not be a symlink")
        target = destination / package["name"]
        target.mkdir()
        # Reflinks are private; ordinary copies are the safe fallback on ext4.
        # Hard links would let candidate code corrupt the trusted shared cache.
        # Never copy .git: it can contain credential-bearing config or hooks.
        for entry in source.iterdir():
            if entry.name == ".git":
                continue
            subprocess.run(["cp", "-a", "--reflink=auto", "--no-preserve=ownership", str(entry), str(target / entry.name)],
                           env=trusted_env(), check=True)
        if (target / ".lake").is_symlink():
            raise ValueError("dependency build cache must not be a symlink")
        (target / ".lake").mkdir(exist_ok=True)
    return destination


def verify_private_packages(project, packages, private):
    """Keep generated target sidecars, but require locked tracked dependency sources."""
    for package in json.loads((project / "lake-manifest.json").read_text()).get("packages", []):
        public, copied = packages / package["name"], private / package["name"]
        if copied.is_symlink() or not copied.is_dir():
            raise ValueError("missing private dependency view during recovery")
        inventory = subprocess.check_output(["git", "-C", str(public), "ls-tree", "-r", "-z", "HEAD"], env=trusted_env())
        for entry in inventory.split(b"\0"):
            if not entry:
                continue
            metadata, raw_name = entry.split(b"\t", 1)
            mode, kind, blob = metadata.decode().split()
            name = raw_name.decode()
            if kind != "blob" or mode not in ("100644", "100755", "120000"):
                raise ValueError("unsupported private dependency source type")
            if mode == "120000":
                path = copied / name
                if not path.is_symlink():
                    raise ValueError("private dependency symlink changed")
                data = os.readlink(path).encode()
                actual = hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest()
            else:
                path = safe_file(copied, name)
                if bool(path.stat().st_mode & 0o111) != (mode == "100755"):
                    raise ValueError("private dependency executable mode changed")
                if path.stat().st_size != safe_file(public, name).stat().st_size:
                    raise ValueError("private dependency source size changed")
                value = hashlib.sha1(f"blob {path.stat().st_size}\0".encode())
                with path.open("rb") as stream:
                    while chunk := stream.read(1024 * 1024):
                        value.update(chunk)
                actual = value.hexdigest()
            if actual != blob:
                raise ValueError("private dependency tracked source differs from its locked Git blob")
    return private


def baseline(args, project, cache, restore=True, modules=None):
    if args.baseline_manifest is None:
        return {}, [], None
    if not args.baseline_map or not args.baseline_cache:
        raise ValueError("baseline needs its full map and completed cache")
    if sha256(args.baseline_manifest) != args.baseline_manifest_sha256:
        raise ValueError("baseline manifest SHA256 mismatch")
    lines = gzip.decompress(args.baseline_manifest.read_bytes()).splitlines()
    header, rows = json.loads(lines[0]), [json.loads(line) for line in lines[1:]]
    map_sha = sha256(args.baseline_map)
    if (header.get("schema") != 1 or header.get("toolchain") != TOOLCHAIN or
            header.get("map_sha256") != map_sha or header.get("modules") != len(rows)):
        raise ValueError("baseline metadata/map mismatch")
    mapping = load_map(args.baseline_map)
    hashes, names = {}, set()
    jobs = []
    for row in rows:
        if not isinstance(row, list) or len(row) != 4 or not all(isinstance(x, str) for x in row):
            raise ValueError("invalid baseline module")
        name, dep_hash, filename, digest = row
        if (not MODULE.fullmatch(name) or name in names or mapping.get(dep_hash) != filename or
                not SHA.fullmatch(digest)):
            raise ValueError("invalid or duplicate baseline module")
        names.add(name)
        if filename in hashes and hashes[filename] != digest:
            raise ValueError("conflicting baseline archive digest")
        hashes[filename] = digest
        if not restore or (modules is not None and name not in modules):
            continue
        module = Path(*name.split("."))
        source = project / "src" / module.with_suffix(".lean")
        if not source.is_file():
            continue  # Deleted modules need no warm output.
        archive = cache / "artifacts" / filename
        if not archive.exists():
            original = safe_file(args.baseline_cache.resolve(), "artifacts/" + filename)
            if sha256(original) != digest:
                raise ValueError(f"incomplete baseline archive: {filename}")
            # Never hard-link a trusted baseline into a PR-writable filesystem.
            shutil.copyfile(original, archive)
        bases = [project / ".lake/build/lib/lean" / module.parent,
                 project / ".lake/build/ir" / module.parent]
        for directory in bases:
            directory.mkdir(parents=True, exist_ok=True)
        alias = project / ".lake/build/ir" / module.with_suffix(".ltar")
        os.link(archive, alias)  # Both links are private to this isolated job.
        jobs.append({"file": "/work/cache/artifacts/" + filename, "hash": dep_hash,
                     "base": ["/work/project/" + str(path.relative_to(project)) for path in bases]})
    if len(names) != len(mapping):
        raise ValueError("baseline module map is incomplete")
    return hashes, jobs, map_sha


def prepare_cache_maps(args, baseline_mapping, cache, control, toolchain, work, known_hashes):
    paths, expected, archive_paths = [], {}, []
    if args.cache_map and not args.baseline_cache:
        raise ValueError("--cache-map needs --baseline-cache containing its completed LTARs")
    for index, mapping_file in enumerate(args.cache_map):
        mapping = load_map(mapping_file)
        fresh = {key: value for key, value in mapping.items() if baseline_mapping.get(key) != value}
        for filename in set(fresh.values()):
            if filename in expected:
                continue
            original = safe_file(args.baseline_cache.resolve(), "artifacts/" + filename)
            destination = cache / "artifacts" / filename
            if not destination.exists():
                shutil.copyfile(original, destination)
            if filename in known_hashes:
                if sha256(destination) != known_hashes[filename]:
                    raise ValueError("baseline archive changed before cache reuse")
                continue
            expected[filename] = filename[:-5]
            archive_paths.append(destination)
        path = control / f"cache-map-{index:03}.jsonl"
        path.write_text(json.dumps(SCHEMA) + "\n" + "".join(json.dumps(row) + "\n" for row in sorted(fresh.items())))
        paths.append("/control/" + path.name)
    if archive_paths:
        actual = native_hashes(toolchain, archive_paths, work)
        if actual != expected:
            raise ValueError("newer cache map references an incomplete or corrupt LTAR")
    return paths


def sandbox(toolchain, project, packages, cache, result, control, jobs, dependency_builds=None):
    command = ["bwrap", "--die-with-parent", "--new-session", "--unshare-all", "--clearenv"]
    for path in ("/usr", "/bin", "/lib", "/lib64", "/nix/store", "/run/current-system/sw"):
        if Path(path).exists():
            command += ["--ro-bind", path, path]
    command += ["--proc", "/proc", "--dev", "/dev", "--tmpfs", "/tmp", "--dir", "/home/build",
                "--ro-bind", str(toolchain), "/opt/lean", "--ro-bind", str(project), "/work/project",
                "--bind", str(project / ".lake"), "/work/project/.lake",
                "--ro-bind", str(packages), "/work/project/.lake/packages",
                "--bind", str(cache), "/work/cache", "--bind", str(result), "/work/result",
                "--ro-bind", str(control), "/control"]
    if dependency_builds is not None:
        for directory in dependency_builds.iterdir():
            command += ["--bind", str(directory), "/work/project/.lake/packages/" + directory.name]
    for package in packages.iterdir():
        if dependency_builds is not None:
            continue  # Private package views exclude all Git metadata.
        metadata = package / ".git"
        if metadata.is_dir():
            command += ["--tmpfs", "/work/project/.lake/packages/" + package.name + "/.git"]
        elif metadata.exists():
            command += ["--ro-bind", "/dev/null", "/work/project/.lake/packages/" + package.name + "/.git"]
    environment = {"HOME": "/home/build", "PATH": "/opt/lean/bin:/run/current-system/sw/bin:/usr/bin:/bin",
                   "LEAN_SYSROOT": "/opt/lean", "LAKE_HOME": "/opt/lean", "LAKE_CACHE_DIR": "/work/cache",
                   # Unset LAKE_ARTIFACT_CACHE: stock defaults allow cache reads
                   # without copying every raw OLean/ILean/C into the cache.
                   "LAKE_RESTORE_ARTIFACTS": "true",
                   "LEAN_NUM_THREADS": str(jobs), "RUST_MIN_STACK": "8388608"}
    for name, value in environment.items():
        command += ["--setenv", name, value]
    return command + ["--chdir", "/work/project"]


def native_hashes(toolchain, paths, work, basenames=True):
    source, jobs, output = work / "Hash.lean", work / "hash-jobs.jsonl", work / "hashes.jsonl"
    source.write_text(HASH_SOURCE)
    jobs.write_text("".join(json.dumps({"file": str(path)}) + "\n" for path in paths))
    library = "libLake_shared.dylib" if sys.platform == "darwin" else "libLake_shared.so"
    subprocess.run([str(toolchain / "bin/lean"), "--load-dynlib=" + str(toolchain / "lib/lean" / library),
                    "--run", str(source), str(jobs), str(output)], cwd=work, env=trusted_env(), check=True)
    return {(Path(row["file"]).name if basenames else row["file"]): row["actual"]
            for row in map(json.loads, output.read_text().splitlines())}


def module_traces(project, incomplete=False):
    library = project / ".lake/build/lib/lean"
    for source in (project / "src").rglob("*.lean"):
        module = source.relative_to(project / "src").with_suffix("")
        relative = module.parent / (module.name + ".trace")
        path = library / relative
        if not path.exists():
            continue
        path = safe_file(library, str(relative))
        if path.stat().st_size > 32 * 1024**2:
            if incomplete:
                continue
            raise ValueError("module trace exceeds the CI controller metadata bound")
        name = str(module).replace("/", ".")
        if not MODULE.fullmatch(name):
            raise ValueError("unsafe compiled module name")
        try:
            dep_hash = json.loads(path.read_text()).get("depHash")
        except (json.JSONDecodeError, UnicodeError):
            if incomplete:
                continue
            raise
        if not isinstance(dep_hash, str) or not HASH.fullmatch(dep_hash):
            if incomplete:
                continue
            raise ValueError("invalid module input hash")
        yield name, module, dep_hash


def recover_completed_map(project, cache, toolchain, work, destination, known_hashes=None, existing=None, known_mappings=None):
    """Recover only already-saved LTARs after Lake dies before flushing -o."""
    known_by_digest = {digest: name for name, digest in (known_hashes or {}).items()}
    candidates, unknown = [], []
    for name, module, dep_hash in module_traces(project, incomplete=True):
        if dep_hash in (existing or {}):
            continue
        try:
            for directory, extension in (("lib/lean", ".olean"), ("lib/lean", ".ilean"), ("ir", ".c")):
                safe_file(project / ".lake/build" / directory, str(module.parent / (module.name + extension)))
        except FileNotFoundError:
            # buildLean removes old outputs before elaboration; its saved trace
            # may remain after a failure and must not revive stale warm outputs.
            continue
        try:
            archive = safe_file(project / ".lake/build/ir", str(module.parent / (module.name + ".ltar")))
        except FileNotFoundError:
            filename = (known_mappings or {}).get(dep_hash)
            if filename is None:
                continue
            try:
                archive = safe_file(cache, "artifacts/" + filename)
            except FileNotFoundError:
                continue
        digest = sha256(archive)
        known = known_by_digest.get(digest)
        candidates.append((dep_hash, archive, digest, known))
        if known is None:
            unknown.append(archive)
    hashes = native_hashes(toolchain, unknown, work, basenames=False) if unknown else {}
    mapping = dict(existing or {})
    for dep_hash, archive, digest, known in candidates:
        filename = known or (hashes[str(archive)] + ".ltar")
        try:
            completed = safe_file(cache, "artifacts/" + filename)
        except FileNotFoundError:
            continue  # leantar may have been killed before cache.saveArtifact.
        if not os.path.samefile(archive, completed) and digest != sha256(completed):
            continue
        if dep_hash in mapping and mapping[dep_hash] != filename:
            raise ValueError("conflicting completed module input hash")
        mapping[dep_hash] = filename
    destination.write_text(json.dumps(SCHEMA) + "\n" +
                           "".join(json.dumps(row) + "\n" for row in sorted(mapping.items())))
    print(f"Retained {len(mapping)} verified completed module mappings", flush=True)


def recover_raw_outputs(project, cache, work, control, command, prefix, environment, reserve_gib,
                        known_mappings, existing, workers=8):
    names = []
    summary = {"already_mapped": 0, "known_cache": 0, "missing_raw": 0}
    for name, module, dep_hash in module_traces(project, incomplete=True):
        if dep_hash in existing:
            summary["already_mapped"] += 1
            continue
        filename = known_mappings.get(dep_hash)
        if filename and (cache / "artifacts" / filename).is_file():
            summary["known_cache"] += 1
            continue
        try:
            for directory, extension in (("lib/lean", ".olean"), ("lib/lean", ".ilean")):
                safe_file(project / ".lake/build" / directory, str(module.parent / (module.name + extension)))
        except FileNotFoundError:
            summary["missing_raw"] += 1
            continue
        names.append(name)
    summary.update(candidates=len(names), accepted=0, stock_rejected=0, unreported=0)
    if not names:
        (work / "raw-recovery-summary.json").write_text(json.dumps(summary, sort_keys=True, indent=2) + "\n")
        return {}
    source = Path(__file__).parent / "cache-bootstrap/RecoverCompleted.lean"
    contents = source.read_text()
    if TOOLCHAIN == "leanprover/lean4:v4.36.0":
        # New module-system elaboration may postpone C/IR generation. Recover
        # only trace-attested parts; normal builds can run leanir afterwards.
        contents = contents.replace("mod.leanArts.fetch", "mod.elabArts.fetch")
        contents = contents.replace("-- OPTIONAL_C_436", "c? := if expected.c?.isSome then arts.c? else none")
    (control / "RecoverCompleted.lean").write_text(contents)
    (control / "raw-recovery-jobs.json").write_text(json.dumps(names))
    report = work / "result/raw-recovery.jsonl"
    if report.exists() or report.is_symlink():
        report.unlink()
    fresh_prefix = [f"--unit=rh-ci-recover-{os.getpid()}-{os.urandom(4).hex()}.scope" if item.startswith("--unit=") else item for item in prefix]
    with (work / "raw-recovery.log").open("wb") as log:
        code = supervised_build(fresh_prefix + command + ["/opt/lean/bin/lean",
            "--load-dynlib=/opt/lean/lib/lean/libLake_shared.so", "--run", "/control/RecoverCompleted.lean",
            "/work/project", "/control/raw-recovery-jobs.json", "/work/result/raw-recovery.jsonl", "/control/packages.json", str(min(workers, 32))],
            environment, log, (work,), reserve_gib)
    print(f"Stock no-build raw recovery processed {len(names)} candidate modules (exit {code}); raw work remains retained", flush=True)
    verified, seen, requested = {}, set(), set(names)
    if report.exists():
        report = safe_file(work / "result", "raw-recovery.jsonl")
        if report.stat().st_size > 64 * 1024**2:
            raise ValueError("raw recovery report exceeds its metadata bound")
        for line in report.read_text().splitlines():
            row = json.loads(line)
            name = row.get("name")
            if name not in requested or name in seen or type(row.get("ok")) is not bool:
                raise ValueError("unexpected raw recovery decision")
            seen.add(name)
            if not row["ok"]:
                summary["stock_rejected"] += 1
                continue
            input_hash, artifact = row.get("input", ""), row.get("artifact", "")
            if (not HASH.fullmatch(input_hash) or not artifact.endswith(".ltar") or
                    not HASH.fullmatch(artifact[:-5])):
                raise ValueError("invalid verified recovery artifact")
            module = Path(*name.split("."))
            trace = safe_file(project / ".lake/build/lib/lean", str(module.parent / (module.name + ".trace")))
            if json.loads(trace.read_text()).get("depHash") != input_hash:
                raise ValueError("recovery decision differs from the verified current trace")
            safe_file(cache, "artifacts/" + artifact)
            verified[input_hash] = artifact
    summary.update(accepted=len(verified), unreported=len(names) - len(seen), helper_exit_code=code)
    (work / "raw-recovery-summary.json").write_text(json.dumps(summary, sort_keys=True, indent=2) + "\n")
    print("Raw recovery coverage: " + json.dumps(summary, sort_keys=True), flush=True)
    return verified


def collect_mapped_ltars(project, cache, mapping):
    """Stock -o confirms completed packs; readonly cache leaves new LTARs local."""
    missing = {filename for filename in mapping.values()
               if not (cache / "artifacts" / filename).exists()}
    if not missing:
        return
    found = set()
    for _, module, dep_hash in module_traces(project):
        filename = mapping.get(dep_hash)
        if filename not in missing:
            continue
        archive = safe_file(project / ".lake/build/ir", str(module.parent / (module.name + ".ltar")))
        shutil.copyfile(archive, cache / "artifacts" / filename)
        found.add(filename)
    if found != missing:
        raise ValueError("completed output map references a missing module LTAR")


def main():
    if sys.argv[1:2] == ["--release-work"]:
        release = argparse.ArgumentParser(description="Release successful raw work only after its compressed cache upload succeeds")
        release.add_argument("--release-work", type=Path, required=True)
        release.add_argument("--uploaded-artifact-id", type=int, required=True)
        release.add_argument("--uploaded-artifact-digest", required=True)
        arguments = release.parse_args()
        release_uploaded_work(arguments.release_work, arguments.uploaded_artifact_id, arguments.uploaded_artifact_digest)
        return 0
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--packages", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--toolchain", type=Path)
    parser.add_argument("--work-dir", type=Path,
                        help="durable work parent (default: RH_CI_STATE_DIR/failed-work outside the GitHub workspace)")
    parser.add_argument("--jobs", type=int, default=24)
    parser.add_argument("--memory-gib", type=int,
                        help="fail-closed systemd user scope memory limit for the candidate build")
    parser.add_argument("--tasks-max", type=int, default=4096)
    parser.add_argument("--reserve-disk-gib", type=int, default=10)
    parser.add_argument("--dependency-manifest-sha256", default=DEPENDENCIES)
    parser.add_argument("--baseline-manifest", type=Path)
    parser.add_argument("--baseline-manifest-sha256", default=BASE_MANIFEST)
    parser.add_argument("--baseline-map", type=Path)
    parser.add_argument("--baseline-cache", type=Path)
    parser.add_argument("--cache-map", type=Path, action="append", default=[],
                        help="newer PR/ancestor map; LTARs must already be in --baseline-cache")
    parser.add_argument("--recover-work", type=Path, help="adopt a quiesced old run-* directory already moved outside the GitHub workspace")
    parser.add_argument("--recover-request", type=Path, help="original independently recorded hosted CI request")
    parser.add_argument("--recover-controller-pid", type=int)
    parser.add_argument("--recover-log", type=Path)
    parser.add_argument("--recover-exit-code", type=int, help="actual nonzero exit the original workflow will record (137 for SIGKILL)")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    recovery_values = (args.recover_request, args.recover_controller_pid, args.recover_log, args.recover_exit_code)
    if args.recover_work:
        if any(value is None for value in recovery_values) or not 1 <= args.recover_exit_code <= 255:
            parser.error("recovery requires original request, frozen controller PID, original log and a nonzero matching workflow exit code")
        verify_quiesced_controller(args.recover_controller_pid)
    elif any(value is not None for value in recovery_values):
        parser.error("recovery arguments require --recover-work")
    if ((args.memory_gib is not None and args.memory_gib < 1) or
            args.tasks_max < 1 or args.reserve_disk_gib < 0):
        parser.error("memory/tasks limits must be positive; disk reserve must be nonnegative")
    resource_prefix, build_environment = build_resources(args.memory_gib, args.tasks_max)
    if not args.toolchain:
        env = {**trusted_env(), "ELAN_TOOLCHAIN": TOOLCHAIN}
        args.toolchain = Path(subprocess.check_output(["elan", "which", "lean"], env=env, text=True).strip()).parent.parent
    toolchain = args.toolchain.resolve()
    version = subprocess.check_output([str(toolchain / "bin/lean"), "--version"], env=trusted_env(), text=True)
    if not version.startswith(f"Lean (version {settings.VERSION},") or settings.COMMIT not in version:
        raise ValueError(f"trusted toolchain must be the pinned stock Lean {settings.VERSION} release")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    if any(output.iterdir()):
        raise ValueError("staging output must be empty")
    head = git(args.candidate, "rev-parse", "HEAD")
    provenance = {"candidate_head": head, "candidate_tree": git(args.candidate, "rev-parse", "HEAD^{tree}"),
                  "source_tree": git(args.candidate, "rev-parse", "HEAD:src"), "build_roots": {},
                  "toolchain": TOOLCHAIN, "lakefile_sha256": sha256(safe_file(args.candidate, "lakefile.toml")),
                  "manifest_sha256": sha256(safe_file(args.candidate, "lake-manifest.json"))}
    # Stack/file limits affect this controller and its children only; hard limits remain unchanged.
    for kind, preferred in ((resource.RLIMIT_STACK, None), (resource.RLIMIT_NOFILE, 65536)):
        soft, hard = resource.getrlimit(kind)
        desired = hard if preferred is None else (preferred if hard == resource.RLIM_INFINITY else min(preferred, hard))
        resource.setrlimit(kind, (desired, hard))
    state_root = Path(os.environ.get("RH_CI_STATE_DIR", str(Path.home() / ".local/share/riemann-build-state")))
    work_parent = choose_work_directory(output, args.work_dir or (state_root / "failed-work"))
    if os.environ.get("GITHUB_WORKSPACE") and work_parent.is_relative_to(Path(os.environ["GITHUB_WORKSPACE"]).resolve()):
        raise ValueError("durable CI work must stay outside the disposable GitHub workspace")
    with DurableBuildWork(work_parent, output, provenance, adopt=args.recover_work) as workspace:
        work = workspace.path
        project, cache, result, control = work / "project", work / "cache", work / "result", work / "control"
        for directory in (project, cache / "artifacts", result, control):
            if directory.is_symlink():
                raise ValueError("recovery directories must not be symlinks")
            directory.mkdir(parents=True, exist_ok=bool(args.recover_work))
        if args.recover_work:
            verify_snapshot(args.candidate, head, project)
        else:
            snapshot(args.candidate, head, project)
        config_sha = validate_inputs(project, args.dependency_manifest_sha256)
        packages = args.packages.resolve()
        if packages.is_relative_to(args.candidate.resolve()):
            raise ValueError("dependencies must come from a trusted cache outside the candidate checkout")
        validate_packages(project, packages)
        overrides = package_overrides(project, control)
        dependency_builds = (verify_private_packages(project, packages, work / "dependency-builds") if args.recover_work else
                             private_package_builds(project, packages, work / "dependency-builds"))
        provenance.update(lakefile_sha256=config_sha, manifest_sha256=sha256(project / "lake-manifest.json"))
        if args.recover_work:
            request_path = safe_file(args.recover_request.parent.absolute(), args.recover_request.name)
            if request_path.stat().st_size > 2 * 1024**2:
                raise ValueError("original CI request exceeds its metadata bound")
            request = json.loads(request_path.read_text())
            if (request.get("repository") != "leanprover-community/riemann-hypothesis" or
                    type(request.get("run_id")) is not int or request["run_id"] <= 0 or
                    any(request.get("expected", {}).get(key) != value for key, value in provenance.items())):
                raise ValueError("recovered source/config identity differs from the original hosted CI request")
        # validate_inputs has checked layout/toolchain/dependencies. Stock
        # --rehash checks semantic options and clears stale module LTARs.
        base_hashes, warm_jobs, base_map_sha = baseline(args, project, cache, restore=not args.recover_work)
        base_mapping = load_map(args.baseline_map) if args.baseline_map else {}
        extra_maps = [] if args.recover_work else prepare_cache_maps(args, base_mapping, cache, control, toolchain, work, base_hashes)
        known_mappings = dict(base_mapping)
        for path in args.cache_map:
            known_mappings.update(load_map(path))
        (project / ".lake/packages").mkdir(parents=True, exist_ok=True)
        command = sandbox(toolchain, project, packages, cache, result, control, args.jobs, dependency_builds)
        if warm_jobs:
            subprocess.run(command + ["/opt/lean/bin/leantar", "--jobs", str(args.jobs), "-f", "-x", "-j", "-"],
                           input=json.dumps(warm_jobs), text=True, env=trusted_env(), check=True)
        for cache_map in extra_maps:
            subprocess.run(command + ["/opt/lean/bin/lake", "--packages", overrides, "cache", "add", cache_map],
                           env=trusted_env(), check=True)
        if args.recover_work:
            original_log = safe_file(args.recover_log.parent.absolute(), args.recover_log.name)
            if not (work / "build.log").exists():
                build_log_link(original_log, work / "build.log")
            elif sha256(work / "build.log") != sha256(original_log):
                raise ValueError("recovered durable log differs from the original frozen job")
            build_log_link(work / "build.log", output / "build.log")
            build_exit_code = args.recover_exit_code
        else:
            workspace.checkpoint("building")
            with (work / "build.log").open("wb") as log:
                build_log_link(work / "build.log", output / "build.log")
                build_exit_code = supervised_build(
                    resource_prefix + command + ["/opt/lean/bin/lake", "--packages", overrides, "--rehash", "build", "-o", "/work/result/outputs.jsonl"],
                    build_environment, log, (work, output), args.reserve_disk_gib, output / "build.log")
        mapping_file = result / "outputs.jsonl"
        if build_exit_code:
            workspace.checkpoint("recovering", build_exit_code)
            existing = {}
            if mapping_file.exists():
                try:
                    existing = load_map(safe_file(result, "outputs.jsonl"))
                except (ValueError, json.JSONDecodeError):
                    # Preserve a torn -o file, then recover only independently
                    # verified completed modules; never parse a partial record.
                    shutil.copyfile(mapping_file, work / "interrupted-outputs.jsonl")
                    mapping_file.unlink()
            verified = recover_raw_outputs(project, cache, work, control, command, resource_prefix, build_environment,
                                           args.reserve_disk_gib, known_mappings, existing, workers=args.jobs)
            # Only actual stock -o successes and explicit current no-build
            # recovery successes are fresh partial completions. A rejected
            # stale/corrupt module must not reenter via an old LTAR/cache pair.
            existing.update(verified)
            mapping_file.write_text(json.dumps(SCHEMA) + "\n" +
                                   "".join(json.dumps(row) + "\n" for row in sorted(existing.items())))
        mapping_file = safe_file(result, "outputs.jsonl")
        mapping = load_map(mapping_file)
        # Lean 4.33.1 omits the portable flag when reusing arts.ltar?, so -o
        # filters those entries from a platformIndependent map. Supplement only
        # current traces whose LTAR has an identical completed cache copy.
        if (TOOLCHAIN == "leanprover/lean4:v4.33.1" and not build_exit_code and
                tomllib.loads((project / "lakefile.toml").read_text()).get("platformIndependent") is True):
            recover_completed_map(project, cache, toolchain, work, mapping_file, base_hashes, mapping, known_mappings)
            mapping = load_map(mapping_file)
        collect_mapped_ltars(project, cache, mapping)
        artifacts = []
        paths = [safe_file(cache, "artifacts/" + name) for name in sorted(set(mapping.values()))]
        new_paths = [path for path in paths if path.name not in base_hashes]
        actual_hashes = native_hashes(toolchain, new_paths, work) if new_paths else {}
        (output / "artifacts").mkdir()
        digests = {}
        for path in paths:
            digest = sha256(path)
            digests[path.name] = digest
            if path.name in base_hashes:
                if digest != base_hashes[path.name]:
                    raise ValueError("baseline content hash collision")
                continue
            if actual_hashes.get(path.name) != path.stem:
                raise ValueError(f"artifact does not match its Lake hash: {path.name}")
            destination = output / "artifacts" / path.name
            shutil.copyfile(path, destination)
            artifacts.append({"file": path.name, "size": destination.stat().st_size, "sha256": digest})
        shutil.copyfile(mapping_file, output / "outputs.jsonl")
        inputs = {key: provenance[key] for key in ("source_tree", "lakefile_sha256", "manifest_sha256", "toolchain", "build_roots")}
        receipt = {"schema": 1, **provenance, "base_map_sha256": base_map_sha,
                   "cache_map_sha256": [sha256(path) for path in args.cache_map],
                   "input_fingerprint": hashlib.sha256(json.dumps(inputs, sort_keys=True, separators=(",", ":")).encode()).hexdigest(),
                   "build_exit_code": build_exit_code, "map_sha256": sha256(output / "outputs.jsonl"), "artifacts": artifacts}
        module_rows, covered = [], set()
        for name, module, dep_hash in module_traces(project, incomplete=bool(build_exit_code)):
            if dep_hash not in mapping:
                continue
            safe_file(project / "src", str(Path(*name.split(".")).with_suffix(".lean")))
            if dep_hash in covered:
                raise ValueError("multiple modules claim one input hash")
            covered.add(dep_hash)
            filename = mapping[dep_hash]
            module_rows.append([name, dep_hash, filename, digests[filename]])
        if covered != set(mapping):
            raise ValueError("compiled module manifest does not cover the full output map")
        header = {"schema": 1, **inputs, "map_sha256": receipt["map_sha256"],
                  "input_fingerprint": receipt["input_fingerprint"], "modules": len(module_rows)}
        manifest = output / "module-manifest.jsonl.gz"
        with manifest.open("wb") as raw, gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as zipped:
            zipped.write((json.dumps(header, sort_keys=True, separators=(",", ":")) + "\n").encode())
            for row in sorted(module_rows):
                zipped.write((json.dumps(row, separators=(",", ":")) + "\n").encode())
        receipt.update(module_manifest_sha256=sha256(manifest), module_manifest_bytes=manifest.stat().st_size)
        if args.recover_work:
            quiesced = verify_quiesced_controller(args.recover_controller_pid)
            verify_snapshot(args.candidate, head, project)
            audit = {"schema": 1, "operation": "quiesced interrupted-build recovery",
                     "identity": provenance, "original_run_id": request["run_id"],
                     "original_request_sha256": sha256(request_path),
                     "original_controller_pid": args.recover_controller_pid, "quiesced_processes": quiesced,
                     "build_exit_code": build_exit_code, "map_sha256": receipt["map_sha256"],
                     "mapped_modules": len(mapping), "delta_artifacts": len(artifacts)}
            (work / "handoff-audit.json").write_text(json.dumps(audit, sort_keys=True, indent=2) + "\n")
        (output / "receipt.json").write_text(json.dumps(receipt, sort_keys=True, indent=2) + "\n")
        workspace.checkpoint("staged" if build_exit_code == 0 else "failed", build_exit_code)
        print(json.dumps({"build_exit_code": build_exit_code, "mapped_modules": len(mapping), "delta_artifacts": len(artifacts)}))
        return build_exit_code


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        sys.exit(f"CI cache build stopped: {error}")
