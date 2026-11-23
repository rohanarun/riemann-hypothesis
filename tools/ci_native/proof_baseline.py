"""Restore only the policy-pinned unchanged modules, with stock leantar in the sandbox."""
import gzip
import json
from pathlib import Path
import subprocess
import rpc


def restore(root, control, worker, incoming=None):
    policy = rpc.proof_policy()
    expected = policy['baseline']
    if expected.get('fresh_project'):
        rpc.require(expected=={'fresh_project':True,'unchanged_modules':0,'unchanged_module_names':[]},'invalid fresh baseline policy')
        for part in ('lib/lean','ir'):(Path(root)/'.lake/build'/part).mkdir(parents=True,exist_ok=True)
        return {'baseline_modules':0,'restored_modules':0,'affected_modules_restored':0}
    cache = Path(worker['baseline_cache_root'])
    manifest = cache / 'modules.jsonl.gz'
    mapping = cache / 'outputs.jsonl'
    rpc.require(rpc.readonly_mount(cache), 'baseline cache must be mounted read-only')
    rpc.require(rpc.digest(manifest) == expected['manifest_sha256'] and
                rpc.digest(mapping) == expected['map_sha256'], 'unapproved native baseline')
    lines = gzip.decompress(manifest.read_bytes()).splitlines()
    header = json.loads(lines[0])
    rows = [json.loads(line) for line in lines[1:]]
    rpc.require(header.get('source_tree') == expected['source_tree'] and
                header.get('map_sha256') == expected['map_sha256'] and
                header.get('modules') == len(rows) == expected['modules'], 'baseline scope mismatch')
    affected = rpc.proof_worklist(Path(control) / 'proof-worklist.txt')
    allowed = expected.get('unchanged_module_names')
    if allowed is not None:
        rpc.require(len(allowed) == expected['unchanged_modules'] and
                    len(set(allowed)) == len(allowed) and not set(allowed).intersection(affected),
                    'invalid explicit unchanged baseline scope')
        allowed = set(allowed)
    inputs = rpc.read(Path(control) / 'input-manifest.json')
    # An incoming current-snapshot artifact always takes precedence over a base.
    incoming = set(inputs['modules']) if incoming is None else incoming
    jobs, seen, unchanged = [], set(), 0
    for name, dep_hash, archive, digest in rows:
        rpc.module_name(name)
        rpc.require(name not in seen, 'duplicate baseline module')
        seen.add(name)
        rpc.require(rpc.SHA.fullmatch(digest) and len(dep_hash) == 16 and
                    all(c in '0123456789abcdef' for c in dep_hash) and
                    len(archive) == 21 and archive.endswith('.ltar') and
                    all(c in '0123456789abcdef' for c in archive[:-5]), 'invalid native baseline entry')
        if name in affected or (allowed is not None and name not in allowed):
            continue
        unchanged += 1
        if name in incoming:
            continue
        source = cache / 'artifacts' / archive
        rpc.require(source.is_file() and not source.is_symlink() and
                    rpc.digest(source) == digest, 'native baseline LTAR SHA mismatch')
        relative = Path(*name.split('.'))
        bases = [Path(root) / '.lake/build' / part / relative.parent
                 for part in ['lib/lean', 'ir']]
        for directory in bases:
            directory.mkdir(parents=True, exist_ok=True)
        jobs.append({'file': str(source), 'hash': dep_hash, 'base': [str(p) for p in bases]})
    rpc.require(unchanged == expected['unchanged_modules'], 'unchanged baseline scope mismatch')
    if jobs:
        subprocess.run([str(Path(worker['toolchain_root']) / 'bin/leantar'), '--jobs',
                        str(min(worker.get('jobs', 1), 64)), '-f', '-x', '-j', '-'],
                       input=json.dumps(jobs), text=True, check=True)
    return {'baseline_modules': unchanged, 'restored_modules': len(jobs),
            'affected_modules_restored': 0}


def seal_fields():
    policy = rpc.proof_policy()
    return {'schema': 1, 'kind': 'expanded-unchanged-native-baseline',
            'baseline': policy['baseline'], 'worklist_sha256': policy['worklist_sha256']}


def prepared(path):
    path = Path(path)
    seal = path / 'complete.json'
    return (path.is_dir() and not path.is_symlink() and seal.is_file() and
            not seal.is_symlink() and rpc.read(seal) == seal_fields() and
            (path / '.lake/build/lib/lean').is_dir() and (path / '.lake/build/ir').is_dir())


def ensure(worker, control, tools, system_mounts):
    """Cold expansion runs once in a separate no-network sandbox, before proofs."""
    import fcntl
    import os
    import sys
    import tempfile
    destination = Path(worker['expanded_base_root']).resolve()
    destination.parent.mkdir(parents=True, exist_ok=True)
    with (destination.parent / (destination.name + '.lock')).open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if prepared(destination):
            return destination
        rpc.require(not destination.exists(), 'unsealed base directory requires operator recovery')
        partial = Path(tempfile.mkdtemp(prefix=destination.name + '.building-', dir=destination.parent))
        cache = Path(worker['baseline_cache_root']).resolve()
        toolchain = Path(worker['toolchain_root']).resolve()
        command = ['bwrap', '--tmpfs', '/', '--dev', '/dev', '--proc', '/proc',
                   '--unshare-net', '--unshare-pid', '--die-with-parent', '--new-session', '--clearenv',
                   '--dir', '/tmp', *system_mounts]
        for source in (cache, toolchain, Path(control).resolve(), Path(tools).resolve()):
            command += ['--ro-bind', str(source), str(source)]
        command += ['--bind', str(partial), str(partial), '--setenv', 'PATH',
                    str(toolchain / 'bin') + ':/usr/bin:/bin:/run/current-system/sw/bin',
                    sys.executable, str(Path(tools) / 'proof_baseline.py'), str(partial), str(control)]
        subprocess.run(command, check=True)
        rpc.require(prepared(partial), 'native baseline expansion did not seal successfully')
        partial.rename(destination)
    return destination


def verify_prepared(path):
    rpc.require(prepared(path) and rpc.readonly_mount(path), 'expanded baseline is not sealed/read-only')


if __name__ == '__main__':
    import sys
    root, control = map(Path, sys.argv[1:])
    lease = rpc.read(control / 'lease.json')
    # A sealed tree is independent of any one lease's dependency deltas.
    manifest = rpc.read(control / 'input-manifest.json')
    # restore(..., incoming=set()) requests the complete unchanged subset.
    restore(root, control, lease['worker'], incoming=set())
    rpc.atomic(root / 'complete.json', seal_fields())
