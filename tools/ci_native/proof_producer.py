#!/usr/bin/env python3
"""Run one fixed stock Lake proof batch inside the existing donor sandbox."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import rpc
from producer import dependency_paths

# Filled from the reviewed infrastructure source; never supplied by candidate data.
SOURCE_SHA_437 = '3a4af1088bb6afe99d794b905d65e7fcf29f22872c66028a48920a11418f9b48'
SOURCE_SHA = 'c3b7feb7f65935838d7a13f8c8f1954779b9f44753050ada63cddd9826e774a6'

def main():
    parser = argparse.ArgumentParser()
    for name in ('workspace', 'request', 'result'):
        parser.add_argument('--' + name, required=True)
    args = parser.parse_args()
    root = Path(args.workspace).resolve()
    request = rpc.read(args.request)
    names = [rpc.module_name(name) for name in request['modules']]
    rpc.require(0 < len(names) <= rpc.proof_policy()['max_batch_modules'], 'invalid proof batch')
    fresh=rpc.proof_policy()['baseline'].get('fresh_project',False)
    expected=SOURCE_SHA_437 if fresh else SOURCE_SHA
    package = Path(__file__).with_name('backend437' if fresh else 'backend')
    binary = package / '.lake/build/bin/proof-producer'
    receipt = rpc.read(package / 'proof-binary-receipt.json')
    rpc.require(rpc.digest(package / 'ProofProducer.lean') == expected == receipt['source_sha256'], 'unreviewed proof infrastructure source')
    rpc.require(rpc.digest(binary) == receipt['elf_sha256'], 'proof infrastructure executable changed')
    dependencies = Path(os.environ['NATIVE_PACKAGE_ROOT']).resolve()
    toolchain = Path(os.environ['NATIVE_TOOLCHAIN_ROOT']).resolve()
    dependency_paths(dependencies, root / 'lake-manifest.json')
    jobs = int(os.environ.get('NATIVE_PRODUCER_JOBS', '1'))
    rpc.require(1 <= jobs <= min(128, int(os.environ['LEAN_NUM_THREADS'])), 'proof concurrency exceeds lease')
    environment = {
        'PATH': str(toolchain / 'bin') + ':/usr/bin:/bin:/run/current-system/sw/bin',
        'HOME': '/tmp/native-home', 'TMPDIR': '/tmp', 'LANG': 'C.UTF-8',
        'LEAN_SYSROOT': str(toolchain), 'LAKE_HOME': str(toolchain),
        'LEAN_NUM_THREADS': str(jobs), 'LAKE_NO_CACHE': 'true', 'LAKE_ARTIFACT_CACHE': 'false',
        'GIT_CONFIG_NOSYSTEM': '1', 'GIT_CONFIG_GLOBAL': '/dev/null',
        'RUST_MIN_STACK': '8388608',
    }
    process = subprocess.run([str(binary), str(Path(args.request).resolve()), str(Path(args.result).resolve())],
                             cwd=root, env=environment)
    rpc.require(process.returncode == 0, 'stock proof backend failed; lease is not reassigned')
    result = rpc.read(args.result)
    rpc.require(result.get('dependency_preflight') is True, 'proof dependency preflight absent')
    rpc.require([row['module'] for row in result['modules']] == names, 'proof result identity mismatch')
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
