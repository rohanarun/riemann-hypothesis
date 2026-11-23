#!/usr/bin/env python3
"""Prepare trusted public dependencies/baseline before entering the proof sandbox."""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import subprocess
from types import SimpleNamespace
import rpc


def prepare(trusted, candidate, control, state, runner):
    trusted, candidate, control, state = map(lambda p: Path(p).resolve(), (trusted, candidate, control, state))
    lease = rpc.read(control / 'lease.json')
    rpc.require(lease['operation'] == rpc.PROOF_OPERATION, 'proof lease required')
    rpc.require(runner == lease['worker']['runner_name'], 'wrong registered runner')
    rpc.verify_source(candidate, lease['snapshot'], rpc.PROOF_OPERATION)
    if rpc.proof_policy()['baseline'].get('fresh_project'):
        from prepare_fresh import prepare_fresh
        return prepare_fresh(candidate,control,state,lease)
    for name, key in [('lakefile.toml', 'lakefile_sha256'), ('lake-manifest.json', 'manifest_sha256')]:
        rpc.require(rpc.digest(trusted / name) == lease['snapshot'][key], 'trusted main configuration differs')
    spec = importlib.util.spec_from_file_location('donor_ci_prepare', trusted / 'scripts/ci-prepare.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    baseline = rpc.proof_policy()['baseline']
    rpc.require(module.TOOLCHAIN == lease['snapshot']['toolchain'] and module.REVISION == baseline['revision'] and
                module.MAP_SHA == baseline['map_sha256'] and module.MANIFEST_SHA == baseline['manifest_sha256'],
                'main does not pin this completed baseline')
    state.mkdir(parents=True, exist_ok=True)
    request = state / 'donor-discovery-request.json'
    rpc.atomic(request, {'pr_head': lease['snapshot']['git_commit'],
                         'expected': {'candidate_head': lease['snapshot']['git_commit']}})
    paths_file = state / 'donor-paths.json'
    explicit = baseline.get('unchanged_module_names')
    filtered_plan = None
    if explicit is not None:
        filtered_plan = state / 'donor-baseline-plan.json'
        rpc.atomic(filtered_plan, {'status':'ready', 'candidate_head':lease['snapshot']['git_commit'],
                                   'closure':explicit})
    module.prepare(SimpleNamespace(trusted=trusted, candidate=candidate, state=state,
                                   request=request, output=paths_file, quick_plan=filtered_plan))
    paths = rpc.read(paths_file)
    environment = module.clean_env()
    environment['ELAN_TOOLCHAIN'] = lease['snapshot']['toolchain']
    lean = subprocess.check_output(['elan', 'which', 'lean'], env=environment, text=True).strip()
    lease['worker'].update(dependency_root=paths['packages'], toolchain_root=str(Path(lean).parent.parent),
                           baseline_cache_root=paths['baseline_cache'])
    key=rpc.rawsha({'baseline':baseline,'worklist':rpc.proof_policy()['worklist_sha256']})
    lease['worker']['expanded_base_root']=str(state/'proof-bases'/key)
    rpc.atomic(control / 'lease.json', lease)
    for name in ['build', 'packages']:
        (candidate / '.lake' / name).mkdir(parents=True, exist_ok=True)
    return lease['worker']


def main():
    parser = argparse.ArgumentParser()
    for name in ('trusted', 'candidate', 'control', 'state', 'runner'):
        parser.add_argument('--' + name, required=True)
    print(json.dumps(prepare(**vars(parser.parse_args()))))

if __name__ == '__main__':
    main()
