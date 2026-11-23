#!/usr/bin/env python3
"""Bind one reviewed ready proof batch and its dependency ZIP to GHA leases."""
import argparse
import json
from pathlib import Path
import shutil
import rpc


def prepare(seed, registry, output, run_id, attempt, workflow_sha, producer, worklist, archive):
    rpc.require(registry, 'no approved proof runners')
    rpc.snapshot_identity(seed['snapshot'], rpc.PROOF_OPERATION)
    inputs = seed['input_manifest']
    fp = seed['snapshot']['fingerprint']
    names = {row['module'] for row in seed['missing']['modules']}
    rpc.require(not names & set(inputs['modules']), 'proof targets must have no stale input artifacts')
    rpc.require(inputs.get('schema') == 1 and inputs.get('snapshot') == fp, 'foreign input manifest')
    rpc.require(rpc.SHA.fullmatch(seed.get('input_archive_sha256', '')), 'unbound input archive')
    if archive is not None:
        rpc.require(rpc.digest(archive) == seed['input_archive_sha256'], 'input ZIP SHA mismatch')
        rpc.verify_zip(archive, inputs, fp)
    matrix = rpc.plan(seed['snapshot'], seed['missing'], registry, run_id, attempt, workflow_sha,
                      rpc.digest(producer), rpc.rawsha(inputs), output,
                      mode=rpc.PROOF_OPERATION, worklist=worklist)
    for row in matrix['include']:
        control = Path(output) / row['id']
        rpc.atomic(control / 'input-manifest.json', inputs)
        if archive is not None:
            shutil.copyfile(archive, control / 'input-parts.zip')
    return matrix


def main():
    parser = argparse.ArgumentParser()
    for name in ('seed', 'seed-sha256', 'registry', 'output', 'run-id', 'workflow-sha',
                 'producer', 'worklist'):
        parser.add_argument('--' + name, required=True)
    parser.add_argument('--archive', default=None)
    parser.add_argument('--attempt', required=True, type=int)
    args = parser.parse_args()
    rpc.require(rpc.digest(args.seed) == args.seed_sha256, 'operator seed SHA mismatch')
    from proof_approval import check
    check(rpc.read(args.seed)['snapshot'])
    print(json.dumps(prepare(rpc.read(args.seed), rpc.read(args.registry), args.output,
                            args.run_id, args.attempt, args.workflow_sha, args.producer,
                            args.worklist, args.archive)))


if __name__ == '__main__':
    main()
