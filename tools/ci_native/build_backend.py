#!/usr/bin/env python3
"""Compile only the pinned trusted infrastructure program, never project proofs."""
import argparse, os, subprocess
from pathlib import Path
import rpc
from producer import SOURCE_SHA
from proof_producer import SOURCE_SHA as PROOF_SOURCE_SHA, SOURCE_SHA_437

def main():
    p=argparse.ArgumentParser();p.add_argument('--toolchain',required=True)
    p.add_argument('--operation',choices=[rpc.OPERATION,rpc.PROOF_OPERATION],default=rpc.OPERATION)
    a=p.parse_args()
    fresh=a.operation==rpc.PROOF_OPERATION and rpc.proof_policy()['baseline'].get('fresh_project',False)
    root=Path(__file__).with_name('backend437' if fresh else 'backend').resolve();tc=Path(a.toolchain).resolve()
    proof=a.operation==rpc.PROOF_OPERATION
    source='ProofProducer.lean' if proof else 'RuntimeProducer.lean'
    expected=(SOURCE_SHA_437 if fresh else PROOF_SOURCE_SHA) if proof else SOURCE_SHA
    target='proof-producer' if proof else 'runtime-producer'
    rpc.require(rpc.digest(root/source)==expected,'unreviewed compiler adapter source')
    version=subprocess.check_output([str(tc/'bin/lean'),'--version'],text=True)
    rpc.require(('4.37.0-rc1' in version and '0b77e129' in version)if fresh else('4.36.0' in version and '611c' in version),'stock pinned toolchain required')
    env={'PATH':str(tc/'bin')+':/usr/bin:/bin:/run/current-system/sw/bin','HOME':'/tmp/native-build-home','LANG':'C.UTF-8'}
    subprocess.run([str(tc/'bin/lake'),'build',target],cwd=root,env=env,check=True)
    binary=root/'.lake/build/bin'/target
    rpc.atomic(root/('proof-binary-receipt.json' if proof else 'binary-receipt.json'),
               {'source_sha256':expected,'elf_sha256':rpc.digest(binary),'toolchain':version.strip()})
if __name__=='__main__':main()
