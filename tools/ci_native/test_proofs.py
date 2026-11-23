import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
import zipfile
from unittest.mock import patch
import rpc

class ProofProtocolTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.policy = rpc.proof_policy()
        self.snapshot = {**self.policy['snapshot'],'git_commit':'a'*40,'source_tree':'b'*40}
        self.snapshot['fingerprint']=hashlib.sha256(json.dumps(self.snapshot,sort_keys=True).encode()).hexdigest()
        self.names = [f'Fixture.M{i:03d}' for i in range(300)]
        self.worklist = self.root / 'worklist.txt'
        self.worklist.write_text('\n'.join(self.names) + '\n')
        self.policy = {**self.policy, 'max_batch_modules':256,'worklist_modules': len(self.names),
                       'worklist_sha256': rpc.digest(self.worklist)}
        self.patch = patch.object(rpc, 'proof_policy', return_value=self.policy)
        self.patch.start()
        self.addCleanup(self.patch.stop)
        self.host = {'id': 'james', 'runner_name': 'registered-james',
                     'runs_on': ['self-hosted', 'Linux', 'X64', 'unique-james'],
                     'cpus': 192, 'memory_mib': 2 * 1024**2,
                     'timeout_seconds': 3600, 'jobs': 64}

    def plan(self, names=None, host=None):
        missing = {'snapshot': self.snapshot['fingerprint'],
                   'modules': [{'module': name} for name in (names or self.names[:2])]}
        output = self.root / 'control'
        rpc.plan(self.snapshot, missing, [host or self.host], '123', 1, 'b' * 40,
                 'c' * 64, 'd' * 64, output, mode=rpc.PROOF_OPERATION,
                 worklist=self.worklist)
        return output / 'james'

    def test_two_tib_runner_and_exact_worklist_are_accepted(self):
        control = self.plan()
        lease = rpc.read(control / 'lease.json')
        self.assertEqual(lease['operation'], rpc.PROOF_OPERATION)
        self.assertEqual(lease['proof_worklist_sha256'], rpc.digest(self.worklist))
        self.assertEqual(rpc.check_lease(lease, rpc.read(control / 'request-0.json'),
                                        '123', 1, 'registered-james'), self.names[:2])

    def test_source_pin_worklist_tampering_and_unknown_module_fail_closed(self):
        with self.assertRaises(ValueError):
            rpc.snapshot_identity({**self.snapshot, 'source_tree': '0' * 40}, rpc.PROOF_OPERATION)
        with self.assertRaises(ValueError):
            self.plan(['Unleased.Other'])
        self.worklist.write_text('Fixture.Modified\n')
        with self.assertRaises(ValueError):
            self.plan()

    def test_tiny_hosts_and_whole_affected_tree_are_rejected(self):
        for update in ({'cpus': 2}, {'memory_mib': 4096}):
            with self.assertRaises(ValueError):
                self.plan(host={**self.host, **update})
        with self.assertRaises(ValueError):
            self.plan(self.names[:257])

    def test_proof_task_budget_matches_unit_and_rejects_unbounded_or_excessive(self):
        values = {'memory.max': str(65536 * 1024**2), 'cpu.max': '1600000 100000',
                  'pids.max': '16384'}
        def check(mode, pids):
            with patch.object(rpc, 'current_cgroup', return_value=Path('/sys/fs/cgroup')), \
                 patch.object(Path, 'exists', return_value=True), \
                 patch.object(Path, 'read_text', lambda p: pids if p.name == 'pids.max' else values[p.name]):
                rpc.resource_limits(self.host, mode)
        check(rpc.PROOF_OPERATION, '16384')
        for pids in ('max', '16385', '0'):
            with self.assertRaises(ValueError):
                check(rpc.PROOF_OPERATION, pids)
        with self.assertRaises(ValueError):
            check(rpc.OPERATION, '16384')
        check(rpc.OPERATION, '512')

    def test_proof_outputs_are_narrow(self):
        for suffix in rpc.PROOF_PARTS:
            self.assertTrue(rpc.proof_path('A' + suffix))
            self.assertTrue(rpc.proof_path('A' + suffix + '.hash'))
        for suffix in ('.so', '.setup.json', '.py', '.sh', '.json'):
            self.assertFalse(rpc.proof_path('A' + suffix))

    def test_lease_cannot_change_operation_to_bypass_source_policy(self):
        control = self.plan()
        lease = rpc.read(control / 'lease.json')
        lease['operation'] = rpc.OPERATION
        with self.assertRaises(ValueError):
            rpc.check_lease(lease, rpc.read(control / 'request-0.json'), '123', 1, 'registered-james')

    def test_accept_requires_all_native_proof_parts_and_bound_actions_identity(self):
        control = self.plan(self.names[:1])
        lease = rpc.read(control / 'lease.json')
        returned = self.root / 'returned'
        returned.mkdir()
        name = self.names[0]
        rows = []
        with zipfile.ZipFile(returned / 'runtime-parts.zip', 'w') as archive:
            for suffix in rpc.PROOF_PARTS:
                part = 'ir' if suffix == '.c' else 'lib/lean'
                path = f'.lake/build/{part}/{name.replace(".", "/")}{suffix}'
                data = (name + suffix).encode()
                archive.writestr(path, data)
                rows.append({'module': name, 'path': path, 'bytes': len(data),
                             'sha256': hashlib.sha256(data).hexdigest()})
        manifest = {'schema': 1, 'snapshot': self.snapshot['fingerprint'],
                    'modules': [name], 'files': rows}
        rpc.atomic(returned / 'artifacts-0.json', manifest)
        response = {'snapshot': self.snapshot['fingerprint'], 'operation': rpc.PROOF_OPERATION,
                    'batch': 0, 'lease_id': lease['lease_id'],
                    'request_sha256': lease['request_sha256'], 'run_id': '123',
                    'run_attempt': 1, 'runner_name': 'registered-james',
                    'result': {'ok': True, 'modules': [{'module': name, 'ok': True}]},
                    'artifacts': {'manifest': 'artifacts-0.json',
                                  'sha256': rpc.digest(returned / 'artifacts-0.json')}}
        rpc.atomic(returned / 'response-0.json', response)
        provenance = {'run_id': '123', 'run_attempt': 1, 'runner_name': 'registered-james',
                      'workflow_sha': 'b' * 40,
                      'artifact_name': f'native-123-1-{lease["lease_id"]}'}
        self.assertEqual(rpc.accept(control, returned, provenance)['modules'], [name])
        bad = {**manifest, 'files': rows[:-1]}
        rpc.atomic(returned / 'artifacts-0.json', bad)
        response['artifacts']['sha256'] = rpc.digest(returned / 'artifacts-0.json')
        rpc.atomic(returned / 'response-0.json', response)
        with self.assertRaises(ValueError):
            rpc.accept(control, returned, provenance)

if __name__ == '__main__':
    unittest.main()
