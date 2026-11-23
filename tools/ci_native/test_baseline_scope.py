import gzip
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import proof_baseline


class ExplicitBaselineTests(unittest.TestCase):
    def test_deleted_baseline_modules_are_not_restored(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            cache = root / 'cache'
            control = root / 'control'
            (cache / 'artifacts').mkdir(parents=True)
            control.mkdir()
            data = b'{}\n'
            (cache / 'outputs.jsonl').write_bytes(data)
            payload = b'only the explicitly approved archive'
            archive = '0000000000000001.ltar'
            (cache / 'artifacts' / archive).write_bytes(payload)
            sha = hashlib.sha256(payload).hexdigest()
            rows = [['Approved', '0'*16, archive, sha],
                    ['Affected', '0'*16, '0000000000000002.ltar', sha],
                    ['Deleted', '0'*16, '0000000000000003.ltar', sha]]
            header = {'source_tree':'1'*40,'map_sha256':hashlib.sha256(data).hexdigest(),'modules':3}
            manifest = gzip.compress(('\n'.join(json.dumps(x) for x in [header,*rows])+'\n').encode())
            (cache / 'modules.jsonl.gz').write_bytes(manifest)
            (control / 'input-manifest.json').write_text('{"modules":[]}')
            expected = {**header,'manifest_sha256':hashlib.sha256(manifest).hexdigest(),
                        'unchanged_modules':1,'unchanged_module_names':['Approved']}
            with patch('proof_baseline.rpc.proof_policy',return_value={'baseline':expected}), \
                 patch('proof_baseline.rpc.readonly_mount',return_value=True), \
                 patch('proof_baseline.rpc.proof_worklist',return_value={'Affected'}), \
                 patch('proof_baseline.subprocess.run') as run:
                result = proof_baseline.restore(root / 'candidate',control,
                    {'baseline_cache_root':str(cache),'toolchain_root':str(root),'jobs':2})
            self.assertEqual(result['restored_modules'],1)
            jobs = json.loads(run.call_args.kwargs['input'])
            self.assertEqual([Path(x['file']).name for x in jobs],[archive])
            self.assertFalse((cache / 'artifacts' / '0000000000000003.ltar').exists())


if __name__ == '__main__':
    unittest.main()
