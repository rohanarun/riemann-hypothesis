"""The donor subset must agree with main's released baseline and seal identity."""
import json
from pathlib import Path
import tempfile
import unittest

import proof_baseline
import rpc


class PolicyTransitionTests(unittest.TestCase):
    def test_fresh_policy_does_not_activate_or_restore_main_baseline(self):
        policy=rpc.proof_policy()
        self.assertEqual(policy['snapshot']['toolchain'],'leanprover/lean4:v4.37.0-rc1')
        self.assertEqual(policy['baseline'],{'fresh_project':True,'unchanged_modules':0,'unchanged_module_names':[]})
        self.assertEqual(policy['worklist_modules'],policy['candidate_modules'])
        self.assertEqual(policy['worklist_modules'],149216)
        self.assertEqual(policy['approval_mode'],'ancestor-of-open-pr')
        self.assertEqual(policy['pr_number'],185)

    def test_previous_policy_seal_cannot_reuse_the_new_expansion(self):
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            for part in ['lib/lean','ir']:
                (base/'.lake/build'/part).mkdir(parents=True)
            old = {'schema':1,'kind':'expanded-unchanged-native-baseline',
                'baseline':{'revision':'2e43e1406f4398c615e1e527eeb3334600726cc4',
                    'source_tree':'0ba0b4d44fa26b97a376ec10889be6b553237103',
                    'map_sha256':'abcc0ec848fc00e4c6fd855eb4ed5c43d5b6773d577d74404cd43748378f6da0',
                    'manifest_sha256':'af49e586c8a073ca0de4669cc68e32604a014b00bf574c931b0a47c2d0fe81f9',
                    'modules':149395,'unchanged_modules':100302},
                'worklist_sha256':'70530fbd26e1c2d27fa36fdae5f0f3655a5c3b9f38faa340b09d7f441549bdd7'}
            rpc.atomic(base/'complete.json',old)
            self.assertFalse(proof_baseline.prepared(base))
            rpc.atomic(base/'complete.json',proof_baseline.seal_fields())
            self.assertTrue(proof_baseline.prepared(base))


if __name__ == '__main__':
    unittest.main()
