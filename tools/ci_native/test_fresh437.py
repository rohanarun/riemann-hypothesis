import copy,hashlib,json,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
import rpc,proof_approval,proof_baseline

class Fresh437Tests(unittest.TestCase):
 def setUp(self):
  self.snapshot={**rpc.proof_policy()['snapshot'],'git_commit':'a'*40,'source_tree':'b'*40}
  self.snapshot['fingerprint']=hashlib.sha256(json.dumps(self.snapshot,sort_keys=True).encode()).hexdigest()
  self.pr={'state':'open','base':{'ref':'main','repo':{'full_name':'leanprover-community/riemann-hypothesis'}},'head':{'sha':'c'*40}}
 def fetch(self,path):
  return self.pr if path.startswith('pulls/')else {'status':'ahead','merge_base_commit':{'sha':self.snapshot['git_commit']}}
 def test_exact_ancestor_approved_without_retagging(self):
  old=copy.deepcopy(self.snapshot);proof_approval.approved_ancestor(self.snapshot,self.fetch);self.assertEqual(old,self.snapshot)
 def test_force_pushed_unrelated_source_rejected(self):
  def fetch(path):return self.pr if path.startswith('pulls/')else {'status':'diverged','merge_base_commit':{'sha':'d'*40}}
  with self.assertRaises(ValueError):proof_approval.approved_ancestor(self.snapshot,fetch)
 def test_wrong_config_or_fingerprint_rejected(self):
  for key in ('lakefile_sha256','source_tree','fingerprint'):
   with self.assertRaises(ValueError):proof_approval.approved_ancestor({**self.snapshot,key:'0'*len(self.snapshot[key])},self.fetch)
 def test_closed_or_foreign_pr_rejected(self):
  self.pr['state']='closed'
  with self.assertRaises(ValueError):proof_approval.approved_ancestor(self.snapshot,self.fetch)
 def test_fresh_restore_reads_no436_archive_and_creates_empty_tree(self):
  with tempfile.TemporaryDirectory()as d:
   with patch('proof_baseline.subprocess.run')as run:
    result=proof_baseline.restore(Path(d),Path(d)/'control',{})
   self.assertEqual(result['restored_modules'],0);run.assert_not_called()
   self.assertTrue((Path(d)/'.lake/build/lib/lean').is_dir())
 def test_expanded_seal_does_not_accept_old436_policy(self):
  with tempfile.TemporaryDirectory()as d:
   p=Path(d)
   for part in ('lib/lean','ir'):(p/'.lake/build'/part).mkdir(parents=True)
   old=proof_baseline.seal_fields();old['baseline']={'fresh_project':False}
   rpc.atomic(p/'complete.json',old);self.assertFalse(proof_baseline.prepared(p))

if __name__=='__main__':unittest.main()
