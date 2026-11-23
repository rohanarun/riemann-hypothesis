import gzip,hashlib,importlib.util,json
from pathlib import Path
import tempfile,unittest,sys
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('small_quick',ROOT/'quick-check.py');q=importlib.util.module_from_spec(spec);spec.loader.exec_module(q)
class QuickChecks(unittest.TestCase):
 def setUp(self):
  self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup);self.root=Path(self.temp.name);(self.root/'src').mkdir()
 def source(self,name,text):
  p=self.root/'src'/(name.replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text);return p
 def test_changed_root_closure(self):
  self.source('A','module\npublic import B\n@[expose] public section\ndef x := 1\n');self.source('B','module\nimport Mathlib\n');self.assertEqual(q.dependency_closure(self.root,['A']),['A','B'])
 def test_big_cone_deferred(self):
  for i in range(4):self.source('A'+str(i),'import A'+str(i+1)+'\n')
  with self.assertRaisesRegex(ValueError,'ancestor cone'):q.dependency_closure(self.root,['A0'],maximum=2)
 def test_comments_are_not_imports(self):
  p=self.source('A','/-\nimport Fake\n/-nested-/\n-/\nmodule\npublic import Actual -- comment\n\ndef x:=1\n');self.assertEqual(q.imports(p),['Actual'])
 def test_real_module_system_header(self):
  p=self.source('A','module\npublic meta import Foo\nimport all Bar\n\ndef x:=1\n');self.assertEqual(q.imports(p),['Foo','Bar'])
 def test_unrecognized_header_deferred(self):
  p=self.source('A','module\nimport «A B»\n')
  with self.assertRaisesRegex(ValueError,'unsupported'):q.imports(p)
 def test_unsafe_source_link_rejected(self):
  real=self.source('B','import Mathlib\n');(self.root/'src/A.lean').symlink_to(real)
  with self.assertRaises(ValueError):q.dependency_closure(self.root,['A'])
 def test_live_low_memory_host_deferred(self):
  host={'memory_gib':64};report={'ready':True,'systemd_user':True,'cgroup_v2':True,'physical_ram_gib':64}
  self.assertFalse(q.doctor_safe(report,host));report['physical_ram_gib']=125.5;self.assertTrue(q.doctor_safe(report,host))
 def test_runner_registry_excludes_big(self):
  with self.assertRaises(ValueError):q.runner('james-192')
  self.assertEqual(q.runner('gcp-small')['runner_id'],298713)
 def test_baseline_filter_does_not_require_other_archives(self):
  from types import SimpleNamespace
  ci=q.ci;cache=self.root/'private';(cache/'artifacts').mkdir(parents=True);trusted=self.root/'trusted';(trusted/'artifacts').mkdir(parents=True);rows=[];mapping={}
  for i,name in enumerate(['A','B']):
   self.source(name,'import Mathlib\n');key=f'{i+1:016x}';archive=f'{i+11:016x}.ltar';data=name.encode();mapping[key]=archive;rows.append([name,key,archive,hashlib.sha256(data).hexdigest()])
   if name=='A':(trusted/'artifacts'/archive).write_bytes(data)
  mapfile=self.root/'map.jsonl';mapfile.write_text(json.dumps(ci.SCHEMA)+'\n'+''.join(json.dumps(list(row))+'\n'for row in mapping.items()))
  manifest=self.root/'modules.gz';manifest.write_bytes(gzip.compress((json.dumps({'schema':1,'toolchain':ci.TOOLCHAIN,'map_sha256':ci.sha256(mapfile),'modules':2})+'\n'+''.join(json.dumps(row)+'\n'for row in rows)).encode()))
  args=SimpleNamespace(baseline_manifest=manifest,baseline_map=mapfile,baseline_cache=trusted,baseline_manifest_sha256=ci.sha256(manifest))
  hashes,jobs,_=ci.baseline(args,self.root,cache,modules={'A'});self.assertEqual(len(hashes),2);self.assertEqual(len(jobs),1);self.assertFalse((cache/'artifacts'/rows[1][2]).exists())
 def test_download_filter_uses_module_not_input_hash(self):
  mapping={'0000000000000001':'000000000000000b.ltar','0000000000000002':'000000000000000c.ltar'}
  data=gzip.compress((json.dumps({'schema':1,'toolchain':q.ci.TOOLCHAIN,'modules':2})+'\n'+json.dumps(['A','0000000000000001',mapping['0000000000000001'],'a'*64])+'\n'+json.dumps(['B','0000000000000002',mapping['0000000000000002'],'b'*64])+'\n').encode())
  self.assertEqual(q.prep.select_module_entries(data,mapping,{'A'}),{'0000000000000001':'000000000000000b.ltar'})
 def test_job_environment_uses_allowed_github_context(self):
  text=(ROOT.parent/'.github/workflows/build-pr.yml').read_text();self.assertNotIn('QUICK_OUTPUT: ${{ runner.',text);self.assertIn('QUICK_OUTPUT: ${{ github.workspace }}/.quick-results/',text)
 def test_full_mode_excluded_and_outputs_unique(self):
  text=(ROOT.parent/'.github/workflows/build-pr.yml').read_text();self.assertIn("inputs.mode != 'quick-check'",text);self.assertIn("format('rh-quick-{0}', inputs.quick_runner)",text);self.assertIn('rh-quick-${{ github.run_id }}-${{ github.run_attempt }}',text)
 def test_timeout_stops_owned_process(self):
  with(self.root/'build.log').open('wb')as out:code=q.ci.supervised_build([sys.executable,'-c','import time; time.sleep(10)'],q.ci.trusted_env(),out,[self.root],0,timeout_seconds=0.01)
  self.assertEqual(code,124)

class QueuePolicy(unittest.TestCase):
 def setUp(self):
  spec=importlib.util.spec_from_file_location('quick_queue_test',ROOT/'quick-schedule.py');self.queue=importlib.util.module_from_spec(spec);spec.loader.exec_module(self.queue)
 def test_big_priority_never_scheduled(self):
  self.assertFalse(self.queue.eligible({'number':134})[0]);self.assertFalse(self.queue.eligible({'number':150})[0])
 def test_large_or_conflicting_pr_deferred(self):
  self.assertEqual(self.queue.eligible({'number':151,'mergeable':'CONFLICTING','changedFiles':1}),(False,'needs_rebase'))
  self.assertFalse(self.queue.eligible({'number':151,'mergeable':'MERGEABLE','changedFiles':9})[0])
 def test_small_pr_eligible(self):
  self.assertTrue(self.queue.eligible({'number':152,'mergeable':'MERGEABLE','changedFiles':1})[0])
 def test_foreign_base_rejected_before_git(self):
  with self.assertRaisesRegex(ValueError,'main as base'):q.plan(Path('/unused'),{'expected':{},'base_ref':'feature'})
 def test_many_roots_rejected_before_elaboration(self):
  from unittest.mock import patch
  with patch.object(q.ci,'git',side_effect=['a'*40,'\n'.join('src/A'+str(i)+'.lean'for i in range(9))]),patch.object(q.ci,'validate_inputs'),patch.object(q.ci,'sha256',return_value='same'):
   with self.assertRaisesRegex(ValueError,'eight changed'):q.plan(Path('/unused'),{'expected':{'candidate_head':'a'*40},'base_ref':'main','base_head':'b'*40})

if __name__=='__main__':unittest.main()
