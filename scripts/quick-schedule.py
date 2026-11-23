#!/usr/bin/env python3
"""Operator-only small-runner queue. GH credentials remain on the operator host.

One logical `gh run watch --interval120` per host/run; no run-view polling.
An uncertain POST or monitor outcome is held for operator recovery, never retried.
"""
import argparse,concurrent.futures,fcntl,json,os,re,subprocess,threading,time
from pathlib import Path
REPO='leanprover-community/riemann-hypothesis'
PRIORITY={134,150}

def command(args,**kw):return subprocess.run(args,capture_output=True,text=True,check=True,**kw).stdout

def gh(path):return json.loads(command(['gh','api',path]))

def save(path,value):
 temporary=path.with_suffix('.partial');temporary.write_text(json.dumps(value,indent=2)+'\n');temporary.replace(path)

def key(pr):return str(pr['number'])+':'+pr['headRefOid']

def eligible(pr):
 if pr['number']in PRIORITY:return False,'reserved priority pool'
 if pr['mergeable']=='CONFLICTING':return False,'needs_rebase'
 if pr['changedFiles']>8:return False,'more than eight changed files'
 return True,''

def main():
 p=argparse.ArgumentParser();p.add_argument('--state',type=Path,required=True);p.add_argument('--once',action='store_true');a=p.parse_args();a.state.mkdir(parents=True,exist_ok=True)
 lock=(a.state/'lock').open('w');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
 hosts=json.loads(Path(__file__).with_name('quick-runners.json').read_text())
 while True:
  quota=gh('rate_limit')['resources']['core']
  if quota['remaining']<200:
   save(a.state/'quota-wait.json',{'remaining':quota['remaining'],'reset_epoch':quota['reset'],'resume_epoch':quota['reset']+30})
   if a.once:return
   time.sleep(min(600,max(60,quota['reset']+30-time.time())));continue
  prs=json.loads(command(['gh','pr','list','--repo',REPO,'--state','open','--limit','200','--json','number,title,headRefOid,changedFiles,additions,deletions,mergeable']))
  queue=[];deferred=[]
  for pr in sorted(prs,key=lambda row:(row['changedFiles'],row['additions']+row['deletions'],row['number'])):
   okay,reason=eligible(pr)
   if not okay:deferred.append({'pr':pr['number'],'head':pr['headRefOid'],'reason':reason});continue
   if not(a.state/(key(pr)+'.json')).exists():queue.append(pr)
  save(a.state/'queue.json',{'observed_epoch':time.time(),'waiting':[{'pr':pr['number'],'head':pr['headRefOid']}for pr in queue],'deferred':deferred})
  inventory=gh('orgs/leanprover-community/actions/runner-groups/5/runners?per_page=100')['runners'];available={row['id']:row for row in inventory if row['status']=='online'and not row['busy']}
  selected=[]
  for host in hosts:
   hostfile=a.state/('host-'+host['id']+'.json')
   prior=json.loads(hostfile.read_text())if hostfile.exists()else{}
   if prior.get('phase')=='watching':
    selected.append((host,{'number':prior['pr'],'headRefOid':prior['pr_head'],'resume':prior}));continue
   row=available.get(host['runner_id'])
   if not row or row['name']!=host['runner_name'] or host['label']not in {label['name']for label in row['labels']}:continue
   hostfile=a.state/('host-'+host['id']+'.json')
   if prior.get('phase')not in(None,'terminal'):continue
   if queue:selected.append((host,queue.pop(0)))
  def worker(pair):
   host,pr=pair;path=a.state/(key(pr)+'.json');hostfile=a.state/('host-'+host['id']+'.json');directory=a.state/key(pr);directory.mkdir(exist_ok=True);state=pr.get('resume',{'phase':'reserved','pr':pr['number'],'pr_head':pr['headRefOid'],'host':host['id']})
   def persist():save(path,state);save(hostfile,state)
   persist()
   try:
    if state['phase']!='watching':
     quota=gh('rate_limit')['resources']['core']
     if quota['remaining']<200:raise RuntimeError('quota reserve reached; held before POST')
     state['phase']='dispatch_started';persist()
     r=subprocess.run(['gh','workflow','run','build-pr.yml','--repo',REPO,'--ref','main','-f','mode=quick-check','-f','pr_number='+str(pr['number']),'-f','quick_head='+pr['headRefOid'],'-f','quick_runner='+host['id']],capture_output=True,text=True,timeout=120)
     (directory/'dispatch.log').write_text(r.stdout+'\n'+r.stderr)
     match=re.search(r'https://github\.com/'+re.escape(REPO)+r'/actions/runs/([0-9]+)',r.stdout+'\n'+r.stderr)
     if r.returncode or not match:raise RuntimeError('uncertain dispatch outcome; do not redispatch automatically')
     state.update(phase='watching',run_id=match[1],run_url=match[0]);persist();print(json.dumps(state),flush=True)
    for recovery in range(4):
     with(directory/'watch.log').open('a+')as log:
      offset=log.tell();watch=subprocess.run(['gh','run','watch',state['run_id'],'--repo',REPO,'--exit-status','--interval','120'],stdout=log,stderr=subprocess.STDOUT);log.flush();log.seek(offset);message=log.read(8192)
     if watch.returncode and 'HTTP 404: Not Found'in message and recovery<3:time.sleep(30);continue
     break
    run=gh('repos/'+REPO+'/actions/runs/'+state['run_id']);save(directory/'run.json',run)
    if run['event']!='workflow_dispatch'or run['head_branch']!='main'or run['path']!='.github/workflows/build-pr.yml'or str(run['id'])!=state['run_id']or run['status']!='completed':raise RuntimeError('foreign/nonterminal run; preserve same run for recovery')
    subprocess.run(['gh','run','download',state['run_id'],'--repo',REPO,'--name','quick-result-'+state['run_id']+'-'+str(run['run_attempt']),'--dir',str(directory/'result')],check=False)
    subprocess.run(['gh','run','download',state['run_id'],'--repo',REPO,'--name','quick-input-'+state['run_id']+'-'+str(run['run_attempt']),'--dir',str(directory/'input')],check=True)
    controls=json.loads((directory/'input/quick-request.json').read_text())
    if controls['pr_number']!=pr['number']or controls.get('quick_runner')!=host:raise RuntimeError('foreign diagnostic control artifact')
    result=directory/'result/result.json'
    outcome=json.loads(result.read_text())if result.exists()else({'status':'deferred','reason':controls.get('reason',''),'full_build':False}if controls.get('quick_status')=='deferred'else{'status':'infrastructure_or_outer_budget_failure','full_build':False})
    if outcome.get('full_build')is not False:raise RuntimeError('diagnostic claims a full build')
    if controls.get('quick_status')=='resolved'and controls['pr_head']!=pr['headRefOid']:raise RuntimeError('PR head changed despite pinned dispatch')
    if result.exists()and outcome.get('candidate_head')!=controls['expected']['candidate_head']:raise RuntimeError('foreign diagnostic result identity')
    state.update(phase='terminal',conclusion=run['conclusion'],result=outcome);persist();print(json.dumps(state),flush=True)
   except Exception as error:
    state.update(phase='held',error=str(error));persist();print(json.dumps(state),flush=True)
  with concurrent.futures.ThreadPoolExecutor(max_workers=3)as pool:list(pool.map(worker,selected))
  if a.once:return
  if not selected:time.sleep(600)
if __name__=='__main__':main()
