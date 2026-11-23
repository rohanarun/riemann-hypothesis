#!/usr/bin/env python3
"""One-shot GitHub Actions transport for the existing source-FP/file-RPC protocol.
Only runtime-cache work is supported. This never calls Lake or a Lean source elaborator.
Artifact manifests retain the reviewed schema=1/module/path/bytes/sha256 format.
"""
from __future__ import annotations
import argparse, hashlib, json, os, re, stat, subprocess, sys, time, zipfile
from pathlib import Path, PurePosixPath

BASELINE_COMMIT = '9b1ee6011d0433c4c38a90508a14d39e33d608b6'
SOURCE = '0ba0b4d44fa26b97a376ec10889be6b553237103'
OPERATION = 'runtime-cache'
PROOF_OPERATION = 'native-proof'
PROOF_PARTS = ('.olean','.olean.server','.olean.private','.ilean','.ir.sig','.ir','.c','.trace')

def proof_policy(): return read(Path(__file__).with_name('proof-policy.json'))

def operation(value):
    require(value in (OPERATION,PROOF_OPERATION),'unknown worker operation')
    return value

def proof_worklist(path):
    policy=proof_policy();blob=Path(path).read_bytes()
    require(hashlib.sha256(blob).hexdigest()==policy['worklist_sha256'],'unapproved proof worklist')
    names=blob.decode().splitlines()
    require(len(names)==policy['worklist_modules'] and names==sorted(set(names)),'invalid proof worklist')
    return {module_name(x) for x in names}

def proof_path(path):
    return any(PurePosixPath(path).name.endswith(s) for s in PROOF_PARTS+tuple(x+'.hash' for x in PROOF_PARTS))
SHA = re.compile(r'^[0-9a-f]{64}$')
IDENT = re.compile(r'^[A-Za-z0-9_-]{1,80}$')
MAX_FILES = 2_000_000
MAX_BYTES = 500 * 1024**3

def require(ok, message):
    if not ok: raise ValueError(message)

def read(path): return json.loads(Path(path).read_text())
def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda: f.read(1024*1024), b''): h.update(b)
    return h.hexdigest()
def rawsha(value): return hashlib.sha256((json.dumps(value, separators=(',', ':'))+'\n').encode()).hexdigest()
def atomic(path, value):
    path=Path(path);path.parent.mkdir(parents=True, exist_ok=True)
    tmp=path.with_name(path.name+'.tmp');tmp.write_text(json.dumps(value,separators=(',', ':'))+'\n');tmp.replace(path)
def module_name(value):
    require(isinstance(value,str) and len(value)<=1000,'invalid module')
    require(all(c and all(x.isalnum() or x in "_'" for x in c) for c in value.split('.')),'unsafe module')
    return value

def relative(value):
    require(isinstance(value,str) and '\\' not in value and '\x00' not in value,'unsafe path')
    p=PurePosixPath(value)
    require(not p.is_absolute() and '..' not in p.parts and str(p)==value,'noncanonical path')
    require(len(p.parts)>2 and p.parts[:2]==('.lake','build'),'outside artifact area')
    return p

def regular(root, rel, exists=True):
    root=Path(root).resolve();p=root
    for part in relative(rel).parts:
        p=p/part
        require(not p.is_symlink(),'symlink in artifact path')
    require(p.resolve().is_relative_to(root),'artifact escaped root')
    if exists:require(p.is_file() and stat.S_ISREG(p.stat().st_mode),'not a regular artifact')
    return p

def snapshot_identity(snapshot, mode=OPERATION):
    operation(mode)
    expected=proof_policy()['snapshot'] if mode==PROOF_OPERATION else read(Path(__file__).with_name('identity.json'))
    require(bool(re.fullmatch(r'[0-9a-f]{40}',snapshot.get('git_commit',''))),'invalid candidate commit pin')
    for key,value in expected.items():require(snapshot.get(key)==value,'candidate identity mismatch: '+key)
    require(bool(SHA.fullmatch(snapshot.get('fingerprint',''))),'invalid source fingerprint')
    if mode==PROOF_OPERATION and proof_policy().get('approval_mode')=='ancestor-of-open-pr':
        require(set(snapshot)=={'git_commit','source_tree','toolchain','lakefile_sha256','manifest_sha256','fingerprint'},'unexpected snapshot fields')
        require(bool(re.fullmatch(r'[0-9a-f]{40}',snapshot.get('source_tree',''))),'invalid source tree')
        fields={k:v for k,v in snapshot.items()if k!='fingerprint'}
        require(hashlib.sha256(json.dumps(fields,sort_keys=True).encode()).hexdigest()==snapshot['fingerprint'],'incorrect snapshot fingerprint')
    return snapshot

def verify_source(root, snapshot, mode=OPERATION):
    snapshot_identity(snapshot,mode);root=Path(root)
    def git(*a):return subprocess.check_output(['git','-C',str(root),*a],text=True).strip()
    require(git('rev-parse','HEAD')==snapshot['git_commit'],'source HEAD changed')
    require(git('rev-parse','HEAD:src')==snapshot['source_tree'],'source tree changed')
    for name,key in [('lakefile.toml','lakefile_sha256'),('lake-manifest.json','manifest_sha256')]:
        require(digest(root/name)==snapshot[key],'raw configuration changed: '+name)
    require((root/'lean-toolchain').read_text().strip()==snapshot['toolchain'],'toolchain changed')
    require(not git('status','--porcelain','--untracked-files=all','--','src','lakefile.toml','lake-manifest.json','lean-toolchain'),'dirty candidate source')

def verify_manifest(root, manifest, fingerprint, allowed=None):
    require(manifest.get('schema')==1 and manifest.get('snapshot')==fingerprint,'artifact/source mismatch')
    names=[module_name(x)for x in manifest['modules']]
    require(len(names)==len(set(names)),'duplicate manifest module')
    if allowed is not None:require(set(names)<=set(allowed),'unexpected output module')
    require(len(manifest['files'])<=MAX_FILES,'too many artifacts')
    seen=set();total=0
    for row in manifest['files']:
        require(row['module']in names,'artifact module absent from manifest')
        rel=row['path'];require(rel not in seen,'duplicate artifact path');seen.add(rel)
        relative(rel)
        module_stem=PurePosixPath(*row['module'].split('.'))
        expected=PurePosixPath('.lake/build')
        require(any(PurePosixPath(rel).parent==expected/part/module_stem.parent and
                    PurePosixPath(rel).name.startswith(module_stem.name+'.')
                    for part in ['lib/lean','ir']),'artifact/module path mismatch')
        require(type(row['bytes'])is int and row['bytes']>=0 and bool(SHA.fullmatch(row['sha256'])),'invalid artifact metadata')
        total+=row['bytes'];require(total<=MAX_BYTES,'artifact byte budget exceeded')
        p=regular(root,rel);require(p.stat().st_size==row['bytes'] and digest(p)==row['sha256'],'artifact integrity failure: '+rel)
    return total

def runtime_path(path):
    name=PurePosixPath(path).name
    return bool(re.fullmatch(r".+\.(?:c|c\.o(?:\.export)?|o(?:\.export)?|bc|map|json|trace|(?:olean(?:\.private|\.server)?|ir|ilean|c|c\.o(?:\.export)?|o(?:\.export)?)\.hash)",name))

def verify_zip(archive, manifest, fingerprint, allowed=None, runtime_only=False):
    require(manifest.get('schema')==1 and manifest.get('snapshot')==fingerprint,'archive source mismatch')
    names=[module_name(x)for x in manifest['modules']]
    require(len(names)==len(set(names)),'duplicate archive module')
    if allowed is not None:require(set(names)<=set(allowed),'unexpected archive module')
    expected={r['path']:r for r in manifest['files']}
    require(len(expected)==len(manifest['files'])and len(expected)<=MAX_FILES,'duplicate/oversize manifest')
    for rel,row in expected.items():
        relative(rel);require(row['module']in names,'archive module mismatch')
        stem=PurePosixPath(*row['module'].split('.'));p=PurePosixPath(rel)
        require(any(p.parent==PurePosixPath('.lake/build')/part/stem.parent and p.name.startswith(stem.name+'.')for part in ['lib/lean','ir']),'archive module/path mismatch')
        require(type(row['bytes'])is int and row['bytes']>=0 and SHA.fullmatch(row['sha256']),'invalid archive metadata')
        if runtime_only:require(runtime_path(rel),'non-runtime output forbidden')
    total=0;seen=set()
    with zipfile.ZipFile(archive)as z:
        require(len(z.infolist())<=MAX_FILES,'oversize archive')
        for info in z.infolist():
            mode=info.external_attr>>16
            require(not stat.S_ISLNK(mode),'archive symlink')
            if info.is_dir():
                d=PurePosixPath(info.filename.rstrip('/'))
                require(not d.is_absolute()and '..'not in d.parts and '\\'not in info.filename,'unsafe archive directory')
                continue
            relative(info.filename)
            require(not stat.S_IFMT(mode)or stat.S_ISREG(mode),'nonregular archive member')
            require(info.filename in expected and info.filename not in seen,'unexpected/duplicate archive member')
            seen.add(info.filename);row=expected[info.filename]
            require(info.file_size==row['bytes'],'archive size mismatch')
            total+=info.file_size;require(total<=MAX_BYTES,'oversize archive')
            h=hashlib.sha256()
            with z.open(info)as f:
                for data in iter(lambda:f.read(1024*1024),b''):h.update(data)
            require(h.hexdigest()==row['sha256'],'archive content SHA mismatch')
    require(seen==set(expected),'incomplete archive')
    return total

def stage_zip(archive, root, manifest, fingerprint):
    verify_zip(archive,manifest,fingerprint)
    root=Path(root);expected={r['path']:r for r in manifest['files']}
    with zipfile.ZipFile(archive)as z:
        for info in z.infolist():
            if info.is_dir():continue
            out=regular(root,info.filename,exists=False)
            if out.exists():require(digest(out)==expected[info.filename]['sha256'],'refuse overwrite of different cached artifact')
            else:
                out.parent.mkdir(parents=True,exist_ok=True)
                with z.open(info)as src,out.open('wb')as dst:
                    while data:=src.read(1024*1024):dst.write(data)
    return verify_manifest(root,manifest,fingerprint)

def host(value):
    require(IDENT.fullmatch(value.get('id','')),'invalid worker ID')
    require(isinstance(value.get('runner_name'),str)and value['runner_name'],'runner name required')
    labels=value.get('runs_on');require(isinstance(labels,list)and labels and all(isinstance(x,str)and x for x in labels),'runner labels required')
    require('self-hosted'in labels and 'Linux'in labels and 'X64'in labels,'registered Linux/X64 runner required')
    for key,lo,hi in [('cpus',1,256),('memory_mib',512,2097152),('timeout_seconds',1,21600)]:
        require(type(value.get(key))is int and lo<=value[key]<=hi,'invalid resource limit: '+key)
    return value

def plan(snapshot, missing, hosts, run_id, attempt, workflow_sha, producer_sha, input_manifest_sha, output, now=None, mode=OPERATION, worklist=None):
    snapshot_identity(snapshot,mode);require(str(run_id).isdigit()and int(run_id)>0,'invalid workflow run ID')
    require(type(attempt)is int and attempt>0,'invalid run attempt')
    require(re.fullmatch(r'[0-9a-f]{40}',workflow_sha)and SHA.fullmatch(producer_sha) and SHA.fullmatch(input_manifest_sha),'unbound trusted code/input')
    require(1<=len(hosts)<=256,'worker count out of range');hosts=[host(dict(x))for x in hosts]
    require(len({x['id']for x in hosts})==len(hosts)and len({x['runner_name']for x in hosts})==len(hosts),'duplicate registered runner')
    require(missing.get('snapshot')==snapshot['fingerprint'],'missing-runtime inventory/source mismatch')
    work=[];seen=set()
    for row in missing['modules']:
        m=module_name(row['module']);require(m not in seen,'duplicate task');seen.add(m)
        weight=row.get('project_closure_archived_bytes',row.get('bytes',1));require(type(weight)is int and 0<weight<=MAX_BYTES,'invalid work weight');work.append((m,weight))
    if mode==PROOF_OPERATION:
        policy=proof_policy();allowed=proof_worklist(worklist)
        require(seen<=allowed,'proof request outside pinned affected worklist')
        for h in hosts:
            require(h['cpus']>=policy['minimum_cpus'] and h['memory_mib']>=policy['minimum_memory_mib'],'proof worker capacity below approved minimum')
        require(len(work)<=policy['max_batch_modules']*len(hosts),'proof batch exceeds bounded lease limit')
    groups={h['id']:[]for h in hosts};loads={h['id']:0 for h in hosts}
    for m,w in sorted(work,key=lambda x:(-x[1],x[0])):
        h=min(hosts,key=lambda x:(loads[x['id']]/x['cpus'],len(groups[x['id']]),x['id']))
        groups[h['id']].append(m);loads[h['id']]+=w
    created=int(time.time()if now is None else now);matrix=[];out=Path(output)
    for h in hosts:
        names=groups[h['id']]
        if mode==PROOF_OPERATION:require(len(names)<=proof_policy()['max_batch_modules'],'proof batch exceeds worker limit')
        if not names:continue # Empty NEVER invokes a default Lake target.
        request={'snapshot':snapshot['fingerprint'],'modules':names,'verify':['input-manifest.json']}
        request_sha=rawsha(request);lease_id=hashlib.sha256(f'{run_id}:{attempt}:{h["id"]}:{request_sha}'.encode()).hexdigest()
        lease={'snapshot':snapshot,'operation':mode,'batch':0,'worker':h,'lease_id':lease_id,'request_sha256':request_sha,
               'run_id':str(run_id),'run_attempt':attempt,'workflow_sha':workflow_sha,'producer_sha256':producer_sha,
               'input_manifest_sha256':input_manifest_sha,'created_at':created,'expires_at':created+h['timeout_seconds']+1800}
        
        if mode==PROOF_OPERATION:
            lease['proof_worklist_sha256']=digest(worklist)
            (out/h['id']).mkdir(parents=True,exist_ok=True)
            (out/h['id']/'proof-worklist.txt').write_bytes(Path(worklist).read_bytes())
        atomic(out/h['id']/'request-0.json',request);atomic(out/h['id']/'lease.json',lease)
        matrix.append({**h,'lease_id':lease_id,'timeout_minutes':min(360,(h['timeout_seconds']+3599)//60)})
    atomic(out/'matrix.json',{'include':matrix});atomic(out/'snapshot.json',snapshot)
    return {'include':matrix}

def check_lease(lease, request, run_id, attempt, runner, now=None):
    mode=operation(lease.get('operation'));snapshot_identity(lease['snapshot'],mode)
    require(str(run_id)==lease['run_id']and attempt==lease['run_attempt'],'stale/foreign GHA run')
    require(runner==lease['worker']['runner_name'],'runner identity mismatch');host(lease['worker'])
    now=int(time.time()if now is None else now);require(lease['created_at']<=now<=lease['expires_at'],'expired/future lease')
    require(rawsha(request)==lease['request_sha256'],'request SHA mismatch')
    require(request['snapshot']==lease['snapshot']['fingerprint'],'request source mismatch')
    names=[module_name(x)for x in request['modules']];require(names and len(names)==len(set(names)),'empty/duplicate work')
    require(request.get('verify')==['input-manifest.json'],'arbitrary verification path forbidden')
    if mode==PROOF_OPERATION:
        policy=proof_policy()
        require(lease.get('proof_worklist_sha256')==policy['worklist_sha256'],'unbound proof worklist')
        require(len(names)<=policy['max_batch_modules'],'proof batch too large')
        require(lease['worker']['cpus']>=policy['minimum_cpus'] and lease['worker']['memory_mib']>=policy['minimum_memory_mib'],'proof worker too small')
    return names

def current_cgroup():
    rows=Path('/proc/self/cgroup').read_text().splitlines()
    row=next((x.split(':',2)[2]for x in rows if x.startswith('0::')),None)
    require(row is not None and row.startswith('/')and '..'not in PurePosixPath(row).parts,'cgroup-v2 unit path required')
    return Path('/sys/fs/cgroup')/row.lstrip('/')

def resource_limits(worker, mode=OPERATION):
    mode=operation(mode)
    # Effective limits include the actual worker unit and all cgroup ancestors.
    current=current_cgroup();root=Path('/sys/fs/cgroup');memory=[];cpu=[];pids=[]
    while True:
        for name,dest in [('memory.max',memory),('pids.max',pids)]:
            p=current/name
            if p.exists():
                v=p.read_text().strip()
                if v.isdigit():dest.append(int(v))
        p=current/'cpu.max'
        if p.exists():
            quota,period=p.read_text().split()
            if quota.isdigit()and int(period)>0:cpu.append(int(quota)/int(period))
        if current==root:break
        require(current.is_relative_to(root),'cgroup escaped mount');current=current.parent
    require(memory and 0<min(memory)<=worker['memory_mib']*1024**2,'memory cgroup absent/too large')
    require(cpu and 0<min(cpu)<=worker['cpus'],'CPU cgroup absent/too large')
    pid_limit=16384 if mode==PROOF_OPERATION else 512
    require(pids and 0<min(pids)<=pid_limit,f'PID cgroup absent/too large; set TasksMax={pid_limit}')

def readonly_mount(path):
    target=Path(path).resolve();matches=[]
    def unescape(value):return re.sub(r'\\([0-7]{3})',lambda m:chr(int(m.group(1),8)),value)
    for line in Path('/proc/self/mountinfo').read_text().splitlines():
        f=line.split();mount=Path(unescape(f[4]))
        if target==mount or target.is_relative_to(mount):matches.append((len(mount.parts),'ro'in f[5].split(',')))
    return bool(matches)and max(matches)[1]

def archive_receipt(value):
    require(value.get('schema')==1 and value.get('kind')=='verified-volunteer-artifact-archive','unknown archive verification receipt')
    require(value.get('revision')==BASELINE_COMMIT and value.get('archive_sha256')=='c652456b1f0e35e98b9a0b809f807e729db6cfaad76c986c20fa618f1781d1fb','foreign published archive')
    require(value.get('files')==1195160 and value.get('modules')==149395 and value.get('unpacked_bytes')==82466169920,'incomplete published archive')
    require(value.get('proof_verification')is False,'archive transport receipt must not claim proof verification')

def flat_file(root,row):
    rel=relative(row['path']);name=PurePosixPath(*module_name(row['module']).split('.'))
    require(rel.parent in [PurePosixPath('.lake/build/lib/lean')/name.parent,PurePosixPath('.lake/build/ir')/name.parent]and rel.name.startswith(name.name+'.'),'flat module/path mismatch')
    path=Path(root).resolve()
    for part in (*name.parent.parts,rel.name):
        path=path/part;require(not path.is_symlink(),'flat archive symlink')
    require(path.is_file()and path.resolve().is_relative_to(Path(root).resolve()),'flat archive escaped/missing')
    return path

def verify_flat(root,manifest,fp,receipt):
    archive_receipt(receipt);require(readonly_mount(root),'published archive must be mounted read-only')
    require(manifest.get('schema')==1 and manifest.get('snapshot')==fp,'flat artifact/source mismatch')
    require(len(manifest['files'])<=MAX_FILES and len(set(x['path']for x in manifest['files']))==len(manifest['files']),'duplicate/oversize flat input')
    names=[module_name(m)for m in manifest['modules']];require(len(names)==len(set(names)),'duplicate flat module')
    total=0
    for row in manifest['files']:
        require(row['module']in names and type(row['bytes'])is int and row['bytes']>=0 and SHA.fullmatch(row['sha256']),'invalid flat artifact metadata')
        p=flat_file(root,row);total+=row['bytes'];require(total<=MAX_BYTES,'flat input byte budget exceeded')
        require(p.stat().st_size==row['bytes']and digest(p)==row['sha256'],'published flat part SHA mismatch')
    return total

def no_network():
    # /proc/net is tied to this process network namespace, unlike a host sysfs bind.
    names={line.split(':',1)[0].strip() for line in Path('/proc/net/dev').read_text().splitlines()[2:] if ':' in line}
    return names=={'lo'}

def worker(root, control, output, producer, run_id, attempt, runner):
    control=Path(control);out=Path(output);lease=read(control/'lease.json');request=read(control/'request-0.json')
    names=check_lease(lease,request,run_id,attempt,runner);mode=lease['operation'];require(no_network(),'runtime execution requires network-none isolation');resource_limits(lease['worker'],mode)
    require(digest(producer)==lease['producer_sha256'],'unreviewed runtime producer')
    verify_source(root,lease['snapshot'],mode);fp=lease['snapshot']['fingerprint'];inputs=read(control/'input-manifest.json');require(digest(control/'input-manifest.json')==lease['input_manifest_sha256'],'foreign input manifest')
    archive=lease['worker'].get('archive_root')
    receipt=None
    if archive:
        require(digest(control/'verified-archive.json')==lease['worker']['archive_receipt_sha256'],'foreign archive receipt')
        receipt=read(control/'verified-archive.json');verify_flat(archive,inputs,fp,receipt)
    else:
        if mode==PROOF_OPERATION:
            from proof_baseline import verify_prepared
            verify_prepared(lease['worker']['expanded_base_root'])
        verify_manifest(root,inputs,fp)
    input_paths={row['path']for row in inputs['files']}
    if mode==PROOF_OPERATION:
        require(not archive,'proof workers use native dependency manifests, not the volunteer runtime archive')
        require(set(names)<=proof_worklist(control/'proof-worklist.txt'),'unapproved proof modules')
        require(not(set(names)&set(inputs['modules'])),'requested proof targets must not have stale input artifacts')
    for name in names:
        stem='/'.join(name.split('.'))
        source=Path(root)/'src'/Path(stem+'.lean')
        require(source.is_file() and not source.is_symlink(),'canonical project source absent')
        if mode==OPERATION:require('.lake/build/ir/'+stem+'.ir'in input_paths and '.lake/build/lib/lean/'+stem+'.olean'in input_paths,'published IR/olean absent; source elaboration fallback forbidden')
    protected={row['path']:row['sha256']for row in inputs['files']}if (archive or mode==PROOF_OPERATION) else {row['path']:row['sha256']for row in inputs['files']if any(row['path'].endswith(s)for s in ['.olean','.olean.private','.olean.server','.ir','.ilean'])}
    out.mkdir(parents=True,exist_ok=True);raw=out/'result-0.json'
    env={'PATH':os.environ.get('PATH','/usr/bin:/bin'),'HOME':'/tmp/native-home','TMPDIR':'/tmp','LANG':'C.UTF-8',
         'LEAN_NUM_THREADS':str(lease['worker']['cpus']),'NATIVE_MEMORY_MIB':str(lease['worker']['memory_mib']),'NATIVE_SETUP_ROOT':str(control/'setups'),'NATIVE_OPERATION':mode}
    if mode==PROOF_OPERATION:env.update(NATIVE_PACKAGE_ROOT=lease['worker']['dependency_root'],NATIVE_TOOLCHAIN_ROOT=lease['worker']['toolchain_root'],NATIVE_PRODUCER_JOBS=str(lease['worker'].get('jobs',1)))
    if archive:env.update(NATIVE_ARCHIVE_ROOT=archive,NATIVE_PACKAGE_ROOT=lease['worker']['dependency_root'],NATIVE_TOOLCHAIN_ROOT=lease['worker']['toolchain_root'],NATIVE_PRODUCER_JOBS=str(lease['worker'].get('jobs',1)))
    atomic(out/'ready.json',{'snapshot':fp,'worker':'runtime-only-fileRPC','operation':mode,'lease_id':lease['lease_id'],'runner_name':runner})
    start=time.monotonic()
    # Fixed reviewed backend contract; no command, shell, facets or flags supplied by candidate data.
    proc=subprocess.run([str(Path(producer).resolve()),'--workspace',str(Path(root).resolve()),'--request',str(control/'request-0.json'),'--result',str(raw)],
                        env=env,cwd=root,timeout=lease['worker']['timeout_seconds'],capture_output=True)
    (out/'producer.stdout').write_bytes(proc.stdout);(out/'producer.stderr').write_bytes(proc.stderr)
    require(proc.returncode==0,'runtime producer failed; no retry/reassignment performed')
    verify_source(root,lease['snapshot'],mode)
    by_path={row['path']:row for row in inputs['files']}
    for rel,sha in protected.items():require(digest(flat_file(archive,by_path[rel])if archive else regular(root,rel))==sha,'published archived part changed')
    result=read(raw);rows=result.get('modules',[])
    require([x['module']for x in rows]==names and all(type(x.get('ok'))is bool for x in rows),'incomplete runtime result')
    require(result.get('ok')==all(x['ok']for x in rows),'runtime summary mismatch')
    tool=Path(__file__).with_name('artifact_manifest.py');manifest=out/'artifacts-0.json'
    subprocess.run([sys.executable,str(tool),'create',str(root),fp,str(raw),str(manifest)],check=True,capture_output=True)
    generated=read(manifest);baseline={r['path']:r['sha256']for r in inputs['files']}
    generated['files']=[r for r in generated['files']if baseline.get(r['path'])!=r['sha256']]
    for row in generated['files']:
        require(proof_path(row['path']) if mode==PROOF_OPERATION else runtime_path(row['path']),'unexpected output kind')
    atomic(manifest,generated);verify_manifest(root,generated,fp,names)
    with zipfile.ZipFile(out/'runtime-parts.zip','w',compression=zipfile.ZIP_DEFLATED if mode==PROOF_OPERATION else zipfile.ZIP_STORED,compresslevel=1 if mode==PROOF_OPERATION else None)as z:
        for row in generated['files']:z.write(regular(root,row['path']),row['path'])
    response={'snapshot':fp,'batch':0,'elapsed_ms':int((time.monotonic()-start)*1000),'operation':mode,
              'result':result,'artifacts':{'manifest':'artifacts-0.json','sha256':digest(manifest)},
              'lease_id':lease['lease_id'],'request_sha256':lease['request_sha256'],'run_id':str(run_id),'run_attempt':attempt,'runner_name':runner}
    atomic(out/'response-0.json',response)
    return response

def accept(control, returned, provenance, now=None):
    """Verify only: caller retains exclusive authority to promote into the final cache."""
    control=Path(control);returned=Path(returned);lease=read(control/'lease.json');request=read(control/'request-0.json')
    mode=operation(lease['operation'])
    names=check_lease(lease,request,provenance['run_id'],provenance['run_attempt'],provenance['runner_name'],now)
    require(provenance['workflow_sha']==lease['workflow_sha'],'foreign workflow code')
    require(provenance['artifact_name']==f'native-{lease["run_id"]}-{lease["run_attempt"]}-{lease["lease_id"]}','foreign artifact identity')
    r=read(returned/'response-0.json')
    for k,v in [('snapshot',lease['snapshot']['fingerprint']),('operation',mode),('lease_id',lease['lease_id']),('request_sha256',lease['request_sha256']),('run_id',lease['run_id']),('run_attempt',lease['run_attempt']),('runner_name',lease['worker']['runner_name'])]:require(r.get(k)==v,'response identity mismatch: '+k)
    require(r.get('batch')==0,'foreign runtime batch')
    rows=r['result']['modules'];require([x['module']for x in rows]==names and all(type(x.get('ok'))is bool for x in rows),'response module mismatch');require(r['result'].get('ok')==all(x['ok']for x in rows),'runtime summary mismatch');successful=[x['module']for x in rows if x['ok']]
    require(r['artifacts'].get('manifest')=='artifacts-0.json'and digest(returned/'artifacts-0.json')==r['artifacts']['sha256'],'manifest response SHA mismatch')
    manifest=read(returned/'artifacts-0.json');require(manifest.get('modules')==successful,'manifest work mismatch')
    if mode==PROOF_OPERATION:
        require(set(names)<=proof_worklist(control/'proof-worklist.txt'),'proof worklist mismatch')
        require(all(proof_path(row['path']) for row in manifest['files']),'unexpected proof output kind')
        paths={row['path'] for row in manifest['files']}
        for name in successful:
            stem=name.replace('.','/')
            for suffix in PROOF_PARTS:
                part='ir' if suffix=='.c' else 'lib/lean'
                require(f'.lake/build/{part}/{stem}{suffix}' in paths,'successful proof missing complete output: '+name+suffix)
    verify_zip(returned/'runtime-parts.zip',manifest,lease['snapshot']['fingerprint'],names,runtime_only=mode==OPERATION)
    return {'verified_transport':True,'operation':mode,'native_proof_check':'NOT_PERFORMED','lease_id':lease['lease_id'],
            'manifest_sha256':r['artifacts']['sha256'],'modules':successful,'failed_modules':[x['module']for x in rows if not x['ok']],'promotion_performed':False}

def main():
    p=argparse.ArgumentParser();sub=p.add_subparsers(dest='mode',required=True)
    q=sub.add_parser('plan');q.add_argument('--snapshot',required=True);q.add_argument('--missing',required=True);q.add_argument('--hosts',required=True);q.add_argument('--run-id',required=True);q.add_argument('--attempt',required=True,type=int);q.add_argument('--workflow-sha',required=True);q.add_argument('--producer-sha',required=True);q.add_argument('--input-manifest-sha',required=True);q.add_argument('--output',required=True)
    q=sub.add_parser('stage');q.add_argument('--archive',required=True);q.add_argument('--root',required=True);q.add_argument('--manifest',required=True);q.add_argument('--fingerprint',required=True)
    q=sub.add_parser('worker');q.add_argument('--root',required=True);q.add_argument('--control',required=True);q.add_argument('--output',required=True);q.add_argument('--producer',required=True);q.add_argument('--run-id',required=True);q.add_argument('--attempt',required=True,type=int);q.add_argument('--runner',required=True)
    q=sub.add_parser('accept');q.add_argument('--control',required=True);q.add_argument('--returned',required=True);q.add_argument('--provenance',required=True)
    a=p.parse_args();v=vars(a);mode=v.pop('mode')
    if mode=='plan':v['snapshot']=read(v['snapshot']);v['missing']=read(v['missing']);v['hosts']=read(v['hosts']);print(json.dumps(plan(**v)))
    elif mode=='stage':v['manifest']=read(v['manifest']);print(stage_zip(**v))
    elif mode=='worker':print(json.dumps(worker(**v)))
    else:v['provenance']=read(v['provenance']);print(json.dumps(accept(**v)))
if __name__=='__main__':main()
