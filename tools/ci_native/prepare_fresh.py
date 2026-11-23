"""Prepare policy-approved official4.37 packages with ZERO project baseline."""
import fcntl,os,shutil,subprocess
from pathlib import Path
import rpc
from producer import dependency_paths


def prepare_fresh(candidate,control,state,lease):
    policy=rpc.proof_policy();snapshot=lease['snapshot'];baseline=policy['baseline']
    rpc.require(baseline=={'fresh_project':True,'unchanged_modules':0,'unchanged_module_names':[]},'invalid fresh project baseline')
    rpc.require(snapshot['toolchain']=='leanprover/lean4:v4.37.0-rc1','fresh helper requires stock4.37')
    for name,key in [('lakefile.toml','lakefile_sha256'),('lake-manifest.json','manifest_sha256')]:
        rpc.require(rpc.digest(candidate/name)==policy['snapshot'][key]==snapshot[key],'unapproved candidate configuration')
    environment={k:os.environ[k]for k in ('HOME','PATH','TMPDIR','XDG_CACHE_HOME','ELAN_HOME')if k in os.environ}
    environment.update(ELAN_TOOLCHAIN=snapshot['toolchain'],GIT_CONFIG_NOSYSTEM='1',GIT_CONFIG_GLOBAL='/dev/null',LANG='C.UTF-8',LAKE_ARTIFACT_CACHE='false')
    subprocess.run(['elan','toolchain','install',snapshot['toolchain']],env=environment,check=True)
    lean=Path(subprocess.check_output(['elan','which','lean'],env=environment,text=True).strip())
    tc=lean.parent.parent;version=subprocess.check_output([str(lean),'--version'],text=True)
    rpc.require('4.37.0-rc1'in version and '0b77e129'in version,'wrong stock4.37 install')
    key=rpc.rawsha(policy['snapshot']);destination=state/'fresh-proof-dependencies'/key
    destination.parent.mkdir(parents=True,exist_ok=True)
    with (destination.parent/(key+'.lock')).open('a')as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        seal=destination/'complete.json';expected={'snapshot_configuration':policy['snapshot'],'project_baseline_modules':0}
        if seal.exists():rpc.require(rpc.read(seal)==expected,'fresh dependency seal mismatch')
        else:
            destination.mkdir(exist_ok=True)
            for name in ('lakefile.toml','lake-manifest.json','lean-toolchain'):shutil.copyfile(candidate/name,destination/name)
            (destination/'src').mkdir(exist_ok=True)
            subprocess.run([str(tc/'bin/lake'),'exe','mathlib/cache','get'],cwd=destination,env=environment,check=True)
            dependency_paths(destination/'.lake/packages',destination/'lake-manifest.json')
            rpc.atomic(seal,expected)
    for name,keyname in [('lakefile.toml','lakefile_sha256'),('lake-manifest.json','manifest_sha256')]:rpc.require(rpc.digest(destination/name)==snapshot[keyname],'prepared config changed')
    dependency_paths(destination/'.lake/packages',candidate/'lake-manifest.json')
    emptycache=state/'fresh-empty-project-cache'/key;emptycache.mkdir(parents=True,exist_ok=True)
    rpc.require(not any(emptycache.iterdir()),'fresh project cache must stay empty')
    lease['worker'].update(dependency_root=str(destination/'.lake/packages'),toolchain_root=str(tc),baseline_cache_root=str(emptycache),expanded_base_root=str(state/'proof-bases'/rpc.rawsha({'baseline':baseline,'worklist':policy['worklist_sha256']})))
    rpc.atomic(control/'lease.json',lease)
    for part in ('build','packages'):(candidate/'.lake'/part).mkdir(parents=True,exist_ok=True)
    return lease['worker']
