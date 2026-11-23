#!/usr/bin/env python3
"""Network/credential-isolated bwrap launcher. Invoke INSIDE a bounded systemd user unit."""
import argparse, os, shutil, subprocess, sys
from pathlib import Path
import rpc
from producer import dependency_paths

def system_mounts():
    argv=[]
    for name in ['/nix/store','/usr','/bin','/sbin','/lib','/lib64']:
        path=Path(name)
        if path.exists():argv+=['--ro-bind',str(path.resolve()),name]
    sw=Path('/run/current-system/sw')
    if sw.exists():argv+=['--ro-bind',str(sw.resolve()),str(sw)]
    return argv

def dependency_mounts(root,deps,output,packages,overlay):
    """Only private upper/copy paths are writable; original caches stay read-only."""
    argv=[]
    for package in packages:
        name=rpc.module_name(package['name'])
        destination=root/'.lake/packages'/name
        private=output/'dependency-overlays'/name
        if overlay:
            upper,work=private/'upper',private/'work'
            upper.mkdir(parents=True,exist_ok=True);work.mkdir(exist_ok=True)
            argv+=['--overlay-src',str(deps/name),'--overlay',str(upper),str(work),str(destination)]
        else:
            copied=private/'copy';copied.mkdir(parents=True,exist_ok=True)
            for entry in (deps/name).iterdir():
                if entry.name=='.git':continue
                subprocess.run(['cp','-a','--reflink=auto','--no-preserve=ownership',
                                str(entry),str(copied/entry.name)],check=True,
                               env={'PATH':os.environ.get('PATH','/usr/bin:/bin')})
            argv+=['--bind',str(copied),str(destination)]
            metadata=deps/name/'.git'
            if metadata.exists():
                if metadata.is_dir():(copied/'.git').mkdir(exist_ok=True)
                else:(copied/'.git').touch()
                argv+=['--ro-bind',str(metadata),str(destination/'.git')]
    return argv

def command(root,control,output,producer,run_id,attempt,runner,seal_base=True):
    root=Path(root).resolve();control=Path(control).resolve();output=Path(output).resolve();producer=Path(producer).resolve()
    lease=rpc.read(control/'lease.json');request=rpc.read(control/'request-0.json')
    rpc.check_lease(lease,request,run_id,attempt,runner);rpc.resource_limits(lease['worker'],lease['operation'])
    rpc.require(rpc.digest(producer)==lease['producer_sha256'],'unreviewed backend wrapper')
    rpc.require((root/'.lake/build').is_dir(),'use a private candidate checkout with an existing empty .lake/build')
    rpc.require(not (root/'.lake/build').is_symlink(),'cache mount must not be a symlink')
    rpc.require(not output.exists() or (output.is_dir() and not any(output.iterdir())),
                'lease output must be fresh; preserve prior lease results at their original path')
    output.mkdir(parents=True,exist_ok=True);cache=output/'cache';cache.mkdir(exist_ok=True);returned=output/'returned';returned.mkdir(exist_ok=True)
    worker=lease['worker'];proof=lease['operation']==rpc.PROOF_OPERATION
    archive=Path(worker['archive_root']).resolve() if not proof else None
    deps=Path(worker['dependency_root']).resolve();tc=Path(worker['toolchain_root']).resolve()
    if proof:
        rpc.require(producer.name=='proof_producer.py','wrong proof wrapper')
        rpc.require(set(request['modules'])<=rpc.proof_worklist(control/'proof-worklist.txt'),'unapproved proof targets')
        inputs=rpc.read(control/'input-manifest.json')
        rpc.require(rpc.digest(control/'input-manifest.json')==lease['input_manifest_sha256'],'unbound proof inputs')
        rpc.require(not set(request['modules'])&set(inputs['modules']),'stale target artifacts in proof inputs')
        seed=output/'seed';seed.mkdir(exist_ok=True)
        rpc.stage_zip(control/'input-parts.zip',seed,inputs,lease['snapshot']['fingerprint'])
        cache=seed/'.lake/build';cache.mkdir(parents=True,exist_ok=True)
        rpc.require((root/'.lake/packages').is_dir() and not(root/'.lake/packages').is_symlink(),
                    'private checkout requires an empty real package mountpoint')
    libs={Path(x)for x in dependency_paths(deps,root/'lake-manifest.json')}
    tools=Path(__file__).parent.resolve()
    rpc.require(producer.parent==tools,'backend wrapper must belong to the trusted tools bundle')
    rpc.require(shutil.which('bwrap') is not None,'bubblewrap required; no unsandboxed fallback')
    expanded=None
    overlay='--overlay-src' in subprocess.check_output(['bwrap','--help'],text=True) if proof else False
    if proof and seal_base:
        from proof_baseline import ensure
        expanded=ensure(worker,control,tools,system_mounts())
        if not overlay:
            # Copy/reflink private inodes on older Bubblewrap. Incoming current
            # dependencies override base copies, never the other way around.
            private=output/'private-base-build';private.mkdir(exist_ok=True)
            subprocess.run(['cp','-a','--reflink=auto','--no-preserve=ownership',
                            str(expanded/'.lake/build')+'/.',str(private)],check=True)
            for row in inputs['files']:
                relative=Path(row['path']).relative_to('.lake/build')
                dest=private/relative;dest.parent.mkdir(parents=True,exist_ok=True)
                shutil.copyfile(cache/relative,dest)
            cache=private
    # Start with an empty filesystem, not a read-only view of host runner secrets.
    argv=['bwrap','--tmpfs','/','--dev','/dev','--proc','/proc','--unshare-net','--unshare-pid',
          '--die-with-parent','--new-session','--clearenv','--dir','/tmp','--dir','/tmp/native-home']
    argv+=system_mounts()
    for name in ['/sys/fs/cgroup']:
        argv+=['--ro-bind',name,name]
    mounts={root,tools,control,deps,tc,*libs}
    if archive:mounts.add(archive)
    if proof:mounts.add(Path(worker['baseline_cache_root']).resolve())
    if expanded:mounts.add(expanded)
    for path in sorted(mounts,key=lambda p:(len(p.parts),str(p))):
        argv+=['--ro-bind',str(path),str(path)]
    if proof:
        private_lake=output/'project-lake'
        for directory in ['build','packages','config']:
            (private_lake/directory).mkdir(parents=True,exist_ok=True)
        argv+=['--bind',str(private_lake),str(root/'.lake')]
        argv+=['--ro-bind',str(deps),str(root/'.lake/packages')]
        argv+=dependency_mounts(root,deps,output,rpc.read(root/'lake-manifest.json')['packages'],overlay)
    if proof and overlay and expanded:
        work=output/'base-overlay-work';work.mkdir(exist_ok=True)
        argv+=['--overlay-src',str(expanded/'.lake/build'),'--overlay',str(cache),str(work),str(root/'.lake/build')]
    else:argv+=['--bind',str(cache),str(root/'.lake/build')]
    argv+=['--bind',str(returned),str(returned)]
    env={'PATH':str(tc/'bin')+':/usr/bin:/bin:/run/current-system/sw/bin','HOME':'/tmp/native-home','LANG':'C.UTF-8',
         'GIT_CONFIG_NOSYSTEM':'1','GIT_CONFIG_GLOBAL':'/dev/null'}
    for key,value in env.items():argv+=['--setenv',key,value]
    argv+=['--chdir',str(root),sys.executable,str(tools/'rpc.py'),'worker','--root',str(root),'--control',str(control),
           '--output',str(returned),'--producer',str(producer),'--run-id',str(run_id),'--attempt',str(attempt),'--runner',runner]
    return argv

def main():
    p=argparse.ArgumentParser()
    for name in ['root','control','output','producer','run-id','runner']:p.add_argument('--'+name,required=True)
    p.add_argument('--attempt',required=True,type=int);p.add_argument('--dry-run',action='store_true');a=p.parse_args()
    args=vars(a);dry=args.pop('dry_run');argv=command(**args)
    if dry:
        import json;print(json.dumps(argv));return 0
    from host_profile import HostProfile,publish_profile
    profile=HostProfile()
    try:
        result=subprocess.run(argv,env={'PATH':os.environ.get('PATH','/usr/bin:/bin')},timeout=rpc.read(Path(a.control)/'lease.json')['worker']['timeout_seconds']+120)
    except BaseException:
        publish_profile(a.output,profile.finish(None))
        raise
    publish_profile(a.output,profile.finish(result.returncode))
    return result.returncode
if __name__=='__main__':sys.exit(main())
