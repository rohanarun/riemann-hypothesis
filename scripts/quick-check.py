#!/usr/bin/env python3
"""Trusted, bounded changed-module diagnostics; never claims a complete PR build."""
import argparse, importlib.util, json, os
from pathlib import Path
import re, subprocess, sys, tempfile
from types import SimpleNamespace

HERE = Path(__file__).resolve().parent
MAX_ROOTS, MAX_CLOSURE = 8, 2000

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module

ci = load('quick_ci', HERE / 'ci-build.py')
prep = load('quick_prepare', HERE / 'ci-prepare.py')

def write(path, value):
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    Path(path).write_text(json.dumps(value, indent=2) + '\n')

def runner(identifier):
    matches = [row for row in json.loads((HERE / 'quick-runners.json').read_text()) if row['id'] == identifier]
    if len(matches) != 1: raise ValueError('unapproved small runner')
    return matches[0]

def imports(path):
    if path.stat().st_size > 4 * 1024**2: raise ValueError('source/header exceeds quick-check limit')
    text = path.read_text(); depth = 0; cleaned = []; i = 0
    # Only the header is needed; preserve line positions across nested comments.
    while i < len(text):
        if text.startswith('/-', i): depth += 1; i += 2
        elif depth and text.startswith('-/', i): depth -= 1; i += 2
        elif not depth and text.startswith('--', i):
            end = text.find('\n', i); i = len(text) if end < 0 else end
        elif depth:
            if text[i] == '\n': cleaned.append('\n')
            i += 1
        else: cleaned.append(text[i]); i += 1
    if depth: raise ValueError('unterminated header/source comment')
    result = []
    for line in ''.join(cleaned).splitlines():
        line = line.strip()
        if not line or line in ('module', 'prelude'): continue
        match = re.fullmatch(r'(?:public\s+)?(?:meta\s+)?import(?:\s+all)?\s+([\w\']+(?:\.[\w\']+)*)', line)
        if match: result.append(match[1]); continue
        if re.match(r'(?:public\s+|meta\s+)*import\b', line): raise ValueError('unsupported import header')
        break
    return result

def dependency_closure(project, targets, maximum=MAX_CLOSURE):
    pending, seen = list(targets), set()
    while pending:
        module = pending.pop()
        if module in seen: continue
        if not ci.MODULE.fullmatch(module): raise ValueError('invalid module name')
        source = project / 'src' / (module.replace('.', '/') + '.lean')
        if not source.exists(): continue  # Package imports are resolved by stock Lake.
        ci.safe_file(project, str(source.relative_to(project)))
        seen.add(module)
        if len(seen) > maximum: raise ValueError('project ancestor cone exceeds small-runner budget')
        pending.extend(imports(source))
    return sorted(seen)

def plan(candidate, request):
    candidate = Path(candidate).resolve()
    expected = request['expected']
    if request.get('base_ref') != 'main': raise ValueError('quick checks require main as base')
    if ci.git(candidate, 'rev-parse', 'HEAD') != expected['candidate_head']: raise ValueError('candidate checkout differs from resolved merge')
    ci.validate_inputs(candidate, ci.DEPENDENCIES)
    if ci.sha256(candidate/'lakefile.toml') != ci.sha256(HERE.parent/'lakefile.toml'): raise ValueError('configuration changes need the priority/full build pool')
    base = request.get('base_head', '')
    if not re.fullmatch('[0-9a-f]{40}', base): raise ValueError('resolved base identity missing')
    changed = ci.git(candidate, 'diff', '--name-only', base, expected['candidate_head'], '--', 'src').splitlines()
    changed = [name for name in changed if name.endswith('.lean')]
    if len(changed) > MAX_ROOTS: raise ValueError('more than eight changed source roots; deferred')
    targets = []
    for name in changed:
        if not name.startswith('src/') or not (candidate/name).is_file(): raise ValueError('deleted/unsafe source requires full build')
        target = name[4:-5].replace('/', '.')
        if not ci.MODULE.fullmatch(target): raise ValueError('invalid target name')
        targets.append(target)
    return {'schema':1, 'status':'ready' if targets else 'no_source_changes', 'scope':'changed-modules-only',
            'full_build':False, 'candidate_head':expected['candidate_head'], 'pr_head':request['pr_head'],
            'base_head':base, 'targets':sorted(targets), 'closure':dependency_closure(candidate, targets)}

def resolve(args):
    host = runner(args.runner)
    try:
        prep.resolve(SimpleNamespace(pr=args.pr, head=args.head or None, output=args.output, require_main=True))
        request = json.loads(Path(args.output).read_text())
        request['quick_runner'] = host
        request['quick_status'] = 'resolved'
    except ValueError as error:
        request = {'pr_number':args.pr,'quick_runner':host,'quick_status':'deferred','reason':str(error), 'full_build':False}
    write(args.output, request)
    if os.environ.get('GITHUB_OUTPUT'):
        with open(os.environ['GITHUB_OUTPUT'],'a') as out:
            print('runnable='+str(request['quick_status']=='resolved').lower(),file=out)
            print('candidate='+request.get('expected',{}).get('candidate_head',''),file=out)
            print('runner_label='+host['label'],file=out)
    print(json.dumps({'pr':args.pr,'status':request['quick_status'],'scope':'changed-modules-only','reason':request.get('reason','')}))

def doctor_safe(report,host):
    return (report.get('ready') and report.get('systemd_user') and report.get('cgroup_v2')
            and report.get('physical_ram_gib',0) >= host['memory_gib']*1.5)

def resource_limits(host, root=Path('/sys/fs/cgroup')):
    line=next(line for line in Path('/proc/self/cgroup').read_text().splitlines()if line.startswith('0::'))
    directory=root/line[3:].lstrip('/')
    quota,period=(directory/'cpu.max').read_text().split()
    memory=(directory/'memory.max').read_text().strip()
    tasks=(directory/'pids.max').read_text().strip()
    if quota=='max' or int(quota)>host['cpus']*int(period):raise ValueError('quick-check requires bounded CPU cgroup')
    if memory=='max' or int(memory)>host['memory_gib']*1024**3:raise ValueError('quick-check requires bounded memory cgroup')
    if tasks=='max' or int(tasks)>16384:raise ValueError('quick-check requires bounded PID cgroup')
    if (directory/'memory.swap.max').read_text().strip()!='0':raise ValueError('quick-check swap must be disabled')

def run(args):
    candidate, state, output = map(lambda p:Path(p).resolve(),(args.candidate,args.state,args.output))
    request = json.loads(Path(args.request).read_text()); host = runner(args.runner)
    if request.get('quick_runner') != host or os.environ.get('RUNNER_NAME') != host['runner_name']: raise ValueError('wrong runner/changed limits')
    resource_limits(host)
    output.mkdir(parents=True,exist_ok=False)
    try: selected = plan(candidate,request)
    except ValueError as error:
        write(output/'result.json',{'status':'deferred','reason':str(error),'full_build':False,'scope':'changed-modules-only','candidate_head':request['expected']['candidate_head']}); return 0
    write(output/'plan.json',selected)
    if not selected['targets']:
        write(output/'result.json',selected); return 0
    # Host doctor runs trusted code before any candidate execution.
    doctor = subprocess.run([sys.executable,str(HERE/'ci-runner.py'),'doctor','--work-directory',str(state),'--minimum-disk-gib','100'],capture_output=True,text=True)
    (output/'doctor.json').write_text(doctor.stdout)
    report=json.loads(doctor.stdout)
    if doctor.returncode or not doctor_safe(report,host): raise ValueError('runner doctor failed; candidate was not executed')
    paths_file=output/'paths.json'
    prep.prepare(SimpleNamespace(trusted=HERE.parent,candidate=candidate,state=state,request=args.request,output=paths_file,quick_plan=output/'plan.json'))
    paths=json.loads(paths_file.read_text())
    tc=Path(subprocess.check_output(['elan','which','lean'],env={**prep.clean_env(),'ELAN_TOOLCHAIN':ci.TOOLCHAIN},text=True).strip()).parent.parent
    parent=state/'quick-work';parent.mkdir(parents=True,exist_ok=True)
    work=Path(tempfile.mkdtemp(prefix='quick-',dir=parent));project=work/'project';project.mkdir()
    ci.snapshot(candidate,request['expected']['candidate_head'],project)
    cache,result,control=[work/name for name in ['cache','result','control']]
    for directory in [cache/'artifacts',result,control]:directory.mkdir(parents=True)
    packages=Path(paths['packages']);ci.validate_packages(project,packages)
    private=ci.private_package_builds(project,packages,work/'dependency-builds')
    overrides=ci.package_overrides(project,control)
    baseline_args=SimpleNamespace(baseline_manifest=Path(paths['baseline_manifest']),baseline_manifest_sha256=ci.BASE_MANIFEST,
                                  baseline_map=Path(paths['baseline_map']),baseline_cache=Path(paths['baseline_cache']))
    _,warm,_=ci.baseline(baseline_args,project,cache,modules=set(selected['closure']))
    (project/'.lake/packages').mkdir(parents=True,exist_ok=True)
    command=ci.sandbox(tc,project,packages,cache,result,control,host['jobs'],private)
    if warm:subprocess.run(command+['/opt/lean/bin/leantar','--jobs',str(host['jobs']),'-f','-x','-j','-'],input=json.dumps(warm),text=True,env=ci.trusted_env(),check=True)
    env=ci.trusted_env()
    with(output/'build.log').open('wb')as log:
        code=ci.supervised_build(command+['/opt/lean/bin/lake','--packages',overrides,'--rehash','build',*['+'+m for m in selected['targets']]],env,log,[work],10,timeout_seconds=host['seconds'])
    status='changed_roots_pass'if code==0 else'deferred_budget'if code in(124,137,143)else'changed_roots_fail'
    write(output/'result.json',{'status':status,'scope':'changed-modules-only','full_build':False,'exit_code':code,
                               'candidate_head':selected['candidate_head'],'targets':selected['targets'],'ancestor_modules':len(selected['closure']),
                               'raw_work_preserved':str(work),'raw_work_source_tree':ci.git(candidate,'rev-parse','HEAD:src'),
                               'raw_work_uploaded':False,'runner_name':host['runner_name']})
    # Full raw native output survives in a source-bound private work directory.
    return 1 if status=='changed_roots_fail'else 0

def main():
    p=argparse.ArgumentParser();sub=p.add_subparsers(dest='command',required=True)
    r=sub.add_parser('resolve');r.add_argument('--pr',type=int,required=True);r.add_argument('--head',default='');r.add_argument('--runner',required=True);r.add_argument('--output',required=True);r.set_defaults(function=resolve)
    r=sub.add_parser('run')
    for name in ['candidate','state','request','output','runner']:r.add_argument('--'+name,required=True)
    r.set_defaults(function=run);args=p.parse_args();return args.function(args)
if __name__=='__main__':sys.exit(main())
