"""Observe the dedicated build cgroup; no network or candidate-code execution."""
import json,os,tempfile,threading,time
from pathlib import Path
import rpc


def integer(path):
    try:
        value=path.read_text().strip()
        return int(value) if value.isdigit() else None
    except OSError:return None


def counters(group):
    try:cpu=dict(line.split() for line in (group/'cpu.stat').read_text().splitlines())
    except(OSError,ValueError):cpu={}
    return {'cpu_usage_usec':int(cpu['usage_usec']) if cpu.get('usage_usec','').isdigit() else None,
            'memory_current_bytes':integer(group/'memory.current'),'memory_peak_bytes':integer(group/'memory.peak'),
            'tasks_current':integer(group/'pids.current'),'tasks_peak':integer(group/'pids.peak')}


class HostProfile:
    def __init__(self):
        self.group=rpc.current_cgroup();self.start=time.monotonic();self.before=counters(self.group)
        self.memory_observed=self.before['memory_current_bytes'];self.tasks_observed=self.before['tasks_current']
        self.stop=threading.Event();self.thread=threading.Thread(target=self.sample,daemon=True)
        self.thread.start()

    def sample(self):
        while not self.stop.wait(.5):
            values=counters(self.group)
            for key,field in [('memory_current_bytes','memory_observed'),('tasks_current','tasks_observed')]:
                value=values[key];old=getattr(self,field)
                if value is not None:setattr(self,field,max(old or 0,value))

    def finish(self,returncode):
        self.stop.set();self.thread.join();after=counters(self.group);wall=time.monotonic()-self.start
        before_cpu=self.before['cpu_usage_usec'];after_cpu=after['cpu_usage_usec']
        cpu=(after_cpu-before_cpu)/1e6 if before_cpu is not None and after_cpu is not None and after_cpu>=before_cpu else None
        return {'schema':1,'kind':'dedicated-host-cgroup-profile','wall_seconds':wall,'exit_status':returncode,
                'cpu_seconds':cpu,'average_used_cpus':cpu/wall if cpu is not None and wall else None,
                'memory_peak_bytes':after['memory_peak_bytes'],'memory_observed_max_bytes':self.memory_observed,
                'tasks_peak':after['tasks_peak'],'tasks_observed_max':self.tasks_observed,
                'sample_interval_seconds':.5,'scope':'entire dedicated build cgroup, including wrapper and child processes',
                'unknown_values_remain_null':True}


def publish_profile(output,value):
    """Create outside the sandbox-writable return directory, then replace its entry."""
    output=Path(output).resolve();returned=output/'returned'
    rpc.require(returned.is_dir()and not returned.is_symlink(),'invalid profile return directory')
    fd,name=tempfile.mkstemp(prefix='.host-profile-',dir=output)
    temporary=Path(name)
    try:
        with os.fdopen(fd,'w')as stream:json.dump(value,stream,separators=(',',':'));stream.write('\n')
        os.replace(temporary,returned/'host-profile.json')
    finally:temporary.unlink(missing_ok=True)
