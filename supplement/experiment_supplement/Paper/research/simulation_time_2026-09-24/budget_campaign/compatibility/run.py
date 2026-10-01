"""Wait for the primary grid, then execute the separately frozen follow-up."""
from common import *
import subprocess,signal,time,shutil,resource
from datetime import datetime,timedelta,timezone
PYTHON='/tmp/exploration-lp-gpu-venv/bin/python'

def main():
    source=verify_sources();jobs=json.loads((HERE/'JOBS.json').read_text())['jobs'];records=[];active=None
    launch=json.loads((PARENT/'LAUNCH.json').read_text());deadline=datetime.fromisoformat(launch['started_utc'])+timedelta(seconds=launch['wall_seconds'])
    def stopped():return (PARENT/'STOP').exists() or (HERE/'STOP').exists() or datetime.now(timezone.utc)>=deadline
    def update(status,reason=None):
        counts={}
        for r in records:counts[r['status']]=counts.get(r['status'],0)+1
        write(HERE/'STATUS.json',dict(status=status,updated_utc=now(),pid=os.getpid(),sources_sha256=source,deadline_utc=deadline.isoformat(),active=active,planned=len(jobs),finished=len(records),pending=len(jobs)-len(records),counts=counts,records=records,reason=reason))
    def child(cmd,log,until):
        def limits():
            os.sched_setaffinity(0,{10});resource.setrlimit(resource.RLIMIT_AS,(8*1024**3,)*2)
        with log.open('w') as f:
            p=subprocess.Popen(cmd,cwd=HERE,stdout=f,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=limits)
            while p.poll() is None:
                if stopped() or time.monotonic()>until:
                    os.killpg(p.pid,signal.SIGTERM)
                    try:p.wait(timeout=3)
                    except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);p.wait()
                    return dict(code=p.returncode,status='timeout_or_stop')
                time.sleep(.5)
            return dict(code=p.returncode,status='exited')
    write(HERE/'LAUNCH.json',dict(created_utc=now(),pid=os.getpid(),cpu=10,worker_count=1,parent_launch_sha256=sha(PARENT/'LAUNCH.json'),sources_sha256=source,deadline_utc=deadline.isoformat()))
    while True:
        if stopped():update('stopped_or_budget_exhausted');return
        primary=json.loads((PARENT/'STATUS.json').read_text())
        if primary['status']=='complete':break
        if primary['status']!='running':update('deferred','Primary campaign did not complete');return
        update('waiting_for_primary');time.sleep(5)
    for job in jobs:
        if stopped():update('stopped_or_budget_exhausted');return
        if shutil.disk_usage(HERE).free<15*1024**3:update('resource_stop','disk reserve');return
        used=sum(p.stat().st_size for d in [PARENT/'results',HERE/'results'] if d.exists() for p in d.rglob('*') if p.is_file())
        if used>4*1024**3:update('resource_stop','combined output allowance');return
        verify_sources();out=HERE/'results'/job['id'];assert not out.exists();out.parent.mkdir(exist_ok=True)
        active=dict(id=job['id'],stage='optimization');update('running');start=time.monotonic();until=start+180
        execution=child([PYTHON,str(HERE/'worker.py'),job['id']],out.parent/(job['id']+'.log'),until)
        record=dict(id=job['id'],execution=execution,status='failed')
        if execution['code']==0:
            active['stage']='independent_check';update('running')
            record['verification']=child([PYTHON,str(HERE/'verify.py'),str(out)],out/'verify.log',until)
            if (out/'CHECK.json').exists():
                c=json.loads((out/'CHECK.json').read_text())
                if c['status']=='passed':record.update(status='passed',classification=c['classification'],reward_regret_lower=c['reward_regret_lower'],reward_regret_upper=c['reward_regret_upper'])
        if execution['status']!='exited':record['status']=execution['status']
        record['seconds']=time.monotonic()-start;records.append(record);active=None;update('running')
    update('complete')

if __name__=='__main__':main()
