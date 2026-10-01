"""Bounded post-planning pipeline; every failed attempt remains visible."""
import os,sys,json,time,subprocess,concurrent.futures,hashlib
from pathlib import Path
HERE=Path(__file__).resolve().parent;PYTHON='/tmp/exploration-lp-gpu-venv/bin/python'
manifest=json.loads((HERE/'completion_manifest.json').read_text());jobs=manifest['jobs']
start=time.monotonic();pending=list(jobs);running={};done=[];cpus=[6,7,8]

def write():
    p=HERE/'audit_queue.json';tmp=p.with_suffix('.tmp');tmp.write_text(json.dumps(dict(status='running' if pending or running else 'finished',pid=os.getpid(),expected=18,pending=[j['id'] for j in pending],running={str(p.pid):dict(cell=j['id'],cpu=c) for p,(j,c,_,_) in running.items()},completed=done,seconds=time.monotonic()-start),indent=2)+'\n');tmp.replace(p)
while pending or running:
    for p,(j,cpu,f,ts) in list(running.items()):
        if p.poll() is not None:
            f.close();done.append(dict(cell=j['id'],exit_code=p.returncode,seconds=time.monotonic()-ts));cpus.append(cpu);del running[p]
    for j in pending[:]:
        source=HERE/'completion_retry_results'/j['id'];rp=source/'result.json'
        if not rp.exists():continue
        r=json.loads(rp.read_text())
        if r.get('status')=='failed':pending.remove(j);done.append(dict(cell=j['id'],status='planning_failed'));continue
        if r.get('status')!='complete' or not cpus:continue
        pending.remove(j);cpu=cpus.pop();f=(HERE/(j['id']+'_pipeline.log')).open('a')
        command=[PYTHON,str(HERE/'pipeline_one.py'),'--cell',j['id']]
        p=subprocess.Popen(['prlimit','--as=5368709120','--','taskset','-c',str(cpu)]+command,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
        running[p]=(j,cpu,f,time.monotonic())
    write()
    if time.monotonic()-start>3*3600:raise TimeoutError('Three-hour controller cap; child audit caps remain active')
    if pending or running:time.sleep(5)
