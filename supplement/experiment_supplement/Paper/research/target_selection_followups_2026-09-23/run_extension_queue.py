"""Bounded two-CPU queue; original saved policies remain read-only."""
from common import *
import argparse,subprocess,time,threading,signal,shutil
from concurrent.futures import ThreadPoolExecutor,as_completed
from datetime import datetime,timezone

def main():
    p=argparse.ArgumentParser();p.add_argument('manifest',type=Path);p.add_argument('--output',type=Path,required=True);args=p.parse_args()
    manifest=json.loads(args.manifest.read_text());args.output.mkdir(parents=True,exist_ok=True)
    for name,h in manifest['source_sha256'].items():assert digest(HERE/name)==h
    start=time.monotonic();deadline=start+manifest['hours_limit']*3600
    state=dict(status='running',pid=os.getpid(),started_utc=datetime.now(timezone.utc).isoformat(),manifest_sha256=digest(args.manifest),jobs=[])
    write(args.output/'queue.json',state)
    stop=threading.Event();active={};lock=threading.Lock()
    def stopped(signum,frame):stop.set()
    signal.signal(signal.SIGTERM,stopped);signal.signal(signal.SIGINT,stopped)
    def worker(job):
        cell=job['cell']
        if stop.is_set():return dict(cell=cell,status='skipped_stop')
        out=args.output/cell;out.mkdir(exist_ok=False)
        if time.monotonic()>=deadline:return dict(cell=cell,status='skipped_deadline')
        for name,h in manifest['source_sha256'].items():assert digest(HERE/name)==h
        original=ORIGINAL/'main_results'/cell
        assert digest(original/job['checkpoint']/'policy.npz')==job['policy_sha256']
        wall=min(1500,deadline-time.monotonic());cpu=job['cpu']
        cmd=['prlimit','--as=4294967296','--','taskset','-c',str(cpu),sys.executable,str(HERE/'recover_saved.py'),'--cell',cell,'--output',str(out),'--wall-seconds',str(max(1,wall-15))]
        ts=time.monotonic()
        with (out/'process.log').open('w') as log:
            proc=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,start_new_session=True,stdin=subprocess.DEVNULL)
            with lock:active[proc.pid]=proc
            write(out/'process.json',dict(pid=proc.pid,command=cmd,cpu=cpu,wall_seconds=wall))
            while proc.poll() is None:
                if shutil.disk_usage(HERE).free<15*1024**3:stop.set()
                if stop.is_set() or time.monotonic()-ts>=wall or time.monotonic()>=deadline:
                    os.killpg(proc.pid,signal.SIGTERM)
                    try:proc.wait(timeout=5)
                    except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait()
                    break
                stop.wait(.5)
            with lock:active.pop(proc.pid,None)
        result=dict(cell=cell,returncode=proc.returncode,seconds=time.monotonic()-ts,aliases=job['aliases'])
        if proc.returncode==0:
            checkcmd=[sys.executable,str(HERE/'check_recovery.py'),str(out)]
            with (out/'verification.log').open('w') as log:
                check=subprocess.run(checkcmd,stdout=log,stderr=subprocess.STDOUT,timeout=120)
            result['status']='complete_verified' if check.returncode==0 else 'verification_failed'
        else:result['status']='failed'
        return result
    # Fixed two chains avoid assigning the same physical CPU to concurrent jobs.
    def chain(items):
        results=[]
        for job in items:
            row=worker(job);results.append(row)
            with lock:
                state['jobs'].append(row);state['elapsed_seconds']=time.monotonic()-start;write(args.output/'queue.json',state)
        return results
    try:
        with ThreadPoolExecutor(max_workers=2) as pool:
            futures=[pool.submit(chain,[j for j in manifest['jobs'] if j['cpu']==cpu]) for cpu in sorted({j['cpu'] for j in manifest['jobs']})]
            for f in futures:f.result()
        state.update(status='stopped' if stop.is_set() else 'deadline' if time.monotonic()>=deadline else 'finished',finished_utc=datetime.now(timezone.utc).isoformat(),elapsed_seconds=time.monotonic()-start)
    except Exception as exc:state.update(status='supervisor_failed',error=repr(exc));raise
    finally:write(args.output/'queue.json',state)
if __name__=='__main__':main()
