"""Apply a recorded CPU-affinity override without changing a frozen live queue.

The existing supervisor supplies per-job taskset commands from its loaded manifest.
This lightweight watcher repins its children after those commands execute. It may
allow a brief startup interval before the next 0.1-second scan; it is not a cgroup
capacity reservation and does not change any numerical or timeout setting.
"""
from pathlib import Path
import argparse,json,os,time
from datetime import datetime,timezone

ROOT=Path(__file__).resolve().parent

def now():return datetime.now(timezone.utc).isoformat()
def write(path,value):
    tmp=path.with_suffix(path.suffix+'.tmp');tmp.write_text(json.dumps(value,indent=2)+'\n');tmp.replace(path)
def ident(pid):
    try:
        fields=Path(f'/proc/{pid}/stat').read_text().rsplit(')',1)[1].split()
        return int(fields[19]) if fields[0]!='Z' else None
    except (FileNotFoundError,ProcessLookupError):return None

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--record',type=Path,required=True);args=parser.parse_args()
    record=json.loads(args.record.read_text());parent=next(x for x in record['owned_processes'] if Path(x['script']).name=='run_extension_queue.py')
    parent_pid=parent['pid'];parent_start=parent['start_ticks'];allowed={10,11}
    manifest=json.loads((ROOT/'near_optimal_manifest.json').read_text())
    cpu_by_cell={j['cell']:{10 if j['cpu']==3 else 11} for j in manifest['jobs']}
    os.sched_setaffinity(0,allowed)
    state={'status':'running','pid':os.getpid(),'started_utc':now(),'parent_pid':parent_pid,'parent_start_ticks':parent_start,'override_record':str(args.record.resolve()),'poll_seconds':.1,'cpu_mapping':{'3':10,'4':11},'cgroup_cpu_capacity':10.2,'requested_cpu_equivalents':2,'scope':'Affinity-only runtime override. Frozen manifest and numerical sources unchanged; both campaigns share the global cgroup quota.','changes':0}
    status=ROOT/'CPU_AFFINITY_GUARD.json';events=ROOT/'CPU_AFFINITY_EVENTS.jsonl';write(status,state);last_write=0.
    try:
        while ident(parent_pid)==parent_start:
            pending=[parent_pid];seen=set();live=[]
            while pending:
                pid=pending.pop()
                if pid in seen:continue
                seen.add(pid);proc=Path(f'/proc/{pid}')
                try:
                    cmd=[v.decode() for v in (proc/'cmdline').read_bytes().split(b'\0') if v]
                    tasks=list((proc/'task').iterdir())
                    for task in tasks:
                        pending.extend(int(v) for v in (task/'children').read_text().split())
                    target=allowed;cell=None
                    if str(ROOT/'recover_saved.py') in cmd and '--cell' in cmd:
                        cell=cmd[cmd.index('--cell')+1];target=cpu_by_cell[cell]
                    elif str(ROOT/'check_recovery.py') in cmd:
                        for arg in cmd:
                            if Path(arg).name in cpu_by_cell:cell=Path(arg).name;target=cpu_by_cell[cell]
                    # This process is the verified supervisor or its live child.
                    # No process found via a broad name match is modified.
                    for task in tasks:
                        try:
                            tid=int(task.name);before=os.sched_getaffinity(tid)
                            if before!=target:
                                os.sched_setaffinity(tid,target);after=os.sched_getaffinity(tid)
                                event={'utc':now(),'pid':pid,'tid':tid,'cell':cell,'before':sorted(before),'after':sorted(after)}
                                with events.open('a') as f:f.write(json.dumps(event)+'\n')
                                state['changes']+=1
                                if after!=target:raise RuntimeError('Affinity override did not apply')
                        except (FileNotFoundError,ProcessLookupError):pass
                    live.append({'pid':pid,'cell':cell,'target_cpus':sorted(target)})
                except (FileNotFoundError,ProcessLookupError):pass
            if time.monotonic()-last_write>=5:
                state.update(updated_utc=now(),live_processes=live);write(status,state);last_write=time.monotonic()
            time.sleep(.1)
        state.update(status='finished',finished_utc=now(),reason='Original queue supervisor exited; no PID reuse followed.')
    except Exception as exc:
        state.update(status='failed',error=repr(exc),finished_utc=now());raise
    finally:write(status,state)
if __name__=='__main__':main()
