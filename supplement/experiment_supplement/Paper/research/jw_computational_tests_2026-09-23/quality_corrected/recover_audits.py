#!/usr/bin/env python3
"""Explicitly recover the frozen audit queue after coordinator exit 143.
No objective/model/policy/source change or score-based retry. Keep all completed
validated jobs, validate complete orphaned witnesses, run every unstarted job.
The lost numerical process exit/wall times stay unknown, not fabricated as zero.
"""
import os
for k in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):
    os.environ[k]='1'
from pathlib import Path
import concurrent.futures, datetime, hashlib, json, queue, shutil, signal, subprocess, threading, time, traceback
import run_audits as original
HERE=Path(__file__).resolve().parent
OUT=HERE/'exhaustive_audits'
PYTHON=original.DEFAULT_PYTHON
read=original.read
atomic=original.atomic
sha=original.sha
require=original.require
utc=original.utc

def main():
    document=read(OUT/'AUDIT_QUEUE.json');bindings=read(OUT/'BINDINGS.json')
    previous=read(OUT/'STATUS.json');execution=read(OUT/'EXECUTION.json')
    require(previous['state']=='running','Recovery requires the interrupted running snapshot')
    require(sha(OUT/'BINDINGS.json')==document['bindings_sha256'],'Bindings changed')
    frozen=dict(document['frozen_files'],**document['source_sha256'])
    require(all(Path(p).is_file() and sha(p)==h for p,h in frozen.items()),'Frozen inputs or sources changed')
    recovery=OUT/'coordinator_recovery';recovery.mkdir(exist_ok=False)
    for name in ['STATUS.json','EXECUTION.json']:
        shutil.copy2(OUT/name,recovery/('before_'+name))
    completed={r['audit_id']:r for r in previous['results']}
    require(len(completed)==223 and all(r['status']=='complete_validated' for r in completed.values()),'Unexpected completed snapshot')
    for aid,record in completed.items():
        require(read(OUT/'tasks'/aid/'PROCESS.json')==record,'Completed task record mismatch')
    pending=[j for j in document['jobs'] if j['audit_id'] not in completed]
    orphaned=[];unstarted=[]
    for job in pending:
        aid=job['audit_id'];task=OUT/'tasks'/aid;target=OUT/'audits'/aid
        if task.exists():
            process=read(task/'PROCESS.json');result=read(target/'result.json')
            require(process['status']=='starting' and not (target/'validation.json').exists(),'Unexpected existing task state')
            require(result['status']=='complete' and result['complete'] and result['completed_target_count']==32768,'Orphaned worker is not complete')
            require(sha(target/'model.npz')==job['model_sha256'] and sha(target/'policy.npz')==job['representative_policy_sha256'],'Orphaned input binding changed')
            dst=recovery/'original_orphan_processes'/aid;dst.mkdir(parents=True)
            shutil.copy2(task/'PROCESS.json',dst/'PROCESS.json')
            orphaned.append(aid)
        else:
            require(not target.exists(),'Unstarted task has unexpected evidence')
            unstarted.append(aid)
    require(len(orphaned)==10 and len(unstarted)==67,'Unexpected recovery coverage')
    record={'started_utc':utc(),'coordinator_exit_observed':143,'cause':'Unknown; no causal attribution inferred from timing.',
        'scope':'Continue every unstarted frozen job and independently validate every complete orphaned worker. Preserve all finished audits. No reoptimization, audit selection or tolerance change.',
        'preserved_complete_jobs':len(completed),'orphaned_complete_worker_ids':orphaned,'unstarted_job_ids':unstarted,
        'source_sha256':{str(Path(__file__).resolve()):sha(__file__)},'queue_sha256':sha(OUT/'AUDIT_QUEUE.json'),
        'original_coordinator_source_sha256':document['source_sha256'][str(HERE/'run_audits.py')],
        'lost_telemetry':'For ten orphaned workers, process exit and process wall time are unknown. Their own elapsed time is retained separately; independent witness validation determines acceptance.',
        'cpus':list(range(10)),'pid':os.getpid()}
    atomic(recovery/'RECOVERY.json',record)
    cpus=original.cpu_allocation(0,10);pool=queue.Queue()
    for c in cpus:pool.put(c)
    active={};lock=threading.Lock();stop=threading.Event()
    initial_start=datetime.datetime.fromisoformat(execution['started_utc'])
    def status(state='running'):
        rows=list(completed.values())
        atomic(OUT/'STATUS.json',dict(state=state,updated_utc=utc(),elapsed_seconds=(datetime.datetime.now(datetime.timezone.utc)-initial_start).total_seconds(),
            total=len(document['jobs']),completed=len(rows),reused_complete=sum(r.get('reuse_attempt',{}).get('status')=='accepted' for r in rows),
            rejected_reuse_attempts=sum(r.get('reuse_attempt',{}).get('status')=='rejected_fresh_audit_required' for r in rows),
            successful_complete=sum(r['status']=='complete_validated' for r in rows),validated_partial=sum(r['status']=='partial_validated' for r in rows),
            failed=sum(r['status'] not in ['complete_validated','partial_validated'] for r in rows),expected_endpoint_count=bindings['expected_endpoint_count'],
            missing_endpoints=bindings['missing_endpoints'],invalid_endpoints=bindings['invalid_endpoints'],active=list(active.values()),results=rows,
            coordinator_recovery=str(recovery/'RECOVERY.json')))
    def process(cmd,log,hard,cpu,aid,phase):
        tick=time.perf_counter()
        with log.open('w') as stream:
            with lock:
                require(not stop.is_set(),'Recovery interrupted before launch')
                proc=subprocess.Popen(cmd,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
                active[aid]=dict(audit_id=aid,cpu=cpu,pid=proc.pid,phase=phase,started_utc=utc());status()
            timeout=False
            try:code=proc.wait(timeout=hard)
            except subprocess.TimeoutExpired:
                timeout=True
                try:os.killpg(proc.pid,signal.SIGKILL)
                except ProcessLookupError:pass
                code=proc.wait()
        return dict(command=cmd,exit=code,hard_timeout=timeout,wall_seconds=time.perf_counter()-tick,pid=proc.pid)
    def task(job):
        aid=job['audit_id'];cpu=pool.get();folder=OUT/'tasks'/aid;target=OUT/'audits'/aid
        r=read(folder/'PROCESS.json') if folder.exists() else dict(audit_id=aid,model=job['model'],cpu=cpu,started_utc=utc(),status='starting',audit_directory=str(target),binding_count=job['binding_count'])
        r['recovery_started_utc']=utc();r['recovery_cpu']=cpu
        try:
            require(sha(job['model_path'])==job['model_sha256'] and sha(job['representative_policy'])==job['representative_policy_sha256'],'Input changed before recovery task')
            if aid in orphaned:
                result=read(target/'result.json')
                r['numerical']=dict(exit=None,hard_timeout=None,wall_seconds=None,mode='recovered_complete_orphan_witnesses',
                    worker_elapsed_seconds=result['elapsed_seconds'],telemetry_scope='Original process exit/wall time lost with coordinator; acceptance requires complete saved witnesses and fresh independent validation.')
                r['recovered_complete_orphan']=True
            else:
                folder.mkdir();atomic(folder/'PROCESS.json',r)
                cmd=[PYTHON,str(HERE/'audit_worker.py'),'--model',job['model_path'],'--policy',job['representative_policy'],'--out',str(target),'--cpu',str(cpu),'--hard-seconds',str(execution['soft_audit_seconds'])]
                r['numerical']=process(cmd,folder/'audit.log',execution['hard_process_seconds'],cpu,aid,'numerical')
            atomic(folder/'PROCESS.json',r)
            cmd=[PYTHON,str(HERE/'validate_audits.py'),'--audit',str(target),'--cpu',str(cpu)]
            r['validation']=process(cmd,folder/'validation.log',execution['validation_hard_seconds'],cpu,aid,'validation')
            result=read(target/'result.json') if (target/'result.json').exists() else {}
            checked=read(target/'validation.json') if (target/'validation.json').exists() else {}
            valid=checked.get('status')=='passed' and r['validation']['exit']==0
            complete=valid and result.get('status')=='complete' and result.get('complete') is True and checked.get('complete') is True and checked.get('completed_target_count')==32768
            r.update(status='complete_validated' if complete else 'partial_validated' if valid else 'failed',audit_status=result.get('status'),
                completed_target_count=result.get('completed_target_count',0),audit_lower=checked.get('audit_lower') if valid else None,audit_upper=checked.get('audit_upper') if valid else None)
        except BaseException as error:
            r.update(status='failed',error=repr(error),traceback=traceback.format_exc())
        finally:
            r['finished_utc']=utc();atomic(folder/'PROCESS.json',r)
            with lock:active.pop(aid,None)
            pool.put(cpu)
        return r
    def interrupt(signum,frame):
        stop.set()
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM,interrupt)
    interrupted=False
    try:
        with concurrent.futures.ThreadPoolExecutor(max_workers=10) as executor:
            futures=[executor.submit(task,j) for j in pending]
            for future in concurrent.futures.as_completed(futures):
                result=future.result()
                with lock:completed[result['audit_id']]=result;status()
                print(json.dumps({'audit_id':result['audit_id'],'status':result['status'],'completed':len(completed)}),flush=True)
    except KeyboardInterrupt:
        interrupted=True;stop.set()
    changes=[p for p,h in frozen.items() if not Path(p).is_file() or sha(p)!=h]
    changes += [p for p,h in record['source_sha256'].items() if sha(p)!=h]
    atomic(OUT/'FINAL_INPUT_CHECK.json',dict(status='passed' if not changes else 'changed',changed_paths=changes,
        changed_sources=[p for p in changes if p in document['source_sha256'] or p in record['source_sha256']],checked_files=len(frozen)+1,
        recovery_source_sha256=record['source_sha256']))
    state='interrupted' if interrupted else 'finished_with_input_changes' if changes else 'finished'
    with lock:status(state)
    record.update(finished_utc=utc(),state=state,completed=len(completed),preserved_orphan_worker_elapsed_seconds=sum(read(OUT/'audits'/a/'result.json')['elapsed_seconds'] for a in orphaned))
    atomic(recovery/'RECOVERY.json',record)
    return 0 if state=='finished' and len(completed)==300 and all(r['status'] in ['complete_validated','partial_validated'] for r in completed.values()) else 2
if __name__=='__main__':raise SystemExit(main())
