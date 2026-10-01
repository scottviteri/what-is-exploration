"""Bounded subprocess queue: pinned source, resume checks, memory/time limits."""
import argparse
from concurrent.futures import ThreadPoolExecutor,as_completed
from datetime import datetime,timezone
import hashlib
import json
import os
from pathlib import Path
import queue
import shutil
import signal
import subprocess
import sys
import threading
import time

HERE=Path(__file__).resolve().parent


def write(path,data):
    tmp=path.with_suffix('.tmp');tmp.write_text(json.dumps(data,indent=2,allow_nan=False)+'\n');tmp.replace(path)


def digest(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def run():
    parser=argparse.ArgumentParser();parser.add_argument('manifest',type=Path)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--hours',type=float,default=1)
    args=parser.parse_args();manifest=json.loads(args.manifest.read_text());manifest_hash=digest(args.manifest)
    args.output=args.output.resolve();args.output.mkdir(parents=True,exist_ok=True)
    bindings=manifest.get('source_sha256',{})
    def sources_match():return all((HERE/name).exists() and digest(HERE/name)==expected for name,expected in bindings.items())
    if not sources_match():raise SystemExit('Refusing changed source bindings')
    previous_queue=args.output/'queue.json'
    if previous_queue.exists():
        prior=json.loads(previous_queue.read_text())
        if prior['manifest_sha256']!=manifest_hash:raise SystemExit('Refusing a different manifest in an existing output directory')
    lock=args.output/'queue.lock'
    try:fd=os.open(lock,os.O_CREAT|os.O_EXCL|os.O_WRONLY)
    except FileExistsError:raise SystemExit('Existing queue lock; inspect its process before resuming')
    os.write(fd,str(os.getpid()).encode());os.close(fd)
    started=time.monotonic();deadline=started+min(args.hours,manifest.get('hours_limit',args.hours))*3600
    summary=dict(status='running',started_utc=datetime.now(timezone.utc).isoformat(),pid=os.getpid(),
                 manifest_sha256=manifest_hash,manifest_path=str(args.manifest.resolve()),
                 registered_jobs=len(manifest['jobs']),executable=sys.executable,workers=manifest['workers'],
                 hours_limit=(deadline-started)/3600,jobs=[])
    write(args.output/'queue.json',summary)
    snapshots=args.output/'source';snapshots.mkdir(exist_ok=True)
    for name,expected in bindings.items():
        (snapshots/(expected+'_'+Path(name).name)).write_bytes((HERE/name).read_bytes())
    affinity=sorted(os.sched_getaffinity(0));slots=queue.Queue()
    for cpu in affinity[:manifest['workers']]:slots.put(cpu)
    env=os.environ|{key:'1' for key in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']}
    stop=threading.Event();active={};active_lock=threading.Lock();gpu_slot=threading.Semaphore(1)
    def terminate(process):
        if process.poll() is not None:return
        try:os.killpg(process.pid,signal.SIGTERM)
        except ProcessLookupError:return
        try:process.wait(timeout=3)
        except subprocess.TimeoutExpired:
            try:os.killpg(process.pid,signal.SIGKILL)
            except ProcessLookupError:pass
            process.wait()
    def interrupted(signum,frame):stop.set()
    signal.signal(signal.SIGTERM,interrupted);signal.signal(signal.SIGINT,interrupted)
    def disk_used():
        total=0
        for path in args.output.rglob('*'):
            try:
                if path.is_file():total+=path.stat().st_size
            except FileNotFoundError:pass
        return total
    def worker(job):
        folder=args.output/job['id']
        job_hash=hashlib.sha256(json.dumps(job,sort_keys=True).encode()).hexdigest()
        previous=folder/'result.json'
        if previous.exists():
            old=json.loads(previous.read_text())
            if old.get('status')=='complete' and old.get('manifest_sha256')==manifest_hash and old.get('job_sha256')==job_hash:
                return dict(id=job['id'],status='reused_complete')
            folder.rename(args.output/(job['id']+f'_previous_{time.time_ns()}'))
        if time.monotonic()>=deadline:return dict(id=job['id'],status='skipped_deadline')
        if stop.is_set() or (args.output/'STOP').exists():return dict(id=job['id'],status='skipped_stop')
        if not sources_match():stop.set();return dict(id=job['id'],status='skipped_changed_source')
        if shutil.disk_usage(HERE).free<15*1024**3 or disk_used()>manifest.get('max_output_gib',12)*1024**3:
            stop.set();return dict(id=job['id'],status='skipped_disk_reserve')
        folder.mkdir(exist_ok=True);is_gpu=job.get('executor')=='gpu'
        if is_gpu:gpu_slot.acquire()
        cpu=slots.get()
        metadata=dict(id=job['id'],started_utc=datetime.now(timezone.utc).isoformat(),cpu=cpu,job_sha256=job_hash)
        ts=time.monotonic()
        try:
            if stop.is_set() or (args.output/'STOP').exists():return dict(id=job['id'],status='skipped_stop')
            if time.monotonic()>=deadline:return dict(id=job['id'],status='skipped_deadline')
            if not sources_match():stop.set();return dict(id=job['id'],status='skipped_changed_source')
            executable=manifest.get('gpu_executable',sys.executable) if is_gpu else sys.executable
            prefix=[] if is_gpu else ['prlimit',f"--as={int(manifest['max_memory_gib_per_worker']*1024**3)}",'--']
            command=prefix+['taskset','-c',str(cpu),executable,str(HERE/'scale_one.py'),'--output',str(folder),
                            '--solve-limit',str(manifest['per_solve_seconds'])]
            metadata['executor']='gpu' if is_gpu else 'cpu'
            metadata['memory_limit_mode']='sampled_RSS' if is_gpu else 'address_space_and_sampled_RSS'
            for key,value in job.items():
                if key not in ['id','executor','wall_seconds']:command.extend(['--'+key.replace('_','-'),str(value)])
            wall_limit=min(job.get('wall_seconds',manifest['per_job_seconds']),max(1,deadline-time.monotonic()))
            metadata.update(command=command,wall_limit=wall_limit)
            child_env=env|{'SCALING_MANIFEST_SHA256':manifest_hash,'SCALING_JOB_SHA256':job_hash,
                           'SCALING_GPU_ARTIFACT_ROOT':str(folder/'gpu_attempts')}
            with (folder/'process.log').open('a') as stream:
                process=subprocess.Popen(command,stdout=stream,stderr=subprocess.STDOUT,env=child_env,start_new_session=True)
                with active_lock:active[process.pid]=process
                metadata['pid']=process.pid;write(folder/'process.json',metadata)
                peak_rss=0;reason=None
                while process.poll() is None:
                    if stop.is_set() or (args.output/'STOP').exists():reason='stopped';stop.set();break
                    if time.monotonic()-ts>=wall_limit or time.monotonic()>=deadline:reason='timeout';break
                    try:
                        lines=Path(f'/proc/{process.pid}/status').read_text().splitlines()
                        peak_rss=max(peak_rss,max([int(line.split()[1]) for line in lines if line.startswith('VmRSS:')],default=0))
                    except FileNotFoundError:pass
                    if peak_rss>manifest['max_memory_gib_per_worker']*1024**2:reason='memory_limit';break
                    if shutil.disk_usage(HERE).free<15*1024**3:reason='disk_reserve';stop.set();break
                    stop.wait(.5)
                if reason:terminate(process)
                code=process.wait()
                with active_lock:active.pop(process.pid,None)
                metadata.update(exit_code=code,status=reason or ('complete' if code==0 else 'failed_process'),
                                sampled_peak_rss_kib=peak_rss)
            if previous.exists():
                cell=json.loads(previous.read_text())
                if cell.get('status')=='running':
                    cell.update(status='execution_incomplete',supervisor_status=metadata['status'])
                    write(previous,cell)
                metadata['cell_status']=cell.get('status')
            metadata['seconds']=time.monotonic()-ts;write(folder/'process.json',metadata)
            return metadata
        finally:
            slots.put(cpu)
            if is_gpu:gpu_slot.release()
    def update_report(job_id):
        if not (HERE/'report_scaling.py').exists():return
        try:
            subprocess.run([sys.executable,str(HERE/'report_scaling.py'),str(args.output)],env=env,
                           stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,timeout=30,check=True)
        except Exception as exc:
            summary.setdefault('report_failures',[]).append(dict(job=job_id,error=repr(exc)))
            write(args.output/'queue.json',summary)
    try:
        with ThreadPoolExecutor(max_workers=max(1,manifest['workers']-1)) as cpu_pool, ThreadPoolExecutor(max_workers=1) as gpu_pool:
            try:
                futures={(gpu_pool if job.get('executor')=='gpu' else cpu_pool).submit(worker,job):job for job in manifest['jobs']}
                last_report=0.
                for future in as_completed(futures):
                    job=futures[future]
                    try:row=future.result()
                    except Exception as exc:row=dict(id=job['id'],status='supervisor_error',error=repr(exc))
                    summary['jobs'].append(row);summary['elapsed_seconds']=time.monotonic()-started
                    summary['updated_utc']=datetime.now(timezone.utc).isoformat()
                    write(args.output/'queue.json',summary)
                    print(row['id'],row['status'],round(row.get('seconds',0),2),'seconds',flush=True)
                    now=time.monotonic()
                    if not stop.is_set() and now<deadline and now-last_report>=60:
                        update_report(job['id']);last_report=now
            except BaseException:
                stop.set()
                raise
        exhausted=time.monotonic()>=deadline
        summary.update(status='stopped' if stop.is_set() else ('deadline' if exhausted else 'finished'),
                       elapsed_seconds=time.monotonic()-started,
                       finished_utc=datetime.now(timezone.utc).isoformat())
        write(args.output/'queue.json',summary)
        update_report('final')
    finally:
        stop.set()
        with active_lock:processes=list(active.values())
        for process in processes:terminate(process)
        lock.unlink(missing_ok=True)


if __name__=='__main__':run()
