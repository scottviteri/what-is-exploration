#!/usr/bin/env python3
"""Execute the frozen model/method queue; no source edits or silent retries."""
from pathlib import Path
import argparse,concurrent.futures,datetime,hashlib,json,os,queue,random,resource,subprocess,sys,time
HERE=Path(__file__).resolve().parent
PYTHON='/tmp/exploration-lp-cpu-venv/bin/python'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def atomic(p,v):
 t=p.with_suffix('.tmp');t.write_text(json.dumps(v,indent=2)+'\n');t.replace(p)
def main():
 parser=argparse.ArgumentParser();parser.add_argument('--prepare',action='store_true');parser.add_argument('--workers',type=int,default=12);args=parser.parse_args();q=json.loads((HERE/'QUEUE.json').read_text())
 if args.prepare:
  import planner
  dest=HERE/'models';dest.mkdir(exist_ok=True);inventory=[]
  for m in q['models']:
   path=dest/(m['id']+'.npz')
   if path.exists():raise RuntimeError('Refusing model overwrite')
   model=planner.core.random_model(m['seed'],worlds=m['worlds'],states=m['states'],concentration=m['concentration'])
   planner.np.savez_compressed(path,T=model['T'],Z=model['Z']);inventory.append(dict(m,path=str(path.relative_to(HERE)),sha256=sha(path)))
  atomic(HERE/'MODELS.json',{'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'models':inventory});return
 lock=json.loads((HERE/'SOURCE_LOCK.json').read_text())
 for name,digest in lock['files'].items():
  if sha(HERE/name)!=digest:raise RuntimeError('Source changed since freeze: '+name)
 models=json.loads((HERE/'MODELS.json').read_text())['models'];jobs=[(m,arm) for m in models for arm in q['arms']];random.Random(926201).shuffle(jobs)
 atomic(HERE/'EXECUTION_QUEUE.json',{'jobs':[{'model':m['id'],'arm':a} for m,a in jobs],'workers':args.workers,'cpus':list(range(24,24+args.workers)),'hard_process_seconds':120,'address_space_gib':4,'source_lock_sha256':sha(HERE/'SOURCE_LOCK.json'),'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()})
 cpus=queue.Queue()
 for cpu in range(24,24+args.workers):cpus.put(cpu)
 def task(job):
  model,arm=job;cpu=cpus.get();out=HERE/'runs'/model['id']/arm;out.mkdir(parents=True,exist_ok=False);start=time.perf_counter();mp=HERE/model['path']
  if sha(mp)!=model['sha256']:raise RuntimeError('Model changed')
  cmd=[PYTHON,str(HERE/'planner.py'),'--model',str(mp),'--out',str(out),'--arm',arm,'--cpu',str(cpu),'--seconds','40']
  # preexec_fn is avoided in this threaded parent; child shell sets ulimit.
  env=dict(os.environ,OMP_NUM_THREADS='1',OPENBLAS_NUM_THREADS='1',MKL_NUM_THREADS='1',NUMEXPR_NUM_THREADS='1')
  with (out/'process.log').open('w') as log:
   try:
    proc=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,env=env,start_new_session=True)
    try:code=proc.wait(timeout=120);error=None
    except subprocess.TimeoutExpired:
     import signal;os.killpg(proc.pid,signal.SIGKILL);proc.wait();code=-9;error='hard_process_timeout'
   except Exception as e:code=None;error=repr(e)
  record=dict(model=model['id'],arm=arm,cpu=cpu,exit=code,error=error,wall_seconds=time.perf_counter()-start,command=cmd)
  atomic(out/'PROCESS.json',record);cpus.put(cpu);print(json.dumps(record),flush=True);return record
 results=[]
 with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as ex:
  for result in ex.map(task,jobs):results.append(result);atomic(HERE/'PLANNING_STATUS.json',{'completed_processes':len(results),'total':len(jobs),'results':results,'state':'running'})
 atomic(HERE/'PLANNING_STATUS.json',{'completed_processes':len(results),'total':len(jobs),'results':results,'state':'finished'})
if __name__=='__main__':main()
