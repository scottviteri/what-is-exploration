"""One archived design full audit, four fixed ranges; no GPU or optimization."""
import os
for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'):os.environ[key]='1'
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json,time,hashlib,multiprocessing as mp
import numpy as np
HERE=Path(__file__).resolve().parent
SOURCE=HERE.parents[1]/'target_selection_2026-09-23'
sys.path.insert(0,str(SOURCE))
import scaling_core as core
from certified_decoder import StableDecoder

def worker(k,start,stop,deadline):
    os.sched_setaffinity(0,{20+k});folder=HERE/'cpu_full_chunks';folder.mkdir(exist_ok=True)
    model=core.random_model(2026096900,worlds=4);E=core.geometry(model['T'],model['Z'],3).raw/8
    targets=core.Targets(model['T'],model['Z'],4);dec=StableDecoder(E,16);rows=[];tick=time.perf_counter();records=[];failures=[]
    for first in range(start,stop,256):
      if time.time()>deadline:break
      gs=[];aa=[];bb=[];ff=[];idx=[]
      try:
       for j in range(first,min(first+256,stop)):
        F=targets.get(j)['kernel'];r,w=dec.solve(F);G=w['decoder'];alpha=w['alpha'];b=w['b'];source=E[:,w['source_indices']]
        residual=max(float(abs(G.sum(1)-1).max()),float(max(0,-G.min())),float(abs(alpha.sum()-1)),float(max(0,-alpha.min())),float(max(0,-b.min())),float(np.maximum(b-alpha[:,None],0).max()))
        upper=float(np.abs(source@G-F).sum(1).max()/2);lower=float((F*b).sum()-np.max(source.T@b,axis=1).sum())
        if not np.isfinite([upper,lower,residual]).all() or residual>1e-12 or lower>upper+1e-10 or upper-lower>2e-7:raise RuntimeError(f'Original-source certificate failure {j}: {lower},{upper},{residual}')
        rows.append(dict(target=j,lower=lower,upper=upper,gap=upper-lower,feasibility=residual));gs.append(G);aa.append(alpha);bb.append(b);ff.append(F);idx.append(j)
       path=folder/f'{first:05d}.npz';np.savez_compressed(path,E=E,source_indices=w['source_indices'],targets=idx,F=ff,G=gs,alpha=aa,b=bb)
       records.append(dict(file=str(path.relative_to(HERE)),sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
      except Exception as e:failures.append(dict(first=first,error=repr(e)));break
    result=dict(worker=k,range=[start,stop],count=len(rows),seconds=time.perf_counter()-tick,rows=rows,witness_chunks=records,failures=failures)
    (folder/f'worker{k}.json').write_text(json.dumps(result,indent=2)+'\n')
    print('WORKER_DONE',k,len(rows),result['seconds'],flush=True)

def main():
    started=time.time();protocol=dict(seed=2026096900,worlds=4,states=3,concentration=1.,t=3,n=4,collector='uniform independent actions',targets='all32768 deterministic observation-adaptive binary depth4 trees',workers=4,affinity=[20,21,22,23],hard_wall_cap_seconds=180,per_target_numerical_tolerance=2e-7,scientific_scope='One complete finite design audit for throughput; no objective comparison',source_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),SOURCE/'scaling_core.py',SOURCE/'certified_decoder.py',SOURCE/'fast_decoder.py']})
    (HERE/'CPU_FULL_PROTOCOL.json').write_text(json.dumps(protocol,indent=2)+'\n')
    children=[];deadline=started+175
    for k in range(4):
      p=mp.Process(target=worker,args=(k,8192*k,8192*(k+1),deadline));p.start();children.append(p)
    for p in children:
      p.join(max(0,started+180-time.time()))
      if p.is_alive():p.terminate();p.join()
    summaries=[]
    for k,p in enumerate(children):
      path=HERE/'cpu_full_chunks'/f'worker{k}.json'
      summaries.append(json.loads(path.read_text()) if path.exists() else dict(worker=k,status='interrupted_at_cap',count=0,rows=[],witness_chunks=[],exitcode=p.exitcode))
    rows=[r for s in summaries for r in s['rows']];ids=[r['target'] for r in rows]
    out=dict(status='complete' if sorted(ids)==list(range(32768)) else 'partial',count=len(rows),wall_seconds=time.time()-started,worker_seconds=[s.get('seconds') for s in summaries],max_bracket=max((r['gap'] for r in rows),default=None),max_feasibility=max((r['feasibility'] for r in rows),default=None),audit_lower=max((r['lower'] for r in rows),default=None),audit_upper=max((r['upper'] for r in rows),default=None),scope='Finite complete n4 audit only if status complete. A partial maximum lower is a witness; partial upper is not a global audit upper.',workers=[{k:v for k,v in s.items() if k!='rows'} for s in summaries])
    (HERE/'CPU_FULL_RESULTS.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='workers'},indent=2))
if __name__=='__main__':main()
