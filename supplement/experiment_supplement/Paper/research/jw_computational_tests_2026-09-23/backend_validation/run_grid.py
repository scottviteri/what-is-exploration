#!/usr/bin/env python3
"""Four pinned serial workers; no frozen sources or historic outcomes are changed."""
import concurrent.futures,hashlib,json,os,subprocess,time
from pathlib import Path
HERE=Path(__file__).resolve().parent;PY='/tmp/exploration-lp-cpu-venv/bin/python';QUEUE=HERE/'QUEUE.json'
def write(p,data):
 tmp=p.with_suffix('.tmp');tmp.write_text(json.dumps(data,indent=2)+'\n');tmp.replace(p)
def batch(phase,slot,cells):
 out=[];cpu=4+slot
 for index,cell in cells:
  methods=[m for m in cell['methods'] if (m.startswith('bridge_') and m!='bridge_cold')==(phase=='extensions')]
  for method in methods:
   dest=HERE/'runs'/f"case_{index:03d}"/method;dest.mkdir(parents=True,exist_ok=True);started=time.perf_counter()
   cmd=[PY,str(HERE/'worker.py'),'--queue',str(QUEUE),'--index',str(index),'--method',method,'--output',str(dest),'--cpu',str(cpu)]
   with (dest/'process.log').open('w') as log:
    try:r=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,timeout=240,env=os.environ|{'PYTHONDONTWRITEBYTECODE':'1'});code=r.returncode
    except subprocess.TimeoutExpired:code=124
   record={'index':index,'case':cell['case'],'repeat':cell['repeat'],'kind':cell['kind'],'method':method,'cpu':cpu,'exit_code':code,'wall_seconds':time.perf_counter()-started}
   write(dest/'PROCESS.json',record);out.append(record);write(HERE/f'progress_{phase}_{slot}.json',out)
   print(phase,index,method,code,round(record['wall_seconds'],2),flush=True)
 return out
if __name__=='__main__':
 q=json.loads(QUEUE.read_text())
 for name,expected in q['source_hashes'].items():
  if hashlib.sha256((HERE/name).read_bytes()).hexdigest()!=expected:raise SystemExit('Frozen code mismatch:'+name)
 start=time.perf_counter();records=[]
 for phase in ['core','extensions']:
  with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
   fs=[pool.submit(batch,phase,s,[(i,c) for i,c in enumerate(q['cells']) if i%4==s]) for s in range(4)]
   for f in fs:records.extend(f.result())
  write(HERE/'RUN_STATUS.json',{'phase_completed':phase,'seconds':time.perf_counter()-start,'processes':records})
 write(HERE/'RUN_COMPLETE.json',{'status':'finished','seconds':time.perf_counter()-start,'processes':records})
