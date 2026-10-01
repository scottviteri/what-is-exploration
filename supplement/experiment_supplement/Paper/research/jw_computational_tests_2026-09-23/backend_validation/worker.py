#!/usr/bin/env python3
"""One isolated timing process. A watchdog enforces a 65s cap per solve."""
import os
for k in ['OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:os.environ[k]='1'
import argparse,copy,json,resource,sys,threading,time
from fractions import Fraction as F
from pathlib import Path
import backend_api as api
from adaptive_weights import CutCache,Cut,digest
from frozen_adapter import numeric_q

def main():
 p=argparse.ArgumentParser();p.add_argument('--queue',type=Path,required=True);p.add_argument('--index',type=int,required=True);p.add_argument('--method',required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--cpu',type=int,required=True);a=p.parse_args()
 os.sched_setaffinity(0,{a.cpu});resource.setrlimit(resource.RLIMIT_AS,(4*1024**3,4*1024**3));a.output.mkdir(parents=True,exist_ok=True)
 spec=json.loads(a.queue.read_text())['cells'][a.index];backend=api.bootstrap();np=backend.np
 modelpath=api.ROOT/spec['model_path'];model=dict(np.load(modelpath));start=time.perf_counter();g=backend.core.geometry(model['T'],model['Z'],spec['t']);pool=backend.core.Targets(model['T'],model['Z'],spec['n']);targets=[pool.get(i)|{'id':str(i)} for i in spec['target_indices']];build=time.perf_counter()-start
 labels=list(range(len(model['T'])));ctx=api.context(backend,g,api.sha(modelpath),labels);bindings=api.bindings_for(targets);K=len(targets)
 cache=CutCache(ctx);witness_store={};uniform=[F(1,K)]*K
 sequences={'monolithic':[('uniform',uniform)],'decomposition':[('uniform',uniform)],'bridge_cold':[('uniform',uniform)],
  'bridge_increasing':[('uniform_initial',uniform),('increasing',[F(i+1,K*(K+1)//2) for i in range(K)]),('uniform_final',uniform)],
  'bridge_decreasing':[('uniform_initial',uniform),('decreasing',[F(K-i,K*(K+1)//2) for i in range(K)]),('uniform_final',uniform)]}
 records=[]
 for stage,weights in sequences[a.method]:
  folder=a.output/stage;folder.mkdir(parents=True,exist_ok=True)
  metadata={**spec,'weights':[str(w) for w in weights],'target_binding_ids':[b.identity for b in bindings],'method':a.method,'stage':stage,'geometry_target_seconds':build,
   'initial_cache_sha256':digest(cache.manifest()),'cpu':a.cpu,'python':sys.version,'numpy':np.__version__,'scipy':backend.scipy.__version__,'highs':backend.highspy.Highs().version(),
   'solve_cap_seconds':40,'hard_process_cap_seconds':65,'gap':1e-6,'timing_scope':'solve+replay+selected decoders+cache verification; shared geometry separate; export and independent audit separate'}
  for t,w in zip(targets,weights):t['weight']=float(w)
  objective=api.objective_for(ctx,targets,weights);metadata['objective_id']=objective.identity
  api.write(folder/'metadata.json',metadata);api.write(folder/'started.json',{'time':time.time()})
  def kill():
   api.write(folder/'HARD_TIMEOUT.json',{'status':'hard_process_timeout','seconds':65});os._exit(124)
  timer=threading.Timer(65,kill);timer.daemon=True;timer.start();beg=time.perf_counter();result=None
  try:
   if a.method.startswith('bridge'):
    result=api.solve(backend,g,targets,objective,cache,model_sha=api.sha(modelpath),labels=labels,witness_store=witness_store)
    witness_store=result['witness_store']
   elif a.method=='decomposition':
    evidence=[];original_master=backend.master;original_oracle=backend.oracle
    def master(*args,**kwargs):
     v=original_master(*args,**kwargs);evidence.append(dict(master_arrays=v[5],cut_prefix=copy.deepcopy(args[3]),E=v[0],rows=v[1],oracle=None));return v
    def oracle(*args,**kwargs):
     v=original_oracle(*args,**kwargs);evidence[-1]['oracle']=v;evidence[-1]['available_seconds']=time.perf_counter()-beg;return v
    backend.master=master;backend.oracle=oracle
    try:best,report,cuts,arrays=backend.decomposed_plan(g,targets,spec['kind'],time_limit=40,gap=1e-6)
    finally:backend.master=original_master;backend.oracle=original_oracle
    for ev in evidence:
     if ev.get('oracle'):
      for c in ev['oracle']['cuts']:
       w={'alpha':c['alpha'].tolist(),'b':c['b'].tolist()};key=digest(w);witness_store[key]=w;b=bindings[c['target']]
       cache.add(b,Cut(ctx.identity,b.identity,numeric_q(c['intercept']),tuple(numeric_q(v) for v in c['slope']),key,'frozen original decomposition numerical witness'))
    result={'status':report['status'],'report':report,'best':best,'evidence_to_export':evidence,'cache':cache.manifest(),'witness_store':witness_store,'seconds':time.perf_counter()-beg}
   else:
    # Isolate export time while preserving the original exact monolithic formulation.
    exports=[];orig=np.savez_compressed
    def save(*args,**kwargs):
     ts=time.perf_counter()
     try:return orig(*args,**kwargs)
     finally:exports.append(time.perf_counter()-ts)
    np.savez_compressed=save
    try:E,rows,leaf,report=backend.core.native_plan(g,targets,spec['kind'],time_limit=40,certificate_path=folder/'monolithic_certificate.npz')
    finally:np.savez_compressed=orig
    ev=backend.oracle(g,E,rows,targets,beg+60)
    upper=backend.aggregate(ev['upper'],targets,spec['kind']);gap=upper-report['dual']
    status='passed' if -2e-7<=gap<=1e-6 else 'failed_gap'
    result={'status':status,'report':report,'best':dict(E=E,rows=rows,leaf=leaf,evaluated=ev),'seconds':time.perf_counter()-beg-sum(exports),'internal_export_seconds':sum(exports),'gap':gap,'evidence_to_export':[]}
  except Exception as exc:result={'status':'failed','error':repr(exc),'seconds':time.perf_counter()-beg,'best':None,'evidence_to_export':[]}
  finally:timer.cancel()
  metadata['selection_provenance']={'weight_sequence':a.method,'stage':stage,'repeat':spec['repeat'],'prior_cache_creation_seconds':sum(x.get('seconds',0) for x in records)}
  light=api.export(backend,folder,g,targets,model,metadata,result)
  if (folder/'monolithic_certificate.npz').exists() and result.get('best') is None:
   # Failed post-planning decode remains a failure, with the saved primal/dual intact.
   pass
  from independent_audit import audit
  auditstart=time.perf_counter()
  try:checked=audit(folder)
  except Exception as exc:checked={'status':'failed','error':repr(exc)}
  checked['seconds']=time.perf_counter()-auditstart;api.write(folder/'audit.json',checked)
  records.append(light|{'stage':stage,'audit':checked});api.write(a.output/'SUMMARY.json',records)
  print(spec['case'],spec['t'],spec['K'],spec['repeat'],a.method,stage,result['status'],checked['status'],round(result['seconds'],3),flush=True)
 api.write(a.output/'DONE.json',{'status':'finished','records':len(records),'rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss})
if __name__=='__main__':main()
