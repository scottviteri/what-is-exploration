#!/usr/bin/env python3
"""Analytic read-bit model and cache corruption/ordering numerical tests."""
import os
for k in ['OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:os.environ[k]='1'
import copy,json,time
from pathlib import Path
from fractions import Fraction as F
import backend_api as api
from adaptive_weights import CutCache,Objective,digest

def main():
 # bootstrap must precede numerical imports; independent audit imported above
 # would import numpy too early, so move audit import after bootstrap below.
 pass
if __name__=='__main__':
 backend=api.bootstrap();np=backend.np
 from independent_audit import audit
 model={'T':np.ones((2,2,1,1)),'Z':np.array([[[[1.,0.]],[[1.,0.]]],[[[0.,1.]],[[1.,0.]]]])}
 g=backend.core.geometry(model['T'],model['Z'],2);pool=backend.core.Targets(model['T'],model['Z'],1)
 targets=[pool.get(j)|{'id':str(j)} for j in range(2)];modelsha=digest({'analytic':'read hidden fair bit or silence'});labels=[0,1];ctx=api.context(backend,g,modelsha,labels);cache=CutCache(ctx);store={};checks=[]
 for label,order,weights in [('uniform',[0,1],[F(1,2)]*2),('zero',[0,1],[F(0),F(1)]),('tiny',[0,1],[F(1,10**12),1-F(1,10**12)]),('reordered',[1,0],[F(1,2)]*2)]:
  ts=[targets[j] for j in order];objective=api.objective_for(ctx,ts,weights)
  result=api.solve(backend,g,ts,objective,cache,model_sha=modelsha,labels=labels,seconds=10,witness_store=store);store=result['witness_store']
  metadata={'t':2,'n':1,'target_indices':order,'weights':[str(w) for w in weights],'kind':'native_weighted','target_binding_ids':[b.identity for b in api.bindings_for(ts)]}
  dest=api.HERE/'tiny'/label;api.export(backend,dest,g,ts,model,metadata,result);checked=audit(dest);api.write(dest/'audit.json',checked)
  assert result['status']=='converged_numerically';assert checked['upper']<=1e-6
  checks.append({'test':label,'status':'passed','audit':checked})
 for label,bad in [('missing',{}),('corrupt',copy.deepcopy(store))]:
  if label=='corrupt':bad[next(iter(bad))]['alpha'][0]+=.1
  try:api.solve(backend,g,targets,api.objective_for(ctx,targets,[F(1,2)]*2),cache,model_sha=modelsha,labels=labels,seconds=10,witness_store=bad)
  except ValueError:checks.append({'test':label+'_witness_rejected','status':'passed'})
  else:raise AssertionError('Invalid cache accepted')
 try:api.objective_for(ctx,[targets[0],targets[0]],[F(1,2)]*2)
 except ValueError:checks.append({'test':'duplicate_target_rejected','status':'passed'})
 else:raise AssertionError('Duplicate encoding accepted')
 api.write(api.HERE/'TINY_CHECKS.json',{'status':'passed','checks':checks});print('passed',len(checks))
