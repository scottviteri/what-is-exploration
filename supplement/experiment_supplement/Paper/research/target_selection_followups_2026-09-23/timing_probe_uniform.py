"""Small timing-only comparison on an unchanged source experiment."""
from common import *
from recovery_decoder import RecoveryDecoder,WitnessNative
import highspy,time
from datetime import datetime,timezone

class ColdIPM(WitnessNative):
    def solve(self,F):
        started=time.perf_counter();F=np.asarray(F);cost=self.c.copy();cost[self.cost_indices]=-F.ravel()
        h=self._new_solver('ipm',cost);h.setOptionValue('time_limit',10.)
        h.run()
        if h.getModelStatus()!=highspy.HighsModelStatus.kOptimal:raise RuntimeError(h.modelStatusToString(h.getModelStatus()))
        r,w=self._extract(h,cost,F)
        r.update(method='timing-cold-ipm',attempts=[],fallback_used=False,total_seconds=time.perf_counter()-started,solve_seconds=time.perf_counter()-started)
        return r,w

orig=ORIGINAL/'main_results/cell_1009';r=json.loads((orig/'result.json').read_text());cp=r['checkpoints'][-1]['k']
with np.load(orig/f'checkpoint_{cp:03d}/policy.npz') as z:E=z['E'].copy()
with np.load(orig/'model.npz') as z:T=z['T'].copy();Z=z['Z'].copy()
ids=[27000,27500,28000,28500,29000,30000,31000,32767];targets=core.Targets(T,Z,4)
report={'utc':datetime.now(timezone.utc).isoformat(),'cell':'cell_1009','policy_sha256':digest(orig/f'checkpoint_{cp:03d}/policy.npz'),'model_sha256':digest(orig/'model.npz'),'scope':'Timing-only CPU-4 probe. Does not change active worker, source policy, recorded outcomes or the 2e-7 original-source interval requirement.','source_sha256':digest(HERE/'timing_probe_uniform.py'),'targets':ids,'rows':[]}
for mode in ['retained_simplex','cold_ipm']:
 d=RecoveryDecoder(E,16,'native-simplex',30)
 if mode=='cold_ipm':d.inner=ColdIPM(d.inner.E.copy(),16,'native-ipm',10)
 for i in ids:
  start=time.perf_counter()
  try:
   result,w=d.solve(targets.get(i)['kernel']);row={'target':i,'method':mode,'seconds':time.perf_counter()-start,'lower':result['lower'],'upper':result['upper'],'status':'passed','gap':result['upper']-result['lower']}
  except Exception as e:row={'target':i,'method':mode,'seconds':time.perf_counter()-start,'status':'failed','error':repr(e)}
  report['rows'].append(row);write(HERE/'TIMING_PROBE_UNIFORM.json',report);print(json.dumps(row),flush=True)
