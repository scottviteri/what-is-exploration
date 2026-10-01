from common import *
from recovery_decoder import RecoveryDecoder
import time
plan=json.loads((ORIGINAL/'interim_reports/2026-09-23_capped_run_1638/AFTER_RUN_PLAN.json').read_text())
rows=[]
for cell in ['cell_0801','cell_0070']:
 item=next(x for x in plan['heldout_saved_policy_recovery'] if x['existing_job_id']==cell)
 with np.load(ORIGINAL/item['saved_policy']) as z:E=z['E'].copy()
 with np.load(ORIGINAL/'main_results'/cell/'model.npz') as z:T=z['T'].copy();Z=z['Z'].copy()
 targets=core.Targets(T,Z,4)
 d=RecoveryDecoder(E,16,'native-ipm',30)
 partial=(ORIGINAL/item['saved_policy']).parent/'held_out_partial.npz'
 with np.load(partial) as z:last=int(z['indices'][-1]) if len(z['indices']) else -1
 ids=sorted(set([0,32767]+list(range(max(0,last-2),min(32768,last+6)))))
 ts=time.monotonic()
 for j in ids:
  F=targets.get(j)['kernel'];r,w=d.solve(F)
  # Check again on the full original experiment, not the coarsened LP.
  source=E[:,w['source_indices']];G=w['decoder'];a=w['alpha'];b=w['b']
  hi=float(abs(source@G-F).sum(1).max()/2);lo=float(np.sum(F*b)-np.max(source.T@b,axis=1).sum())
  assert hi-lo<=2e-7 and lo<=hi+2e-7
  assert G.min()>=0 and np.max(abs(G.sum(1)-1))<1e-12
  assert a.min()>=0 and abs(a.sum()-1)<1e-12 and b.min()>=0 and np.max(b-a[:,None])<=1e-15
  rows.append(dict(cell=cell,target=j,lower=lo,upper=hi,lp_stationarity_diagnostic=r['lp_stationarity_diagnostic'],seconds=r['total_seconds']))
 print(cell,'passed',len(ids),'targets in',time.monotonic()-ts,flush=True)
write(HERE/'RECOVERY_PROBE.json',dict(status='passed',checks=rows,scope='Original-law intervals on saved failed-source examples; not a full-horizon sweep.'))
