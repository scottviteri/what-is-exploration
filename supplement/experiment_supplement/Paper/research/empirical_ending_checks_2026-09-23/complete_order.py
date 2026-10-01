"""Finish the five formerly absent Brier5 pair comparisons, with fixed selections."""
import os
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
from diagnostics import *
d=json.loads((HERE/'COMPLETE_REWARDS.json').read_text());selected={}
for r in sorted(d['records'],key=lambda x:x['cell']):selected.setdefault((r['case'],r['method']),r)
original=json.loads((HERE/'order/RESULTS.json').read_text());seen={(r['source'],r['target']) for r in original['records']};out=HERE/'order_completion';out.mkdir(exist_ok=False);records=[];jobs=[]
for case in d['ranges']:
 for method in ['weighted128','minimax']:
  n=selected[case,method];b=selected[case,'face_brier_0.05']
  for s,t in [(n,b),(b,n)]:
   if (s['cell'],t['cell']) not in seen:jobs.append(dict(case=case,source=s['cell'],target=t['cell'],source_method=s['method'],target_method=t['method'],source_policy=s['policy'],target_policy=t['policy']))
assert len(jobs)==20
write(out/'MANIFEST.json',dict(selection='Same lexical original/native representative rule; newly completed Brier5 controls only.',jobs=jobs,input_sha256=digest(HERE/'COMPLETE_REWARDS.json')))
for i,j in enumerate(jobs):
 with np.load(j['source_policy']) as z:E=z['E'].copy()
 with np.load(j['target_policy']) as z:F=z['E'].copy()
 for p in [j['source_policy'],j['target_policy']]:assert digest(Path(p))==d['input_sha256'][p]
 dec=RecoveryDecoder(E,64,'native-ipm',60);v,w=dec.solve(F);G=w['decoder'];alpha=w['alpha'];b=w['b'];keep=w['source_indices']
 assert G.min()>=0 and np.max(abs(G.sum(1)-1))<1e-12 and alpha.min()>=0 and abs(alpha.sum()-1)<1e-12 and b.min()>=0 and np.max(b-alpha[:,None])<1e-15
 lo=float(np.sum(F*b)-np.max(E[:,keep].T@b,axis=1).sum());hi=float(np.max(abs(E[:,keep]@G-F).sum(1))/2);assert -2e-7<=hi-lo<=2e-7
 p=out/f'witness_{i:03d}.npz';np.savez_compressed(p,E=E,F=F,G=G,alpha=alpha,b=b,source_indices=keep,lower=lo,upper=hi)
 records.append(dict(j,status='passed',lower=lo,upper=hi,witness=str(p),witness_sha256=digest(p)))
write(out/'RESULTS.json',dict(status='complete',records=records))
allrows=original['records']+records;pairs={}
for r in allrows:pairs.setdefault((r['case'],tuple(sorted([r['source'],r['target']]))),[]).append(r)
assert len(allrows)==176 and len(pairs)==88
report=dict(status='passed',pairs=88,directions=176,incomparable=sum(all(r['lower']>1e-6 for r in rs) for rs in pairs.values()),equivalent_within_tolerance=sum(all(r['upper']<=1e-6 for r in rs) for rs in pairs.values()),records=allrows,scope='One lexically chosen representative per class/method, fixed without looking at directed errors; native weighted/minimax versus ordinary Brier and Brier5, both directions. Numerical float64 witness checks, finite time 3.')
write(HERE/'COMPLETE_ORDER.json',report);print({k:v for k,v in report.items() if k!='records'})
