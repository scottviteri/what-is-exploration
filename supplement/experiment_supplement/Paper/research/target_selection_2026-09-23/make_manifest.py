import argparse,hashlib,json,random
from datetime import datetime,timezone
from pathlib import Path
HERE=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('mode',choices=['pilot','main']);p.add_argument('--output',type=Path,required=True);args=p.parse_args()
if args.output.exists():raise SystemExit('Manifest already exists; use a new filename')
old=['sensors_0.1_0.1','sensors_0.1_0.3','sensors_0.25_0.25','delayed_0.1_0.1','delayed_0.25_0.1','irreversible_0.1_0.1','irreversible_0.1_0.3','hmm_91501_0.2','hmm_91502_1.0','hmm_91503_5.0']
cases=[{'case':x} for x in old]
fresh=[]
for q in [4,8]:
 for ci,alpha in enumerate([.2,1.,5.]):
  for replicate in range(2):fresh.append(dict(case='fresh',worlds=q,concentration=alpha,seed=2026092800+1000*q+100*ci+replicate))
cases+=fresh
jobs=[]
def add(case,**kwargs):
 jobs.append(dict(case=case) if isinstance(case,str) else dict(case))
 jobs[-1].update(kwargs)
if args.mode=='pilot':
 add('hmm_91501_0.2',t=3,n=3,objective='native_weighted',strategy='random',max_targets=128,target_seed=923101,method='highs-ipm',executor='cpu')
 add('hmm_91501_0.2',t=3,n=3,objective='native_weighted',strategy='random',max_targets=128,target_seed=923101,method='cuopt-pdlp',executor='gpu')
 add('hmm_91502_1.0',t=4,n=3,objective='native_weighted',strategy='structured',max_targets=128,method='hybrid',executor='gpu')
 add('hmm_91501_0.2',t=4,n=3,objective='native_minimax',strategy='adaptive',face_objective='information',regret=.01,max_targets=32,method='highs-ipm',executor='cpu')
 add('sensors_0.1_0.3',t=6,n=3,objective='native_weighted',strategy='baseline',method='hybrid',executor='gpu')
 add('hmm_91501_0.2',t=3,n=4,objective='native_minimax',strategy='adaptive',max_targets=32,method='highs-ipm',executor='cpu')
 add(fresh[-3],t=3,n=3,eval_n=4,objective='prediction_error',strategy='baseline',method='highs-ipm',executor='cpu')
 add('sensors_0.1_0.3',t=3,n=3,objective='native_minimax',strategy='adaptive',face_objective='brier',regret=0.,max_targets=32,method='highs-ipm',executor='cpu')
else:
 if not (HERE/'PILOT_REVIEW.json').exists() or json.loads((HERE/'PILOT_REVIEW.json').read_text())['launch_authorized_by_checks'] is not True:raise SystemExit('Pilot review gate not passed')
 main=[]
 for case in cases:
  for t in [3,4]:
   shared=dict(t=t,n=3,eval_n=4 if t==3 else 0,method='hybrid' if t==4 else 'highs-ipm',executor='gpu' if t==4 else 'cpu')
   cap=128 if t==3 else 64
   for objective in ['native_minimax','native_weighted']:
    for strategy in ['random','structured']:
     for seed in [923101,923102,923103]:add(case,**shared,objective=objective,strategy=strategy,target_seed=seed,max_targets=cap)
   add(case,**shared,objective='native_minimax',strategy='adaptive',max_targets=cap)
   for objective in ['information','brier','surprisal','prediction_error','pseudo_count','empirical_label_entropy','posterior_disagreement','observation_occupancy_entropy','uniform','native_weighted','native_minimax']:
    base=shared|dict(executor='cpu',method='highs-ipm')
    add(case,**base,objective=objective,strategy='baseline')
  for objective in ['information','brier']:
   for regret in [0.,.01,.05]:add(case,t=3,n=3,eval_n=4 if regret==0 else 0,objective='native_minimax',strategy='adaptive',face_objective=objective,regret=regret,max_targets=128,method='highs-ipm',executor='cpu')
 random.Random(923501).shuffle(jobs)
 primary_count=len(jobs)
 for case in cases[:10]+fresh[::2]:
  add(case,t=3,n=4,objective='native_minimax',strategy='adaptive',max_targets=128,method='highs-ipm',executor='cpu',wall_seconds=2400)
 for case in cases[:10]:
  add(case,t=5,n=3,objective='native_minimax',strategy='adaptive',max_targets=16,method='hybrid',executor='gpu')
  for strategy in ['random','structured']:add(case,t=5,n=3,objective='native_weighted',strategy=strategy,target_seed=923101,max_targets=16,method='hybrid',executor='gpu')
  for objective in ['information','brier','surprisal','prediction_error','pseudo_count','empirical_label_entropy','posterior_disagreement','observation_occupancy_entropy','uniform']:
   add(case,t=5,n=3,objective=objective,strategy='baseline',method='highs-ipm',executor='cpu')
 for case in [cases[1],cases[6],cases[7],fresh[-3]]:
  for objective in ['information','brier','surprisal','prediction_error','pseudo_count','empirical_label_entropy','posterior_disagreement','observation_occupancy_entropy','uniform','native_weighted','native_minimax']:
   native=objective.startswith('native_')
   add(case,t=6,n=3,objective=objective,strategy='baseline',method='hybrid' if native else 'highs-ipm',executor='gpu' if native else 'cpu')
for i,j in enumerate(jobs):j['id']=f'cell_{i:04d}'
paths=list(HERE.glob('*.py'))+[HERE/'PROTOCOL.md',HERE/'ORIGIN.json',HERE/'VALIDATION.json',*([HERE/'PILOT_REVIEW.json'] if args.mode=='main' else []),
 HERE.parent/'native_objective_benchmark_2026-09-15/compute.py',HERE.parent/'noisy_diagnostic_transfer_2026-09-13/compute.py']
bindings={str(p.relative_to(HERE)) if p.is_relative_to(HERE) else '../'+str(p.relative_to(HERE.parent)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
manifest={'frozen_utc':datetime.now(timezone.utc).isoformat(),'study':'target selection and finite computation','mode':args.mode,
 'workers':4,'cpu_workers':3,'gpu_workers':1,'hours_limit':1 if args.mode=='pilot' else 8,
 'per_job_seconds':1800,'per_solve_seconds':300,'max_memory_gib_per_worker':5,'max_output_gib':12,
 'gpu_executable':'/tmp/exploration-lp-gpu-venv/bin/python','source_sha256':bindings,'cases':cases,
 'source_definition':'Exact supplied-model candidate class; actual world unknown; all history-adaptive policies.',
 'target_count_checkpoints':[8,16,32,64,128],'selection_seeds':[923101,923102,923103],
 'primary_jobs':len(jobs) if args.mode=='pilot' else primary_count,'jobs':jobs}
args.output.write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'jobs':len(jobs),'cpu':sum(j['executor']=='cpu' for j in jobs),'gpu':sum(j['executor']=='gpu' for j in jobs),'primary':manifest['primary_jobs'],'manifest':str(args.output)},indent=2))
