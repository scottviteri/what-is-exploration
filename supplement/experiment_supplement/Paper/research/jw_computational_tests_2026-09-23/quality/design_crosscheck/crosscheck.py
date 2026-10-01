#!/usr/bin/env python3
"""Independent DESIGN-only comparison of decomposed planner and complete primal LP."""
import os
for name in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):os.environ[name]='1'
import concurrent.futures,hashlib,importlib.util,json,multiprocessing,time,traceback
from fractions import Fraction as F
from pathlib import Path
BASE=Path(__file__).resolve().parent;QUALITY=BASE.parent;ROOT=next(p for p in BASE.parents if (p/'AGENTS.md').exists())
ARCHIVE=ROOT/'Paper/research/native_objective_benchmark_2026-09-15/results/hmm_91501_0.2/model.npz'
P=None

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def initialize():
 global P
 os.sched_setaffinity(0,{12+(multiprocessing.current_process()._identity[0]-1)%2})
 spec=importlib.util.spec_from_file_location('quality_crosscheck_subject',QUALITY/'planner.py');P=importlib.util.module_from_spec(spec);spec.loader.exec_module(P)

def model(name):
 np=P.np
 if name=='archived_hmm_91501_0.2':
  m=np.load(ARCHIVE);return m['T'],m['Z'],[42,128,129]
 # Exact deterministic binary sensors, with many zero full-history columns.
 T=np.ones((4,2,1,1));Z=np.zeros((4,2,1,2))
 for w in range(4):
  for a in range(2):Z[w,a,0,(w>>a)&1]=1
 return T,Z,[0,42,85,127,128,129]

def direct_target(T,Z,encoding):
 np=P.np;table=encoding.table();levels=P.core.levels(encoding.depth);decision=[h for layer in levels[:-1] for h in layer];lookup={h:table[i] for i,h in enumerate(decision)};cols=[]
 for h in levels[-1]:
  v=np.zeros((len(T),T.shape[-1]));v[:,0]=1;prob=1.
  for i,(a,o) in enumerate(h):
   v=np.array([v[w]@T[w,a] for w in range(len(T))])*Z[:,a,:,o]
   prob*=float(lookup[h[:i]][a])
  cols.append(v.sum(1)*prob)
 return np.stack(cols,1)

def direct_reward(E,name):
 np=P.np;W=len(E);prob=E.sum(0)/W;post=np.divide(E/W,prob,out=np.zeros_like(E),where=prob>0)
 if name=='information':
  terms=np.zeros_like(post);np.log2(post,out=terms,where=post>0)
  return float(np.log2(W)+(prob*(post*terms).sum(0)).sum())
 return float((prob*(post*post).sum(0)).sum()-1/W)

def face_for(g,T,Z,arm):
 if '_face' not in arm:return None,None
 np=P.np;name,part=arm.split('_face');pct=int(part)/100
 levels=P.dp.history_levels(3);mass=P.dp.controlled_masses(levels,T,Z);score=P.dp.terminal_scores(levels,mass)[name]
 best=P.dp.plan_terminal_rewards(levels,mass,score);worst=P.dp.plan_terminal_rewards(levels,mass,-score)
 maximum=best['optimal_objective'];minimum=-worst['optimal_objective'];threshold=maximum-max(1e-10,pct*(maximum-minimum))
 return {'reward':name,'maximum':maximum,'minimum':minimum,'threshold':threshold,'coefficients':best['coefficients'],'action_coefficients':np.bincount(g.leaf_index,weights=best['coefficients'],minlength=g.flow.shape[1])},best

def audited_value(ev,weights,kind):
 if kind=='native_minimax':return float(max(ev['lower'])),float(max(ev['upper']))
 return sum(float(w)*x for w,x in zip(weights,ev['lower'])),sum(float(w)*x for w,x in zip(weights,ev['upper']))

def one(task):
 name,arm=task;np=P.np;start=time.perf_counter();dest=BASE/'witnesses'/f'{name}__{arm}';dest.mkdir(exist_ok=True)
 out={'model':name,'arm':arm,'subject_sha256':sha(QUALITY/'planner.py'),'scope':'Archived design model or deterministic zero-column control; no confirmation model accessed'}
 try:
  T,Z,indices=model(name);g=P.core.geometry(T,Z,3);alltargets=P.training_targets(T,Z);targets=[alltargets[i] for i in indices];K=len(targets);weights=[F(i+1,K*(K+1)//2) for i in range(K)]
  out['targets']=indices;out['kernel_replay_error']=max(float(np.max(abs(t['kernel']-direct_target(T,Z,t['encoding'])))) for t in targets)
  assert out['kernel_replay_error']<1e-12
  out['zero_target_columns']=[int(np.sum(np.max(t['kernel'],axis=0)==0)) for t in targets]
  out['zero_raw_source_columns']=int(np.sum(np.max(g.raw,axis=0)==0))
  np.savez_compressed(dest/'inputs.npz',T=T,Z=Z,**{f'target_{i}':t['kernel'] for i,t in enumerate(targets)})
  face,reference=face_for(g,T,Z,arm);kind='native_weighted' if arm=='weighted' else 'native_minimax';out['kind']=kind;out['weights']=[str(w) for w in weights]
  if face:out['face']={k:v for k,v in face.items() if k not in ['coefficients','action_coefficients']}
  deadline=time.perf_counter()+20;cuts=[];records=[];best=None;lower=0.
  while time.perf_counter()<deadline and len(records)<100:
   E,rows,leaf,d,report,z=P.master(g,targets,weights,kind,cuts,max(.01,min(5,deadline-time.perf_counter())),face)
   # Match the subject's advertised face repair before auditing the actual policy.
   repair=0.
   if face:
    reward=float(leaf@face['coefficients'])
    if reward<face['threshold']:
     safe=min(face['maximum'],face['threshold']+1e-12);repair=min(1.,max(0.,(safe-reward)/(face['maximum']-reward)))
     E,rows,leaf=P.core.replay(g,(1-repair)*P.B.realization(g,rows)+repair*P.B.realization(g,reference['rows']))
   ev=P.oracle(g,E,rows,targets,deadline);lo,hi=audited_value(ev,weights,kind);lower=max(lower,float(report['dual']))
   idx=len(records);np.savez_compressed(dest/f'master_{idx:03d}.npz',**z);P.api.pack_evaluation(np,ev,dest/f'decoders_{idx:03d}.npz')
   np.savez_compressed(dest/f'policy_{idx:03d}.npz',E=E,rows=rows,leaf=leaf)
   record={'iteration':idx,'master_lower':float(report['dual']),'candidate_lower':lo,'candidate_upper':hi,'face_repair':repair,'seconds':time.perf_counter()-start}
   if face:
    coeffreward=float(leaf@face['coefficients']);replayed=direct_reward(E,face['reward']);record.update(reward=coeffreward,independent_reward=replayed,reward_replay_error=abs(coeffreward-replayed));assert coeffreward>=face['threshold']-1e-12 and abs(coeffreward-replayed)<1e-10
   records.append(record)
   if best is None or hi<best['upper']:best={'upper':hi,'lower':lo,'index':idx,'E':E,'rows':rows,'leaf':leaf}
   cuts.extend(ev['cuts'])
   if best['upper']-lower<=1e-6:break
  if best is None:raise RuntimeError('No complete decomposed iterate')
  out['decomposed']={'lower':lower,'upper':best['upper'],'gap':best['upper']-lower,'iterations':len(records),'best_iteration':best['index'],'records':records}
  # Independent complete-primal LP: same literal full-record targets, weights and face.
  ref_targets=[dict(kernel=t['kernel'],weight=float(w)) for t,w in zip(targets,weights)]
  constraint=(face['coefficients'],face['threshold']) if face else None
  st=time.perf_counter();Ec,rc,lc,cr=P.core.native_plan(g,ref_targets,kind,time_limit=20,certificate_path=dest/'complete_primal.npz',reward_constraint=constraint)
  out['complete_primal']={**cr,'elapsed_seconds':time.perf_counter()-st};np.savez_compressed(dest/'complete_policy.npz',E=Ec,rows=rc,leaf=lc)
  ce=P.oracle(g,Ec,rc,targets,time.perf_counter()+20);clo,chi=audited_value(ce,weights,kind);P.api.pack_evaluation(np,ce,dest/'complete_decoders.npz');out['complete_replayed_bounds']=[clo,chi]
  if face:
   actual=direct_reward(Ec,face['reward']);out['complete_actual_reward']=actual;out['complete_reward_constraint_shortfall']=max(0.,face['threshold']-actual);assert actual>=face['threshold']-2e-7
  checks={'decomposed_gap':best['upper']-lower,'primal_vs_decomposed_lower':abs(cr['primal']-lower),'primal_vs_decomposed_upper':abs(cr['primal']-best['upper']),'complete_original_decoder_gap':chi-clo,'complete_primal_vs_replay':abs(cr['primal']-chi)}
  out['checks']=checks
  assert checks['decomposed_gap']<=1e-6+2e-7 and max(checks['primal_vs_decomposed_lower'],checks['primal_vs_decomposed_upper'])<=2e-6 and checks['complete_original_decoder_gap']<2e-7 and checks['complete_primal_vs_replay']<2e-7
  out['status']='passed'
 except Exception as exc:out.update(status='failed',error=repr(exc),traceback=traceback.format_exc())
 out['elapsed_seconds']=time.perf_counter()-start;(dest/'result.json').write_text(json.dumps(out,indent=2)+'\n');return out

def main():
 start=time.perf_counter();models=['archived_hmm_91501_0.2','exact_zero_column_sensors'];arms=['weighted','minimax']+[f'{r}_face{p}' for r in ('information','brier') for p in (0,1,5)];tasks=[(m,a) for m in models for a in arms]
 (BASE/'report.json').write_text(json.dumps({'status':'running','frozen_tasks':tasks,'planner_sha256':sha(QUALITY/'planner.py'),'script_sha256':sha(__file__),'archive_sha256':sha(ARCHIVE),'note':'No confirmation models'},indent=2)+'\n')
 with concurrent.futures.ProcessPoolExecutor(2,initializer=initialize,mp_context=multiprocessing.get_context('spawn')) as pool:
  rows=[]
  for r in pool.map(one,tasks):rows.append(r);print(json.dumps({'model':r['model'],'arm':r['arm'],'status':r['status'],'error':r.get('error'),'seconds':r['elapsed_seconds']}),flush=True)
 report={'status':'passed' if all(r['status']=='passed' for r in rows) else 'failed','cases':len(rows),'elapsed_seconds':time.perf_counter()-start,'frozen_tasks':tasks,'planner_sha256':sha(QUALITY/'planner.py'),'script_sha256':sha(__file__),'archive_sha256':sha(ARCHIVE),'all_subject_hashes':sorted(set(r['subject_sha256'] for r in rows)),'scope':'Independent decomposed-vs-complete-primal design comparisons; float numerical evidence, not an exact or eventual theorem. No confirmation model accessed.','rows':rows}
 report['files']={str(p.relative_to(BASE)):sha(p) for p in sorted((BASE/'witnesses').rglob('*')) if p.is_file()};(BASE/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k not in ('rows','files','frozen_tasks')}),flush=True)
if __name__=='__main__':main()
