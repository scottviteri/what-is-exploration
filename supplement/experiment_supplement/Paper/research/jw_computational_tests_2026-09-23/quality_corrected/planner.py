#!/usr/bin/env python3
"""Finite-budget supplied-model optimization; all evidence exported for replay."""
from pathlib import Path
from fractions import Fraction as F
import argparse,hashlib,importlib.util,json,os,sys,time,traceback,resource
HERE=Path(__file__).resolve().parent
ROOT=next(p for p in HERE.parents if (p/'AGENTS.md').exists())
sys.path.insert(0,str(HERE.parent/'backend_validation'))
import backend_api as api
B=api.bootstrap();np=B.np;core=B.core
from scipy import sparse
from adaptive_weights import RationalTarget
from frozen_adapter import array_hash
from weight_updates import tractability_weights,hard_target_update
spec=importlib.util.spec_from_file_location('quality_objective_dp',HERE/'source/objective_dp.py')
dp=importlib.util.module_from_spec(spec);spec.loader.exec_module(dp)

def write(p,v):api.write(p,v)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def flatten(levels):return [h for layer in levels for h in layer]
def encode(n,d,digits):
 rank=0
 for v in digits:rank=rank*(d+1)+v
 return RationalTarget(2,2,n,d,rank)
def compile_target(T,Z,e):
 layers=core.levels(e.depth);masses=core.masses(T,Z,layers);table=e.table();rows={h:table[i] for i,h in enumerate(flatten(layers[:-1]))};cols=[]
 for h in layers[-1]:
  w=F(1)
  for i,(a,o) in enumerate(h):w*=rows[h[:i]][a]
  cols.append(masses[h]*float(w))
 return np.stack(cols,axis=1)
def training_targets(T,Z):
 enc=[];n=3;decisions=flatten(core.levels(n)[:-1]);trees=core.Targets(T,Z,n)
 for index in range(trees.count):
  bits=[(index>>k)&1 for k in range(2**n-2,-1,-1)];digits=[]
  for h in decisions:
   node=0
   for a,o in h:node=2*node+1+o
   digits.append(1-bits[node])
  enc.append(encode(n,1,digits))
 for n in [1,2,3]:enc.append(encode(n,2,[1]*len(flatten(core.levels(n)[:-1]))))
 targets=[{'id':e.key,'kernel':compile_target(T,Z,e),'mass':e.mass,'encoding':e} for e in enc]
 # Literal full-history kernels must recover the original deterministic tree kernel.
 for j in range(128):
  Ffull=targets[j]['kernel'];table=targets[j]['encoding'].table();lookup={h:table[i] for i,h in enumerate(decisions)}
  compatible=[all(lookup[h[:i]][a]==1 for i,(a,o) in enumerate(h)) for h in core.levels(3)[-1]];selected=Ffull[:,compatible]
  if np.max(abs(selected-trees.get(j)['kernel']))>1e-12:raise ValueError('Deterministic full-record embedding changed target')
 return targets

def master(g,targets,weights,kind,cuts,seconds,face=None):
 if face is None:
  return B.master(g,[dict(t,weight=float(w)) for t,w in zip(targets,weights)],kind,cuts,seconds)
 P=g.flow.shape[1];D=1 if kind=='native_minimax' else len(targets);V=P+D
 c=np.r_[np.zeros(P),[1.] if D==1 else list(map(float,weights))]
 Ae=sparse.hstack([g.flow,sparse.csr_matrix((len(g.flow_rhs),D))],format='csr')
 rows=[];rhs=[]
 for cut in cuts:
  row=np.zeros(V);row[:P]=-cut['slope'];row[P+(0 if D==1 else cut['target'])]=-1
  rows.append(row);rhs.append(-cut['intercept'])
 row=np.zeros(V);row[:P]=-face['action_coefficients'];rows.append(row);rhs.append(-face['threshold'])
 Au=sparse.csr_matrix(np.asarray(rows));rhs=np.asarray(rhs)
 st=time.perf_counter();sol,report=core.solve_arrays(c,Ae,g.flow_rhs,Au,rhs,[(0,1)]*V,'highs',seconds)
 E,pr,leaf=core.replay(g,sol.x[:P]);report['total_seconds']=time.perf_counter()-st
 z=dict(cost=c,solution=sol.x,b_eq=g.flow_rhs,b_ub=rhs,eq_dual=sol.eqlin.marginals,ub_dual=sol.ineqlin.marginals,lower_dual=sol.lower.marginals,upper_dual=sol.upper.marginals)
 for name,A in [('A_eq',Ae),('A_ub',Au)]:
  for key,val in [('data',A.data),('indices',A.indices),('indptr',A.indptr),('shape',A.shape)]:z[name+'_'+key]=val
 return E,pr,leaf,sol.x[P:],report,z

def oracle(g,E,rows,targets,deadline):
 """Drop exactly zero target columns for solving, then lift every witness back."""
 st=time.perf_counter();decoders={};build={};cost=[];lo=[];hi=[];cuts=[];witnesses=[]
 for j,t in enumerate(targets):
  if time.perf_counter()>=deadline:raise TimeoutError('Selected-target audit deadline')
  full=t['kernel'];keep=np.flatnonzero(np.max(full,axis=0)>0);Y=len(keep)
  if Y not in decoders:
   ts=time.perf_counter();decoders[Y]=B.StableDecoder(E,Y,time_limit=max(.01,min(2,deadline-time.perf_counter())));build[Y]=time.perf_counter()-ts
  ts=time.perf_counter();report,w=decoders[Y].solve(full[:,keep]);cost.append(time.perf_counter()-ts)
  G=np.zeros((w['decoder'].shape[0],full.shape[1]));G[:,keep]=w['decoder']
  dual=np.zeros_like(full);dual[:,keep]=w['b'];w=dict(w,decoder=G,b=dual)
  source=E[:,w['source_indices']];alpha=w['alpha']
  upper=float(np.max(abs(source@G-full).sum(1)/2));lower=float(np.sum(full*dual)-np.max(source.T@dual,axis=1).sum())
  residual=max(abs(G.sum(1)-1).max(),max(0.,-G.min()),abs(alpha.sum()-1),max(0.,-alpha.min()),max(0.,-dual.min()),max(0.,(dual-alpha[:,None]).max()),abs(upper-lower))
  if residual>2e-7:raise ValueError('Original lifted decoder failed: '+str(residual))
  inter,slope,_=B.make_cut(g,full,w)
  cuts.append(dict(target=j,intercept=inter,slope=slope,alpha=alpha,b=dual));lo.append(lower);hi.append(upper);witnesses.append(w)
 for j,t in enumerate(targets):
  Y=int(np.sum(np.max(t['kernel'],axis=0)>0));count=sum(int(np.sum(np.max(v['kernel'],axis=0)>0))==Y for v in targets);cost[j]+=build[Y]/count
 return dict(lower=np.asarray(lo),upper=np.asarray(hi),cuts=cuts,witnesses=witnesses,cost=np.asarray(cost),seconds=time.perf_counter()-st)

def output_policy(folder,g,E,rows,leaf,extra):
 folder.mkdir(parents=True,exist_ok=True);np.savez_compressed(folder/'policy.npz',E=E,rows=rows,leaf=leaf)
 write(folder/'policy.json',dict(extra,policy_sha256=array_hash(rows)))

def baseline(g,T,Z,out,started):
 geometry_seconds=time.perf_counter()-started
 ts=time.perf_counter();levels=dp.history_levels(3);mass=dp.controlled_masses(levels,T,Z);scores=dp.terminal_scores(levels,mass);shared=geometry_seconds+time.perf_counter()-ts;saved={}
 for name in ['information','brier']:
  ts=time.perf_counter();r=dp.plan_terminal_rewards(levels,mass,scores[name]);leaf=r['weights'][-len(levels[-1]):];available=shared+time.perf_counter()-ts
  output_policy(out/name,g,r['E'],r['rows'],leaf,{'method':name,'available_seconds':available,'timing_scope':'individual DP plus common geometry/reward construction; excludes serialization','optimal_reward':r['optimal_objective'],'reward':r['objective'],'checks':r['checks']})
  np.savez_compressed(out/name/'bellman.npz',**{k:r[k] for k in ['weights','action_values','tie_mask','values','coefficients']})
  saved[name]={k:v for k,v in r.items() if k not in ['E','rows','weights','action_values','tie_mask','values','coefficients']}
 ts=time.perf_counter();rows=np.full((len(g.decisions),2),.5);a=B.realization(g,rows);E,rows,leaf=core.replay(g,a);available=geometry_seconds+time.perf_counter()-ts
 output_policy(out/'uniform',g,E,rows,leaf,{'method':'uniform','available_seconds':available,'timing_scope':'geometry and uniform policy construction only'})
 write(out/'result.json',{'status':'completed','baselines':saved,'end_to_end_seconds':time.perf_counter()-started})

def run(modelpath,out,arm,budget=40,design=False):
 out=Path(out);out.mkdir(parents=True,exist_ok=True);model=np.load(modelpath);T,Z=model['T'],model['Z'];started=time.perf_counter();g=core.geometry(T,Z,3)
 if arm=='baseline':return baseline(g,T,Z,out,started)
 targets=training_targets(T,Z);K=len(targets);eps=F(1,20);ref=[F(1,K)]*K;emphasis=ref[:];cost=np.zeros(K);scale=None
 kind='native_minimax' if arm=='minimax' or '_face' in arm else 'native_weighted';face=None
 if '_face' in arm:
  name,percent=arm.split('_face');pct=int(percent)/100
  levels=dp.history_levels(3);mass=dp.controlled_masses(levels,T,Z);score=dp.terminal_scores(levels,mass)[name]
  best=dp.plan_terminal_rewards(levels,mass,score);worst=dp.plan_terminal_rewards(levels,mass,-score)
  maximum=best['optimal_objective'];minimum=-worst['optimal_objective'];slack=max(1e-10,pct*(maximum-minimum))
  face=dict(reward=name,maximum=maximum,minimum=minimum,range=maximum-minimum,percent=percent,numerical_slack=1e-10,slack=slack,threshold=maximum-slack,coefficients=best['coefficients'],action_coefficients=np.bincount(g.leaf_index,weights=best['coefficients'],minlength=g.flow.shape[1]))
 face_reference=best if face else None
 deadline=started+budget;cuts=[];seen=set();records=[];average_records=[];sumreal=np.zeros(g.flow.shape[1]);count=0;status='time_cap';error=None;timings={'setup_seconds':time.perf_counter()-started};fixedlower=0.;allrecords=[]
 # Common order is frozen; sorting remains aligned for every numerical statement.
 order=np.random.default_rng(926201).permutation(K).tolist();targets=[targets[j] for j in order]
 specs=[dict(kind='rational',key=t['id']) for t in targets]
 write(out/'metadata.json',dict(arm=arm,kind=kind,t=3,model_sha256=sha(modelpath),model_path=str(Path(modelpath).resolve()),target_specs=specs,background_epsilon=str(eps),omitted_mass=str(eps*(1-sum((t['mass'] for t in targets),F(0)))),target_order_seed=926201,face={k:(v.tolist() if hasattr(v,'tolist') else v) for k,v in face.items()} if face else None,budget=budget,setup_seconds=timings['setup_seconds']))
 while time.perf_counter()<deadline and count<200:
  weights=[(1-eps)*x+eps*t['mass'] for x,t in zip(emphasis,targets)] if kind=='native_weighted' else ref
  rec=dict(iteration=count,cut_prefix=len(cuts),weights=[str(w) for w in weights],emphasis=[str(w) for w in emphasis]);allrecords.append(rec)
  try:
   E,rows,leaf,d,report,z=master(g,targets,weights,kind,cuts,max(.01,min(10,deadline-time.perf_counter())),face)
   
   if face:
    achieved=float(leaf@face['coefficients'])
    if achieved<face['threshold']:
     safe_target=min(face['maximum'],face['threshold']+1e-12)
     mix=min(1.,max(0.,(safe_target-achieved)/(face['maximum']-achieved)))
     original=B.realization(g,rows);reference=B.realization(g,face_reference['rows'])
     E,rows,leaf=core.replay(g,(1-mix)*original+mix*reference)
     rec['face_repair_mixture']=mix
    rec['actual_reward']=float(leaf@face['coefficients'])
    if rec['actual_reward']<face['threshold']-1e-12:raise ValueError('Actual reward outside advertised face')
   rec.update(master=z,master_report=report,E=E,rows=rows,leaf=leaf,master_available_seconds=time.perf_counter()-started)
   if time.perf_counter()>deadline:raise TimeoutError('Master evidence late')
   ev=oracle(g,E,rows,targets,deadline);rec.update(evaluation=ev,available_seconds=time.perf_counter()-started)
   if time.perf_counter()>deadline:raise TimeoutError('Decoder evidence late')
   if face and float(leaf@face['coefficients'])<face['threshold']-2e-7:raise ValueError('Reward face violated on actual policy')
   upper=float(max(ev['upper']) if kind=='native_minimax' else np.asarray(list(map(float,weights)))@ev['upper'])
   shift=sum((min(F(0),w-F.from_float(float(w))) for w in weights),F(0)) if kind=='native_weighted' else F(0)
   lower=float(report['dual'])+float(shift);rec.update(lower=lower,upper=upper,cost_rounding_lower_shift=str(shift))
   if arm not in ['tractability','hard']:fixedlower=max(fixedlower,lower);rec['lower']=fixedlower
   records.append(rec);count+=1;sumreal+=B.realization(g,rows);cost+=ev['cost'];rec['decoder_costs']=ev['cost'].tolist()
   for cut in ev['cuts']:
    key=(cut['target'],float(cut['intercept']),cut['slope'].tobytes())
    if key not in seen:seen.add(key);cuts.append(cut)
   if arm in ['tractability','hard'] and count>1:
    Ea,ra,la=core.replay(g,sumreal/count);av=dict(iteration=count-1,E=Ea,rows=ra,leaf=la,weights=rec['weights'])
    try:
     eva=oracle(g,Ea,ra,targets,deadline);av.update(evaluation=eva,available_seconds=time.perf_counter()-started)
     if time.perf_counter()<=deadline:average_records.append(av);cost+=eva['cost'];av['decoder_costs']=eva['cost'].tolist();rec['average_decoder_costs']=eva['cost'].tolist()
     else:rec['average_rejection']='late'
    except Exception as exc:rec['average_rejection']=repr(exc)
   elif arm in ['tractability','hard']:average_records.append(rec)
   rec['cumulative_decoder_costs']=cost.tolist()
   if arm=='tractability':
    if scale is None:scale=max(float(np.median(ev['cost'][ev['cost']>0])),1e-9)
    emphasis=list(tractability_weights(ref,[F.from_float(float(v)) for v in cost],F.from_float(scale)));rec['cost_scale']=scale
   elif arm=='hard':
    intervals=[(F.from_float(max(0.,float(lo))),F.from_float(min(1.,max(float(lo),float(hi))))) for lo,hi in zip(ev['lower'],ev['upper'])]
    update=hard_target_update(emphasis,intervals,F(1))
    emphasis=list(update[0] if isinstance(update,tuple) else update);rec['weight_update_metadata']=update[1]
   else:
    if min(r['upper'] for r in records)-fixedlower<=1e-6:status='converged';break
  except Exception as exc:
   rec['error']=repr(exc);error=repr(exc);status='time_cap' if isinstance(exc,TimeoutError) or time.perf_counter()>=deadline else 'failed';break
 planning_seconds=time.perf_counter()-started
 # Serialization is outside the planner budget, separately timed and never hidden.
 export_start=time.perf_counter()
 np.savez_compressed(out/'inputs.npz',T=T,Z=Z,raw=g.raw,leaf_index=g.leaf_index,**{f'target_{j}':t['kernel'] for j,t in enumerate(targets)})
 cutarrays={}
 for i,c in enumerate(cuts):
  for k,v in c.items():cutarrays[f'{i}_{k}']=v
 np.savez_compressed(out/'cuts.npz',**cutarrays)
 for i,r in enumerate(allrecords):
  p=out/f'round_{i:03d}';p.mkdir(exist_ok=True)
  if 'master' in r:np.savez_compressed(p/'master.npz',**r['master']);np.savez_compressed(p/'policy.npz',E=r['E'],rows=r['rows'],leaf=r['leaf'])
  if 'evaluation' in r:api.pack_evaluation(np,r['evaluation'],p/'decoders.npz')
  write(p/'record.json',{k:v for k,v in r.items() if k not in ['master','E','rows','leaf','evaluation']})
 for i,r in enumerate(average_records):
  p=out/f'average_{i:03d}';p.mkdir(exist_ok=True);np.savez_compressed(p/'policy.npz',E=r['E'],rows=r['rows'],leaf=r['leaf']);api.pack_evaluation(np,r['evaluation'],p/'decoders.npz');write(p/'record.json',{k:r[k] for k in ['iteration','available_seconds','weights']})
 endpoints={}
 for limit in [2,10,40]:
  eligible=[r for r in records if r['available_seconds']<=limit]
  if eligible:
   chosen=eligible[-1] if arm in ['tractability','hard'] else min(eligible,key=lambda r:r['upper'])
   r=chosen;lossgap=r['upper']-r['lower'];data=dict(method=arm,budget=limit,iteration=r['iteration'],available_seconds=r['available_seconds'],selected_lower=r['lower'],selected_upper=r['upper'],selected_gap=lossgap,omitted_mass=str(eps*(1-sum((t['mass'] for t in targets),F(0)))) if kind=='native_weighted' else None,policy_kind='last_fully_audited' if arm in ['tractability','hard'] else 'best_training_incumbent')
   
   if face:data.update(actual_reward=float(r['leaf']@face['coefficients']),reward_threshold=face['threshold'],optimal_reward=face['maximum'],reward_regret=face['maximum']-float(r['leaf']@face['coefficients']))
   output_policy(out/f'checkpoint_{limit}',g,r['E'],r['rows'],r['leaf'],data);endpoints[str(limit)]=data
  else:endpoints[str(limit)]={'status':'no_in_budget_audited_policy'}
  eligibleavg=[r for r in average_records if r['available_seconds']<=limit]
  if eligibleavg:
   r=eligibleavg[-1];output_policy(out/f'average_checkpoint_{limit}',g,r['E'],r['rows'],r['leaf'],dict(method=arm+'_average',budget=limit,iteration=r['iteration'],available_seconds=r['available_seconds'],policy_kind='realization_average',selected_full_objective_regret=None))
 write(out/'result.json',dict(status=status,error=error,arm=arm,iterations=count,cuts=len(cuts),planning_seconds=planning_seconds,export_seconds=time.perf_counter()-export_start,checkpoints=endpoints,cost_scale=scale,cumulative_decoder_costs=cost.tolist(),scope='Finite numerical evidence; no eventual J_w or optimization rate claim'))
 write(out/'FILES.json',{str(p.relative_to(out)):sha(p) for p in sorted(out.rglob('*')) if p.is_file() and p.name!='FILES.json'})

if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--model',required=True);parser.add_argument('--out',required=True);parser.add_argument('--arm',required=True);parser.add_argument('--cpu',type=int);parser.add_argument('--seconds',type=float,default=40);args=parser.parse_args()
 if args.cpu is not None:os.sched_setaffinity(0,{args.cpu})
 resource.setrlimit(resource.RLIMIT_AS,(4*1024**3,4*1024**3))
 try:run(args.model,args.out,args.arm,args.seconds)
 except Exception as exc:
  Path(args.out).mkdir(parents=True,exist_ok=True);write(Path(args.out)/'FAILURE.json',{'error':repr(exc),'traceback':traceback.format_exc()});raise
