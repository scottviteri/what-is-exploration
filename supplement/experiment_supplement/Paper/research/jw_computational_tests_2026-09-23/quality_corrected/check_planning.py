#!/usr/bin/env python3
"""Independent causal, objective, master, reward-face and endpoint replay.

Imports no planner/decoder and never optimizes. This checks finite numerical
witnesses, not eventual J_w, complete optimal faces, or exact arithmetic LPs.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,hashlib,json,re,sys,time,math
import numpy as np
from scipy import sparse
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'backend_validation'))
from independent_audit import histories,law,rational_target,replay,norm,pos,lp,matrix,decode
TOL=2e-7

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def raw_tables(T,Z,t):
 layers=histories(t);decisions=sum(layers[:-1],[]);di={h:i for i,h in enumerate(decisions)}
 raw=np.stack([law(T,Z,h) for h in layers[-1]],axis=1)
 leafidx=np.asarray([2*di[h[:-1]]+h[-1][0] for h in layers[-1]])
 return layers,decisions,di,raw,leafidx

def objective_coefficients(raw,name):
 Q=raw.shape[0];mass=raw.mean(0);post=np.divide(raw/Q,mass[None,:],out=np.zeros_like(raw),where=mass[None,:]>0)
 if name=='information':
  logpost=np.log2(post,out=np.zeros_like(post),where=post>0);score=np.log2(Q)+(post*logpost).sum(0)
 elif name=='brier':score=(post*post).sum(0)-1/Q
 else:raise ValueError('Unknown posterior objective')
 return mass*score

def bellman(coeff,layers):
 values=dict(zip(layers[-1],map(float,coeff)));action={}
 for layer in reversed(layers[:-1]):
  for h in layer:
   action[h]=np.asarray([sum(values[h+((a,o),)] for o in range(2)) for a in range(2)])
   values[h]=float(max(action[h]))
 return values,action

def policy_check(z,layers,raw):
 rows=z['rows'];aw,w=replay(rows,layers);E=raw*w
 residual=max(norm(rows.sum(1)-1),pos(-rows),norm(E-z['E']),norm(E.sum(1)-1))
 if 'leaf' in z:residual=max(residual,norm(w-z['leaf']))
 return residual,aw,w,E

def target_mass(key):
 match=re.fullmatch(r'rational-native-v1/a2o2/n(\d+)/d(\d+)/r(\d+)',key)
 if match is None:raise ValueError('Unknown target encoding')
 n,d,r=map(int,match.groups());count=(d+1)**sum(4**i for i in range(n))
 if d<1 or not 0<=r<count:raise ValueError('Invalid target encoding')
 return F(1,2**(n+1+d)*count)

def expected_pool():
 full=histories(3);prefix=sum(full[:-1],[]);keys=[]
 for tree in range(128):
  decisions=[(tree>>i)&1 for i in range(6,-1,-1)];rank=0
  for h in prefix:
   node=0
   for _,o in h:node=2*node+1+o
   rank=2*rank+1-decisions[node]
  keys.append(f'rational-native-v1/a2o2/n3/d1/r{rank}')
 for n in [1,2,3]:
  rank=sum(3**i for i in range(sum(4**d for d in range(n))))
  keys.append(f'rational-native-v1/a2o2/n{n}/d2/r{rank}')
 return keys

def baseline_check(folder,T,Z):
 layers,decisions,di,raw,leafidx=raw_tables(T,Z,3);residual=0.;rows=[]
 for name in ['information','brier','uniform']:
  p=folder/name;z=np.load(p/'policy.npz');meta=json.loads((p/'policy.json').read_text());rr,aw,w,E=policy_check(z,layers,raw);residual=max(residual,rr)
  record={'method':name}
  if name=='uniform':residual=max(residual,norm(z['rows']-.5))
  else:
   coeff=objective_coefficients(raw,name);values,actions=bellman(coeff,layers);b=np.load(p/'bellman.npz');allhist=sum(layers,[])
   residual=max(residual,norm(b['coefficients']-coeff),norm(b['values']-np.asarray([values[h] for h in allhist])),norm(b['action_values']-np.asarray([actions[h] for h in decisions])),abs(meta['optimal_reward']-values[()]),abs(meta['reward']-float(w@coeff)))
   if values[()]-float(w@coeff)>TOL:raise ValueError('DP returned policy is not reward optimal')
   # Every supported action must attain its recursively optimal action value.
   for i,h in enumerate(decisions):residual=max(residual,abs(values[h]-float(z['rows'][i]@actions[h])))
   record.update(optimum=values[()],attained=float(w@coeff))
  rows.append(record)
 if residual>TOL:raise ValueError(f'Baseline residual {residual}')
 return {'status':'passed','kind':'baseline','residual':residual,'rows':rows,'scope':'Independent posterior formula, Bellman and causal policy replay'}

def check(folder,model_path=None):
 folder=Path(folder);started=time.perf_counter()
 if not (folder/'metadata.json').exists():
  if model_path is None:raise ValueError('Baseline check requires original --model')
  model=np.load(model_path);return baseline_check(folder,model['T'],model['Z'])
 m=json.loads((folder/'metadata.json').read_text());result=json.loads((folder/'result.json').read_text());inp=np.load(folder/'inputs.npz');T,Z=inp['T'],inp['Z']
 origin=Path(model_path or m['model_path'])
 if sha(origin)!=m['model_sha256']:raise ValueError('Original model hash mismatch')
 original=np.load(origin);residual=max(norm(T-original['T']),norm(Z-original['Z']),norm(T.sum(-1)-1),norm(Z.sum(-1)-1),pos(-T),pos(-Z))
 layers,decisions,di,raw,leafidx=raw_tables(T,Z,m['t']);P=2*len(decisions)
 if not np.array_equal(leafidx,inp['leaf_index']):raise ValueError('Incorrect controlled leaf map')
 residual=max(residual,norm(raw-inp['raw']));specs=m['target_specs'];keys=[s['key'] for s in specs];K=len(keys)
 if any(s['kind']!='rational' for s in specs) or sorted(keys)!=sorted(expected_pool()):raise ValueError('Training pool differs from frozen 131 targets')
 permutation=np.random.default_rng(m['target_order_seed']).permutation(131).tolist()
 if keys!=[expected_pool()[i] for i in permutation]:raise ValueError('Target order differs from declared seed')
 targets=[rational_target(T,Z,k) for k in keys];masses=[target_mass(k) for k in keys];eps=F(m['background_epsilon']);beta=eps*(1-sum(masses))
 if F(m['omitted_mass'])!=beta:raise ValueError('Omitted background mass changed')
 for j,target in enumerate(targets):residual=max(residual,norm(target-inp[f'target_{j}']),norm(target.sum(1)-1),pos(-target))
 face=m.get('face');facecoeff=None;threshold=None
 if face:
  facecoeff=objective_coefficients(raw,face['reward']);v,_=bellman(facecoeff,layers);neg,_=bellman(-facecoeff,layers)
  maximum=v[()];minimum=-neg[()];slack=max(1e-10,float(face['percent'])/100*(maximum-minimum));threshold=maximum-slack
  expected_action=np.bincount(leafidx,weights=facecoeff,minlength=P)
  residual=max(residual,norm(facecoeff-np.asarray(face['coefficients'])),norm(expected_action-np.asarray(face['action_coefficients'])),abs(maximum-face['maximum']),abs(minimum-face['minimum']),abs(threshold-face['threshold']))
 # Independently validate every saved cut on complete raw geometry.
 packed=np.load(folder/'cuts.npz');indices=sorted({int(k.split('_')[0]) for k in packed.files});cuts=[]
 if indices!=list(range(len(indices))):raise ValueError('Noncontiguous saved cuts')
 for i in indices:
  j=int(packed[f'{i}_target']);alpha=packed[f'{i}_alpha'];b=packed[f'{i}_b'];inter=float(packed[f'{i}_intercept']);s=packed[f'{i}_slope']
  if not 0<=j<K:raise ValueError('Cut target outside library')
  expect=np.bincount(leafidx,weights=np.max(raw.T@b,axis=1),minlength=P)
  residual=max(residual,abs(alpha.sum()-1),pos(-alpha),pos(-b),pos(b-alpha[:,None]),abs(inter-np.sum(targets[j]*b)),norm(s-expect))
  cuts.append((j,inter,s))
 rounds=[];valid=[];maxlower=0.;kind=m['kind'];D=1 if kind=='native_minimax' else K;expected_flow=sparse.lil_matrix((len(decisions),P+D));rhs=np.zeros(len(decisions));rhs[0]=1
 for i,h in enumerate(decisions):
  expected_flow[i,2*i]=1;expected_flow[i,2*i+1]=1
  if h:expected_flow[i,2*di[h[:-1]]+h[-1][0]]=-1
 for folder_r in sorted(folder.glob('round_*')):
  r=json.loads((folder_r/'record.json').read_text());i=r['iteration'];exact=list(map(F,r['weights']));emphasis=list(map(F,r['emphasis']))
  if len(exact)!=K or len(emphasis)!=K or sum(emphasis)!=1 or any(v<0 for v in emphasis):raise ValueError('Unnormalized emphasis')
  expected=[(1-eps)*x+eps*b for x,b in zip(emphasis,masses)] if kind=='native_weighted' else [F(1,K)]*K
  if exact!=expected:raise ValueError('Wrong literal objective coefficients')
  if not (folder_r/'master.npz').exists():rounds.append((r,None,None,None));continue
  z=np.load(folder_r/'master.npz');rr,lower,lpupper=lp(z);residual=max(residual,rr);weights=np.asarray(list(map(float,exact)));cost=np.r_[np.zeros(P),[1.] if D==1 else weights]
  residual=max(residual,norm(cost-z['cost']),norm((matrix(z,'A_eq')-expected_flow.tocsr()).data),norm(rhs-z['b_eq']))
  prefix=int(r['cut_prefix'])
  if not 0<=prefix<=len(cuts):raise ValueError('Cut prefix outside saved sequence')
  expected_ub=sparse.lil_matrix((prefix+int(face is not None),P+D));expected_rhs=[]
  for j,(target,inter,s) in enumerate(cuts[:prefix]):expected_ub[j,:P]=-s;expected_ub[j,P+(0 if D==1 else target)]=-1;expected_rhs.append(-inter)
  if face:expected_ub[prefix,:P]=-expected_action;expected_rhs.append(-threshold)
  residual=max(residual,norm((matrix(z,'A_ub')-expected_ub.tocsr()).data),norm(z['b_ub']-np.asarray(expected_rhs)))
  # Literal rational costs differ from submitted binary floats; lower shift is explicit.
  correction=float(sum((min(F(0),e-F.from_float(float(e))) for e in exact),F(0))) if kind=='native_weighted' else 0.
  lower+=correction
  pol=np.load(folder_r/'policy.npz');rr,aw,leaf,E=policy_check(pol,layers,raw);residual=max(residual,rr)
  if 'evaluation_policy_repaired' in r and r['evaluation_policy_repaired']:
   pass # Its feasibility and law, rather than equality with the LP action vector, matter.
  if (folder_r/'decoders.npz').exists():
   ev=np.load(folder_r/'decoders.npz');rr,lo,hi=decode(ev,targets,E);residual=max(residual,rr);upper=float(max(hi) if D==1 else weights@hi)
   if 'available_seconds' not in r:raise ValueError('Decoder evidence lacks availability time')
   if r['available_seconds']<=m['budget'] and 'upper' in r:
    if face and float(leaf@facecoeff)<threshold-1e-12:raise ValueError('Returned policy violates literal reward-face threshold')
    if m['arm'] not in ['tractability','hard']:maxlower=max(maxlower,lower);lower=maxlower
    residual=max(residual,abs(upper-r['upper']))
    if r['lower']>lower+TOL:raise ValueError('Unjustified master lower bound')
    valid.append((r,pol,aw,leaf,E,upper,lower))
  rounds.append((r,pol,aw,leaf))
 # Replay the declared emphasis rule from saved interval/cost evidence.
 weight_rule_checks=0;cost_rule_checks=0;last_cost=np.zeros(K);fixed_cost_scale=None
 for r,pol,aw,leaf,E,upper,lower in valid:
  if 'cumulative_decoder_costs' in r:
   charged=np.asarray(r['decoder_costs'])+np.asarray(r.get('average_decoder_costs',[0.]*K))
   if np.any(charged<0):raise ValueError('Negative charged decoder cost')
   residual=max(residual,norm(last_cost+charged-np.asarray(r['cumulative_decoder_costs'])))
   last_cost=np.asarray(r['cumulative_decoder_costs']);cost_rule_checks+=1
  successor=next((entry[0] for entry in rounds if entry[0]['iteration']==r['iteration']+1),None)
  if successor is None:continue
  current=list(map(F,r['emphasis']));expected_next=None
  if m['arm']=='hard':
   saved=np.load(folder/f"round_{r['iteration']:03d}"/'decoders.npz')
   intervals=[(F.from_float(max(0.,float(lo))),F.from_float(min(1.,max(float(lo),float(hi))))) for lo,hi in zip(saved['lower'],saved['upper'])]
   logs=[math.log(float(w))+float((lo+hi)/2) for w,(lo,hi) in zip(current,intervals)];pivot=max(logs)
   rawweights=[F.from_float(math.exp(v-pivot)) for v in logs];total=sum(rawweights);expected_next=[w/total for w in rawweights]
  elif m['arm']=='tractability' and 'cost_scale' in r:
   if fixed_cost_scale is None:
    first=np.asarray(valid[0][0]['decoder_costs']);fixed_cost_scale=max(float(np.median(first[first>0])),1e-9)
   if r['cost_scale']!=fixed_cost_scale:raise ValueError('Tractability scale is not fixed initial median')
   scale=F.from_float(float(r['cost_scale']));rawweights=[F(1,K)/(1+F.from_float(float(c))/scale) for c in r['cumulative_decoder_costs']];total=sum(rawweights);expected_next=[w/total for w in rawweights]
  elif m['arm'] not in ['tractability','hard']:expected_next=[F(1,K)]*K
  if expected_next is not None:
   if list(map(F,successor['emphasis']))!=expected_next:raise ValueError('Next emphasis violates declared update rule')
   weight_rule_checks+=1
 # Realization averages must average executed policy weights, never conditional rows.
 averages=[]
 for p in sorted(folder.glob('average_*')):
  if p.name.startswith('average_checkpoint'):continue
  ar=json.loads((p/'record.json').read_text());pol=np.load(p/'policy.npz');rr,aw,leaf,E=policy_check(pol,layers,raw);residual=max(residual,rr)
  constituents=[v for v in valid if v[0]['iteration']<=ar['iteration']]
  if len(constituents)!=ar['iteration']+1:raise ValueError('Average omitted an accepted round')
  expected_average=sum((v[2] for v in constituents),np.zeros(P))/len(constituents);residual=max(residual,norm(aw-expected_average))
  rr,lo,hi=decode(np.load(p/'decoders.npz'),targets,E);residual=max(residual,rr);averages.append((ar,pol))
 endpoints=[]
 for limit in [2,10,40]:
  eligible=[v for v in valid if v[0]['available_seconds']<=limit];p=folder/f'checkpoint_{limit}'
  if not eligible:
   if p.exists():raise ValueError('Endpoint exists without timely audited evidence')
   if result['checkpoints'][str(limit)].get('status')!='no_in_budget_audited_policy':raise ValueError('Missing endpoint misreported')
  else:
   chosen=eligible[-1] if m['arm'] in ['tractability','hard'] else min(eligible,key=lambda v:v[5]);r,source,_,_,_,upper,lower=chosen
   pol=np.load(p/'policy.npz');meta=json.loads((p/'policy.json').read_text());residual=max(residual,norm(pol['rows']-source['rows']),norm(pol['E']-source['E']))
   if meta['iteration']!=r['iteration'] or meta['available_seconds']!=r['available_seconds']:raise ValueError('Wrong or backdated endpoint')
   residual=max(residual,abs(meta['selected_upper']-upper),abs(meta['selected_gap']-(meta['selected_upper']-meta['selected_lower'])))
   if meta['selected_lower']>lower+TOL:raise ValueError('Endpoint lower bound unsupported')
   if D!=1 and F(meta['omitted_mass'])!=beta:raise ValueError('Endpoint omitted tail erased')
   endpoints.append({'budget':limit,'iteration':r['iteration'],'selected_gap':meta['selected_gap'],'available_seconds':meta['available_seconds']})
  eligibleavg=[v for v in averages if v[0]['available_seconds']<=limit];p=folder/f'average_checkpoint_{limit}'
  if eligibleavg:
   ar,source=eligibleavg[-1];pol=np.load(p/'policy.npz');meta=json.loads((p/'policy.json').read_text());residual=max(residual,norm(pol['rows']-source['rows']))
   if meta['iteration']!=ar['iteration'] or meta['available_seconds']!=ar['available_seconds']:raise ValueError('Wrong average endpoint')
  elif p.exists():raise ValueError('Average endpoint lacks timely decoder evidence')
 if residual>TOL:raise ValueError(f'Planning replay residual {residual}')
 if result['status']=='converged' and (not valid or min(v[5] for v in valid)-max(v[6] for v in valid)>1e-6+TOL):raise ValueError('Convergence gap not closed')
 return {'status':'passed','arm':m['arm'],'residual':residual,'rounds':len(rounds),'accepted_rounds':len(valid),'cuts':len(cuts),'averages':len(averages),'endpoints':endpoints,'weight_rule_checks':weight_rule_checks,'cost_rule_checks':cost_rule_checks,'omitted_mass':str(beta) if kind=='native_weighted' else None,'seconds':time.perf_counter()-started,'scope':'Independent finite numerical replay; no eventual, all-optima or certified floating MW guarantee'}

def main():
 p=argparse.ArgumentParser();p.add_argument('folder',type=Path);p.add_argument('--model',type=Path);p.add_argument('--output',type=Path);args=p.parse_args()
 try:result=check(args.folder,args.model)
 except Exception as exc:result={'status':'failed','error':repr(exc)}
 result['checker_sha256']=sha(__file__);out=args.output or args.folder/'PLANNING_CHECK.json';out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
 if result['status']!='passed':raise SystemExit(1)
if __name__=='__main__':main()
