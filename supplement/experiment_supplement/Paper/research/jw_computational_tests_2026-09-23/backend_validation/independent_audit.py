"""Independent raw-probability, policy, cut and LP certificate reconstruction.

Imports no adapter/planner/decoder code and performs no optimization. Floating
arithmetic is bounded by residual tolerance; this is not exact rational proof.
"""
from pathlib import Path
from fractions import Fraction
import hashlib,itertools,json,re
import numpy as np
from scipy import sparse
TOL=2e-7
GAP=1e-6

def norm(x):return float(np.max(np.abs(x),initial=0))
def pos(x):return float(np.max(np.maximum(x,0),initial=0))
def matrix(z,key):return sparse.csr_matrix((z[key+'_data'],z[key+'_indices'],z[key+'_indptr']),shape=z[key+'_shape'])
def histories(t):return [list(itertools.product(itertools.product(range(2),repeat=2),repeat=d)) for d in range(t+1)]
def law(T,Z,h):
 v=[]
 for q in range(len(T)):
  s=np.zeros(T.shape[-1]);s[0]=1
  for a,o in h:s=(s@T[q,a])*Z[q,a,:,o]
  v.append(s.sum())
 return np.asarray(v)
def target(T,Z,n,index):
 bits=[(index>>k)&1 for k in range(2**n-2,-1,-1)];columns=[]
 for obs in itertools.product(range(2),repeat=n):
  h=[];node=0
  for o in obs:h.append((bits[node],o));node=2*node+1+o
  columns.append(law(T,Z,h))
 return np.stack(columns,axis=1)
def rational_target(T,Z,key):
 match=re.fullmatch(r'rational-native-v1/a2o2/n(\d+)/d(\d+)/r(\d+)',key)
 if match is None:raise ValueError('Unsupported rational target encoding')
 depth,denom,rank=map(int,match.groups());levels=histories(depth);decisions=sum(levels[:-1],[]);digits=[0]*len(decisions)
 for i in range(len(digits)-1,-1,-1):rank,digits[i]=divmod(rank,denom+1)
 if rank:raise ValueError('Rational target rank overflow')
 table={h:(float(Fraction(v,denom)),float(1-Fraction(v,denom))) for h,v in zip(decisions,digits)}
 columns=[]
 for h in levels[-1]:
  p=1.
  for i,(a,o) in enumerate(h):p*=table[h[:i]][a]
  columns.append(law(T,Z,h)*p)
 return np.stack(columns,axis=1)
def replay(rows,layers):
 decisions=sum(layers[:-1],[]);di={h:i for i,h in enumerate(decisions)};w={():1.};a=np.zeros(2*len(decisions))
 for h in decisions:
  for x in range(2):
   a[2*di[h]+x]=w[h]*rows[di[h],x]
   for o in range(2):w[h+((x,o),)]=a[2*di[h]+x]
 return a,np.asarray([w[h] for h in layers[-1]])
def decode(z,Fs,E):
 residual=0.;lo=[];hi=[]
 for j,F in enumerate(Fs):
  keep=z[f'witness_{j}_source_indices'];G=z[f'witness_{j}_decoder'];a=z[f'witness_{j}_alpha'];b=z[f'witness_{j}_b']
  if not np.array_equal(keep,np.flatnonzero(np.max(E,axis=0)>0)):raise ValueError('Omitted nonzero source signal')
  residual=max(residual,norm(G.sum(1)-1),pos(-G),abs(a.sum()-1),pos(-a),pos(-b),pos(b-a[:,None]))
  upper=float(np.max(abs(E[:,keep]@G-F).sum(1)/2));lower=float(np.sum(F*b)-np.max(E[:,keep].T@b,axis=1).sum())
  residual=max(residual,abs(upper-z['upper'][j]),abs(lower-z['lower'][j]),abs(upper-lower));lo.append(lower);hi.append(upper)
 return residual,np.asarray(lo),np.asarray(hi)
def lp(z):
 c=z['cost'];x=z['solution'];Ae=matrix(z,'A_eq');Au=matrix(z,'A_ub');be=z['b_eq'];bu=z['b_ub'];ye=z['eq_dual'];yu=z['ub_dual'];yl=z['lower_dual'];yh=z['upper_dual']
 if not all(np.isfinite(v).all() for v in [c,x,Ae.data,Au.data,be,bu,ye,yu,yl,yh]):raise ValueError('Nonfinite LP evidence')
 residual=max(norm(Ae@x-be),pos(Au@x-bu),pos(-x),pos(x-1),pos(yu),pos(-yl),pos(yh),norm(c-Ae.T@ye-Au.T@yu-yl-yh))
 yu=np.minimum(yu,0);remaining=c-Ae.T@ye-Au.T@yu;lower=float(be@ye+bu@yu+np.minimum(remaining,0).sum());upper=float(c@x)
 residual=max(residual,abs(upper-lower));return residual,lower,upper

def audit(folder):
 folder=Path(folder);m=json.loads((folder/'metadata.json').read_text());r=json.loads((folder/'result.json').read_text());inp=np.load(folder/'inputs.npz')
 T,Z=inp['T'],inp['Z'];layers=histories(m['t']);decisions=sum(layers[:-1],[]);di={h:i for i,h in enumerate(decisions)};P=2*len(decisions)
 raw=np.stack([law(T,Z,h) for h in layers[-1]],axis=1)
 if 'target_specs' in m:
  Fs=[rational_target(T,Z,s['key']) if s['kind']=='rational' else target(T,Z,s['depth'],s['index']) for s in m['target_specs']]
 else:Fs=[target(T,Z,m['n'],j) for j in m['target_indices']]
 leafidx=np.asarray([2*di[h[:-1]]+h[-1][0] for h in layers[-1]])
 residual=max([norm(raw-inp['raw'])]+[norm(F-inp[f'target_{j}']) for j,F in enumerate(Fs)])
 if not np.array_equal(leafidx,inp['leaf_index']):raise ValueError('Incorrect leaf realization map')
 # Every saved cache cut is reconstructed from its original alpha,b witness.
 cachepath=folder/'cache.json';witnesspath=folder/'witness_store.json';verified=[]
 if cachepath.exists():
  cache=json.loads(cachepath.read_text());witnesses=json.loads(witnesspath.read_text());binding=m['target_binding_ids'];lookup={v:i for i,v in enumerate(binding)}
  for item in cache['cuts']:
   c=item;targetid=c['target_identity'];idx=lookup.get(targetid)
   if idx is None:raise ValueError('Unbound cached target')
   w=witnesses[c['witness_sha256']]
   digest=hashlib.sha256(json.dumps(w,sort_keys=True,separators=(',',':'),allow_nan=False).encode()).hexdigest()
   if digest!=c['witness_sha256']:raise ValueError('Corrupt dual witness')
   a=np.asarray(w['alpha']);b=np.asarray(w['b']);s=np.asarray([float(Fraction(v)) for v in c['slope']]);inter=float(Fraction(c['intercept']))
   expected=np.bincount(leafidx,weights=np.max(raw.T@b,axis=1),minlength=P)
   residual=max(residual,abs(a.sum()-1),pos(-a),pos(-b),pos(b-a[:,None]),norm(s-expected),abs(inter-np.sum(Fs[idx]*b)))
   verified.append((idx,inter,s))
 # Check every saved master, not just the last or winning iteration.
 verified_keys={(int(i),float(v),np.asarray(s,dtype=float).tobytes()) for i,v,s in verified}
 lower=0.;masters=0
 for p in sorted(folder.glob('iteration_*/master.npz')):
  z=np.load(p);cuts=np.load(p.parent/'cuts.npz');rr,ll,uu=lp(z);residual=max(residual,rr);lower=max(lower,ll);masters+=1
  D=1 if m['kind']=='native_minimax' else len(Fs);weights=np.asarray([float(Fraction(w)) for w in m['weights']]);cost=np.r_[np.zeros(P),[1.] if D==1 else weights]
  residual=max(residual,norm(cost-z['cost']))
  Ae=matrix(z,'A_eq');expected=sparse.lil_matrix(Ae.shape);rhs=np.zeros(len(decisions));rhs[0]=1
  for i,h in enumerate(decisions):
   expected[i,2*i]=1;expected[i,2*i+1]=1
   if h:expected[i,2*di[h[:-1]]+h[-1][0]]=-1
  residual=max(residual,norm((Ae-expected.tocsr()).data),norm(z['b_eq']-rhs))
  Au=matrix(z,'A_ub');expected=sparse.lil_matrix(Au.shape)
  for j,(idx,inter,s) in enumerate(zip(cuts['targets'],cuts['intercepts'],cuts['slopes'])):
   expected[j,:P]=-s;expected[j,P+(0 if D==1 else int(idx))]=-1
   if cachepath.exists() and (int(idx),float(inter),np.asarray(s,dtype=float).tobytes()) not in verified_keys:raise ValueError('Master cut lacks reconstructed witness')
  residual=max(residual,norm((Au-expected.tocsr()).data),norm(z['b_ub']+cuts['intercepts']))
  pol=np.load(p.parent/'policy.npz');_,w=replay(pol['rows'],layers);E=raw*w;residual=max(residual,norm(E-pol['E']),norm(pol['rows'].sum(1)-1),pos(-pol['rows']))
  if (p.parent/'decoders.npz').exists():
   rr,_,_=decode(np.load(p.parent/'decoders.npz'),Fs,E);residual=max(residual,rr)
 upper=None
 if (folder/'policy.npz').exists():
  pol=np.load(folder/'policy.npz');_,w=replay(pol['rows'],layers);E=raw*w
  residual=max(residual,norm(E-pol['E']),norm(w-pol['leaf']),norm(E.sum(1)-1),norm(pol['rows'].sum(1)-1),pos(-pol['rows']))
  rr,los,his=decode(np.load(folder/'selected_decoders.npz'),Fs,E);residual=max(residual,rr)
  weights=np.asarray([float(Fraction(v)) for v in m['weights']]);upper=float(max(his) if m['kind']=='native_minimax' else weights@his)
 if (folder/'monolithic_certificate.npz').exists():
  rr,ll,uu=lp(np.load(folder/'monolithic_certificate.npz'));residual=max(residual,rr);lower=max(lower,ll)
  # Full formulation is independently bound below by decoded feasible upper;
  # a separate structural constructor verifies monolithic matrices.
  from monolithic_structure import check_structure
  residual=max(residual,check_structure(np.load(folder/'monolithic_certificate.npz'),raw,Fs,leafidx,layers,weights,m['kind']))
 if r.get('certificate'):
  cert=r['certificate'];stated=float(Fraction(cert['selected_policy_loss_interval'][1]));statedlower=stated-float(Fraction(cert['full_finite_regret_upper']))
  # Decoder interval padding and exact cost rounding are intentionally conservative.
  if stated+TOL<upper or statedlower>lower+TOL:raise ValueError('Unsupported exported objective bound')
 if residual>TOL:raise ValueError(f'Independent arithmetic residual {residual}')
 gap=None if upper is None else upper-lower
 complete=r['status'] in ['converged','converged_numerically','passed']
 if complete and (gap is None or gap>GAP+TOL or gap<-TOL):raise ValueError(f'Unclosed objective gap {gap}')
 return dict(status='passed',residual=residual,lower=lower,upper=upper,gap=gap,masters=masters,cuts=len(verified),complete=complete,
  scope='Independent finite numerical replay; not exact arithmetic or eventual J_w')
