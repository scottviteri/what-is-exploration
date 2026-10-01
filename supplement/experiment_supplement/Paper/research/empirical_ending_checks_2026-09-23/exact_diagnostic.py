"""Rational physical replay and kernel-checkable certificates for a named reversal.
The new rational policies approximate the archived planner rows; they are not
silently identified with those floating-point experiments or their optima.
"""
from fractions import Fraction as R
from pathlib import Path
import json,hashlib,math
import numpy as np
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2]
DEN=10**6

def norm(row):
    a=[R(str(float(x))).limit_denominator(10**6) for x in row];s=sum(a);return [x/s for x in a]
def simplex(row):
    a=np.maximum(np.asarray(row,float),0);a/=a.sum();v=np.floor(DEN*a).astype(int);left=DEN-int(v.sum())
    for i in np.argsort(-(DEN*a-v),kind='stable')[:left]:v[i]+=1
    assert sum(v)==DEN
    return [R(int(x),DEN) for x in v]
def physical(model,policy):
    with np.load(model) as z:t=z['T'];z0=z['Z']
    with np.load(policy) as z:rows0=z['rows'];saved=z['E']
    rows=[simplex(x) for x in rows0];T=[[[norm(row) for row in a] for a in q] for q in t];Z=[[[norm(row) for row in a] for a in q] for q in z0]
    Q=len(T);S=len(T[0][0]);out=[[R(0) for _ in range(64)] for q in range(Q)]
    for col in range(64):
        w=R(1);state=[[R(int(i==0)) for i in range(S)] for _ in range(Q)];prefix=0
        for d in range(3):
            digit=(col//4**(2-d))%4;a,o=divmod(digit,2);w*=rows[(4**d-1)//3+prefix][a];prefix=4*prefix+digit
            state=[[sum(state[q][s]*T[q][a][s][u] for s in range(S))*Z[q][a][u][o] for u in range(S)] for q in range(Q)]
        for q in range(Q):out[q][col]=w*sum(state[q])
    assert all(sum(x)==1 and min(x)>=0 for x in out)
    keep=[i for i in range(64) if any(row[i]>0 for row in out)]
    return [[row[i] for i in keep] for row in out],keep,dict(max_probability_row_change=float(np.max(abs(np.array(rows,dtype=float)-rows0))),experiment_TV_change=float(np.max(abs(np.array(out,float)-saved).sum(1))/2)),dict(T=T,Z=Z,rows=rows)
def show(x):
    if isinstance(x,(list,tuple)):return '!['+', '.join(show(y) for y in x)+']'
    if x.denominator==1:return str(x.numerator)
    return f'({x.numerator} / {x.denominator})'
def serial(x):
    if isinstance(x,dict):return {k:serial(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [serial(v) for v in x]
    if isinstance(x,R):return str(x)
    return x

d=json.loads((HERE/'REWARD_DIAGNOSTICS.json').read_text());rr=d['records']; case='delayed_0.25_0.1'
a={m:sorted([r for r in rr if r['case']==case and r['method']==m],key=lambda r:r['cell'])[0] for m in ['weighted128','brier']}
e={m:physical(r['model'],r['policy']) for m,r in a.items()}
orders=json.loads((HERE/'order/RESULTS.json').read_text())['records'];data={};clauses=[]
header='''import Formal.EmpiricalEndingCertificates\n\n/-! Exact finite-experiment certificates for explicitly specified rational\nreplays of the delayed example. The Python physical-model derivation and its\nbinding to archived policies are separately checked; Lean checks these tables\nand every rational certificate inequality without trusting the LP solver.\nThese claims are neither all-optima results nor a depth-four audit theorem. -/\nnamespace IdExp.EmpiricalEnding.Delayed\nopen Finset\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'''
text=header
for m,name in [('weighted128','nativeE'),('brier','brierE')]:
    E,keep,_,_=e[m];text+=f'\ndef {name} : Fin {len(E)} → Fin {len(keep)} → ℚ :=\n  {show(E)}\n'
    text+=f'\ntheorem {name}_valid : RatRows {name} := by\n  unfold RatRows {name}\n  decide +kernel\n'
for src,tgt,name,en,fn in [('weighted128','brier','forward','nativeE','brierE'),('brier','weighted128','reverse','brierE','nativeE')]:
    item=next(r for r in orders if r['case']==case and r['source_method']==src and r['target_method']==tgt)
    E,ek,_,_=e[src];F,fk,_,_=e[tgt];Q=len(E);X=len(ek);Y=len(fk)
    with np.load(item['witness']) as z:
        alpha=simplex(z['alpha']);bb=z['b'];Gfull=np.zeros((64,64));Gfull[z['source_indices']]=z['G'];G=[simplex(Gfull[i,fk]) for i in ek]
    # Rescale each bounded decision function to the rationalized world weight.
    olda=np.array([float(x) for x in np.load(item['witness'])['alpha']]);b=[]
    for q in range(Q):b.append([alpha[q]*R(int(round(DEN*min(1.,max(0.,bb[q,j]/olda[q])))),DEN) if olda[q]>0 else R(0) for j in fk])
    mu=[[alpha[q]-b[q][y] for y in range(Y)] for q in range(Q)]
    floor=[min(sum(mu[q][y]*E[q][x] for q in range(Q)) for y in range(Y)) for x in range(X)]
    lo=sum(floor)-sum(mu[q][y]*F[q][y] for q in range(Q) for y in range(Y))
    hi=max(sum(abs(sum(E[q][x]*G[x][y] for x in range(X))-F[q][y]) for y in range(Y))/2 for q in range(Q))
    low=R(math.floor(lo*10000),10000);up=R(math.ceil(hi*10000),10000)
    assert 0<low<=lo<=hi<=up
    vals={'lambda':(alpha,f'Fin {Q} → ℚ'),'mu':(mu,f'Fin {Q} → Fin {Y} → ℚ'),'floor':(floor,f'Fin {X} → ℚ'),'decoder':(G,f'Fin {X} → Fin {Y} → ℚ')}
    for key,(v,typ) in vals.items():text+=f'\ndef {name}_{key} : {typ} :=\n  {show(v)}\n'
    text+=f'''\ndef {name}Checks : Prop :=\n  (∀ q, 0 ≤ {name}_lambda q) ∧\n  (∑ q, {name}_lambda q = 1) ∧\n  (∀ q y, 0 ≤ {name}_mu q y) ∧\n  (∀ q y, {name}_mu q y ≤ {name}_lambda q) ∧\n  (∀ x y, {name}_floor x ≤ ∑ q, {name}_mu q y * {en} q x) ∧\n  ({show(low)} : ℚ) ≤ (∑ x, {name}_floor x) - ∑ q, ∑ y, {name}_mu q y * {fn} q y\n\ntheorem {name}_checked : {name}Checks := by\n  unfold {name}Checks {name}_lambda {name}_mu {name}_floor {en} {fn}\n  decide +kernel\n\ntheorem {name}_lower : ({show(low)} : ℝ) ≤ finiteDeficiency (realRows {en}) (realRows {fn}) := by\n  obtain ⟨h0, h1, hm0, hml, hf, hv⟩ := {name}_checked\n  have hh := rational_lower_bound {en} {fn} {en}_valid {fn}_valid\n    {name}_lambda h0 h1 {name}_mu hm0 hml {name}_floor hf _ hv\n  norm_num at hh ⊢\n  exact hh\n\ndef {name}UpperChecks : Prop :=\n  RatRows {name}_decoder ∧\n  (∀ q, (∑ y, |(∑ x, {en} q x * {name}_decoder x y) - {fn} q y|) ≤ 2 * ({show(up)} : ℚ))\n\ntheorem {name}_upper_checked : {name}UpperChecks := by\n  unfold {name}UpperChecks RatRows {name}_decoder {en} {fn}\n  decide +kernel\n\ntheorem {name}_upper : finiteDeficiency (realRows {en}) (realRows {fn}) ≤ ({show(up)} : ℝ) := by\n  have hh := rational_upper_bound {en} {fn} {name}_decoder\n    {name}_upper_checked.1 _ {name}_upper_checked.2\n  norm_num at hh ⊢\n  exact hh\n'''
    data[name]=dict(source=src,target=tgt,lower=low,upper=up,exact_lower=lo,exact_upper=hi,source_keep=ek,target_keep=fk,source_policy=a[src]['policy'],target_policy=a[tgt]['policy'],archived_witness=item['witness'])
text+='''\ntheorem records_incomparable :\n    0 < finiteDeficiency (realRows nativeE) (realRows brierE) ∧\n    0 < finiteDeficiency (realRows brierE) (realRows nativeE) := by\n  exact incomparable_of_positive_bounds _ _ _ _ (by norm_num) (by norm_num)\n    forward_lower reverse_lower\nend IdExp.EmpiricalEnding.Delayed\n'''
path=ROOT/'Formal/Formal/EmpiricalEndingDelayed.lean';path.write_text(text)
(HERE/'EXACT_DIAGNOSTIC.json').write_text(json.dumps(serial(dict(status='rational_arithmetic_passed_lean_pending',case=case,quantization_denominator=DEN,certificates=data,replay={m:dict(diagnostics=x[2],physical=x[3]) for m,x in e.items()},data_module=str(path),data_module_sha256=hashlib.sha256(path.read_bytes()).hexdigest())),indent=2)+'\n')
print(json.dumps(serial({k:{x:v[x] for x in ['lower','upper','source','target']} for k,v in data.items()})),len(text),'Lean characters')
