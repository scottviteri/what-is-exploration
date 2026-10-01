#!/usr/bin/env python3
"""Independent exact-rational replay of stored compressed LP certificates."""
import os
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'): os.environ[k]='1'
import concurrent.futures,gzip,hashlib,json,math,time
from collections import defaultdict
from fractions import Fraction as R
from pathlib import Path
BASE=Path(__file__).resolve().parent

def frac(z):return R(int(z['num']),int(z['den']))
def prepare(r):
    e=R(r['eps_num'],r['eps_den']);ps=defaultdict(R)
    for m in range(r['M']+1):
        for j in range(2**m+1):ps[R(j,2**m)]+=R(3,4**(m+1)*(2**m+1))
    weights=defaultdict(R)
    for n in range(1,r['N']+1):
        for p,v in ps.items():weights[n,p]+=e*v/2**n
    weights[1 if r['schedule']=='fixed' else r['H'],R(0)]+=1-e
    def bitset(t,s):
        z=set(range((t+1)//2)) if s==0 else set(range(1,t+1))
        if r['d'] is not None:z.intersection_update(range(r['d']))
        return z
    source=[bitset(r['H'],s) for s in (0,1)];ts=[]
    for (n,p),w in sorted(weights.items()):
        target=[bitset(n,s) for s in (0,1)]
        a=[R(1,2**len(target[s]-source[t])) for t in (0,1) for s in (0,1)]
        ts.append((p,w,a))
    return ts

def replay_dual(wit,ts,objective,threshold=None):
    nv=1+6*len(ts);cost=[R(0)]*nv;lower=[R(0)]*nv;upper=[R(1)]*nv
    if objective in ('minq','maxq'):cost[0]=R(1 if objective=='minq' else -1)
    for i,(p,w,a) in enumerate(ts):
        upper[1+6*i+4]=p;upper[1+6*i+5]=1-p
        if objective=='loss':cost[1+6*i+4]=cost[1+6*i+5]=-w
    residual=cost[:];dual_constant=R(0)
    eq=[R(float(v)) for v in wit['dual_eq']];ub=[min(R(0),R(float(v))) for v in wit['dual_ub']]
    # Walk actual constraint rows, without the production closed-form reduction.
    for i,(p,w,a) in enumerate(ts):
        z=1+6*i
        for row,rhs,entries in [(2*i,R(0),[(z,R(1)),(z+1,R(1)),(0,R(-1))]),(2*i+1,R(1),[(z+2,R(1)),(z+3,R(1)),(0,R(1))])]:
            dual_constant+=eq[row]*rhs
            for j,v in entries:residual[j]-=eq[row]*v
        for row,entries in [(2*i,[(z+4,R(1)),(z,-a[0]),(z+2,-a[2])]),(2*i+1,[(z+5,R(1)),(z+1,-a[1]),(z+3,-a[3])])]:
            for j,v in entries:residual[j]-=ub[row]*v
    if objective!='loss':
        dual_constant+=ub[-1]*threshold
        for i,(p,w,a) in enumerate(ts):
            residual[1+6*i+4]-=ub[-1]*(-w);residual[1+6*i+5]-=ub[-1]*(-w)
    bound=dual_constant+sum(min(v*l,v*u) for v,l,u in zip(residual,lower,upper))
    return bound+(sum(w for p,w,a in ts) if objective=='loss' else 0)

def replay_candidate(wit,ts):
    raw=wit['x'];q=min(R(1),max(R(0),R(float(raw[0]))));value=R(0)
    for i,(p,w,a) in enumerate(ts):
        z=1+6*i;x=[max(R(0),R(float(v))) for v in raw[z:z+4]]
        for offset,mass in [(0,q),(2,1-q)]:
            den=x[offset]+x[offset+1]
            if den:x[offset],x[offset+1]=mass*x[offset]/den,mass*x[offset+1]/den
            else:x[offset],x[offset+1]=mass,R(0)
        overlap=min(p,a[0]*x[0]+a[2]*x[2])+min(1-p,a[1]*x[1]+a[3]*x[3])
        assert 0<=overlap<=1
        value+=w*(1-overlap)
    return q,value

def one(path):
    r=json.load(gzip.open(path,'rt'))
    try:
        assert r['status']=='passed';ts=prepare(r);mass=sum(w for p,w,a in ts)
        tail=R(r['eps_num'],r['eps_den'])*(1-(1-R(1,2**r['N']))*(1-R(1,4**(r['M']+1))))
        assert mass+tail==1 and tail==frac(r['omitted_weight'])
        q,U=replay_candidate(r['witnesses']['minimum'],ts);B=replay_dual(r['witnesses']['minimum'],ts,'loss')
        assert B<=U and U==frac(r['candidate_retained_upper']) and B==frac(r['retained_lower'])
        rhs=U+tail+frac(r['range_slack'])-mass
        lo=max(R(0),replay_dual(r['witnesses']['min_q_sublevel'],ts,'minq',rhs))
        hi=min(R(1),-replay_dual(r['witnesses']['max_q_sublevel'],ts,'maxq',rhs))
        assert lo==frac(r['all_full_optima_q_outer'][0]) and hi==frac(r['all_full_optima_q_outer'][1])
        assert 0<=lo<=q<=hi<=1
        assert (1-hi)/2==frac(r['all_full_optima_safe1_loss_outer'][0])
        assert (1-lo)/2==frac(r['all_full_optima_safe1_loss_outer'][1])
        assert U+tail-B==frac(r['candidate_full_regret_bound'])
        if r['d'] is not None:
            h,d=r['H'],r['d'];s=min((h+1)//2,d);f=min(h,d-1)
            assert r['information_gain']['all_optimal_q']==([1,1] if s>f else [0,0] if s<f else [0,1])
            if h>=2*d-1:assert hi==1 and lo<=1 and q==1
        return {'id':r['id'],'status':'passed','sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'primal_dual_gap':float(U-B),'full_regret_bound':float(U+tail-B)}
    except Exception as e:return {'id':r.get('id',str(path)),'status':'failed','error':repr(e)}

def init():
    import multiprocessing
    os.sched_setaffinity(0,{12+(multiprocessing.current_process()._identity[0]-1)%4})

def main():
    start=time.monotonic();files=sorted((BASE/'cells').glob('*.json.gz'))
    with concurrent.futures.ProcessPoolExecutor(4,initializer=init) as pool:rows=list(pool.map(one,files,chunksize=8))
    report={'status':'passed' if all(x['status']=='passed' for x in rows) else 'failed','arithmetic':'exact fractions of stored float primal/dual entries against original rational model coefficients','cells':len(rows),'elapsed_seconds':time.monotonic()-start,'failures':[x for x in rows if x['status']!='passed'],'max_retained_primal_dual_gap':max((r.get('primal_dual_gap',0) for r in rows),default=0),'rows':rows,'audit_source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (BASE/'AUDIT.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k not in ('rows','failures')}));print('failures',report['failures'][:5])
if __name__=='__main__':main()
