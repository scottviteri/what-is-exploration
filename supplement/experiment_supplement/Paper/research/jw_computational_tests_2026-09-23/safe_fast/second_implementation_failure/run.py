#!/usr/bin/env python3
"""Prospectively specified SAFE/FAST exact-tail LP study; no GPU or learning."""
import os
for _k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','HIGHS_THREADS'):
    os.environ[_k]='1'
import argparse, concurrent.futures, gzip, hashlib, itertools, json, math, resource, time, warnings
from collections import defaultdict
from fractions import Fraction as F
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix, vstack
BASE=Path(__file__).resolve().parent
OPT={'dual_feasibility_tolerance':1e-9,'primal_feasibility_tolerance':1e-9,'threads':1}
warnings.filterwarnings('ignore',message='Unrecognized options detected')
SLACK=F(1,10**9)

def fj(x):
    x=F(x); return {'num':str(x.numerator),'den':str(x.denominator),'float':float(x)}
def dump(path,x):
    path.parent.mkdir(parents=True,exist_ok=True)
    if str(path).endswith('.gz'):
        with gzip.open(path,'wt') as f: json.dump(x,f,separators=(',',':'))
    else: path.write_text(json.dumps(x,indent=2)+'\n')
def bits(h,d,safe):
    v=set(range((h+1)//2)) if safe else set(range(1,h+1))
    return v if d is None else {i for i in v if i<d}
def coeff(h,n,d):
    aa=[bits(h,d,True),bits(h,d,False)]; bb=[bits(n,d,True),bits(n,d,False)]
    return [F(1,2**len(bb[s]-aa[r])) for r in range(2) for s in range(2)]
def target_list(h,eps,schedule,N,M):
    ps=defaultdict(F)
    for m in range(M+1):
        k=2**m
        for j in range(k+1): ps[F(j,k)]+=F(3,4**(m+1)*(k+1))
    rows=defaultdict(F)
    for n in range(1,N+1):
        for p,w in ps.items(): rows[(n,p)]+=eps*F(1,2**n)*w
    rows[(1 if schedule=='fixed' else h,F(0))]+=1-eps
    return [(n,p,w) for (n,p),w in sorted(rows.items()) if w]
def matrices(targets,h,d):
    k=len(targets); nv=1+6*k; er=[];ec=[];ev=[]; ur=[];uc=[];uv=[]
    be=np.zeros(2*k); bu=np.zeros(2*k); c=np.zeros(nv); bounds=[(0,1)]; cf=[]
    for i,(n,p,w) in enumerate(targets):
        z=1+6*i; a=coeff(h,n,d); cf.append(a)
        for row,cols,vals in [(2*i,[z,z+1,0],[1,1,-1]),(2*i+1,[z+2,z+3,0],[1,1,1])]:
            er.extend([row]*3);ec.extend(cols);ev.extend(vals)
        be[2*i+1]=1
        for row,cols,vals in [(2*i,[z+4,z,z+2],[1,-float(a[0]),-float(a[2])]),(2*i+1,[z+5,z+1,z+3],[1,-float(a[1]),-float(a[3])])]:
            ur.extend([row]*3);uc.extend(cols);uv.extend(vals)
        c[z+4]=c[z+5]=-float(w)
        bounds.extend([(0,1)]*4+[(0,float(p)),(0,float(1-p))])
    ae=coo_matrix((ev,(er,ec)),shape=(2*k,nv)).tocsr()
    au=coo_matrix((uv,(ur,uc)),shape=(2*k,nv)).tocsr()
    return c,ae,be,au,bu,bounds,cf

def exact_candidate(x,targets,cf):
    q=min(F(1),max(F(0),F(float(x[0])))); total=F(0)
    for i,((n,p,w),a) in enumerate(zip(targets,cf)):
        raw=[max(F(0),F(float(v))) for v in x[1+6*i:5+6*i]]; xx=[]
        for row,mass in [(raw[:2],q),(raw[2:],1-q)]:
            den=sum(row);xx.extend([mass*v/den for v in row] if den else [mass,F(0)])
        ys=min(p,a[0]*xx[0]+a[2]*xx[2]); yf=min(1-p,a[1]*xx[1]+a[3]*xx[3])
        total+=w*(1-ys-yf)
    return q,total

def exact_dual(res,targets,cf,kind='loss',threshold=None):
    """Exact bound from arbitrary float duals, via box residual correction."""
    lam=[F(float(v)) for v in res.eqlin.marginals]
    mu=[min(F(0),F(float(v))) for v in res.ineqlin.marginals]
    psi=mu[-1] if kind!='loss' else F(0)
    base=sum(lam[1::2]); rq=F(1 if kind=='minq' else -1 if kind=='maxq' else 0)
    if kind!='loss': base+=psi*threshold
    for i,((n,p,w),a) in enumerate(zip(targets,cf)):
        ls,lf=lam[2*i:2*i+2]; ms,mf=mu[2*i:2*i+2]; rq+=ls-lf
        rr=[-ls-ms*a[0],-ls-mf*a[1],-lf-ms*a[2],-lf-mf*a[3]]
        base+=sum(min(F(0),v) for v in rr)
        cy=-w if kind=='loss' else psi*w
        base+=p*min(F(0),cy-ms)+(1-p)*min(F(0),cy-mf)
    base+=min(F(0),rq)
    if kind=='loss':base+=sum(w for n,p,w in targets)
    return base

def solve(c,ae,be,au,bu,bounds):
    r=linprog(c,A_ub=au,b_ub=bu,A_eq=ae,b_eq=be,bounds=bounds,method='highs',options=OPT)
    if not r.success: raise RuntimeError(f'LP failure {r.status}: {r.message}')
    return r

def witness(r):
    return {'x':r.x.tolist(),'dual_eq':r.eqlin.marginals.tolist(),'dual_ub':r.ineqlin.marginals.tolist(),'fun':float(r.fun),'nit':int(r.nit)}
def case_id(c):
    return f"{c['schedule']}_e{c['eps_num']}of{c['eps_den']}_d{c['d'] or 'inf'}_H{c['H']}_N{c['N']}_M{c['M']}"
def run_case(case):
    start=time.monotonic(); ident=case_id(case)
    try:
        h,d,N,M=case['H'],case['d'],case['N'],case['M'];eps=F(case['eps_num'],case['eps_den'])
        ts=target_list(h,eps,case['schedule'],N,M); c,ae,be,au,bu,bounds,cf=matrices(ts,h,d)
        mass=sum(w for n,p,w in ts);beta=1-(1-F(1,2**N))*(1-F(1,4**(M+1)));tail=eps*beta
        assert mass+tail==1
        t0=time.monotonic(); r=solve(c,ae,be,au,bu,bounds);solver_sec=time.monotonic()-t0
        q,U=exact_candidate(r.x,ts,cf);B=exact_dual(r,ts,cf); assert B<=U
        threshold=U+tail+SLACK-mass
        # Rounding/slack affects the solver's proposed multipliers only; exact dual replay
        # below uses the exact threshold and exact original coefficient weights.
        aug=vstack([au,coo_matrix(c.reshape(1,-1))]).tocsr();baug=np.r_[bu,math.nextafter(float(threshold),math.inf)]
        cr=np.zeros_like(c);cr[0]=1
        t0=time.monotonic();rlo=solve(cr,ae,be,aug,baug,bounds);rhi=solve(-cr,ae,be,aug,baug,bounds);solver_sec+=time.monotonic()-t0
        qlo=max(F(0),exact_dual(rlo,ts,cf,'minq',threshold));qhi=min(F(1),-exact_dual(rhi,ts,cf,'maxq',threshold));assert qlo<=qhi
        out={**case,'id':ident,'status':'passed','targets':len(ts),'variables':len(c),'omitted_background':fj(beta),'omitted_weight':fj(tail),'retained_mass':fj(mass),'candidate_q':fj(q),'retained_lower':fj(B),'candidate_retained_upper':fj(U),'full_optimum_lower':fj(B),'full_optimum_upper':fj(U+tail),'candidate_full_regret_bound':fj(U+tail-B),'range_slack':fj(SLACK),'all_full_optima_q_outer':[fj(qlo),fj(qhi)],'all_full_optima_safe1_loss_outer':[fj((1-qhi)/2),fj((1-qlo)/2)],'solver_seconds':solver_sec,'elapsed_seconds':time.monotonic()-start,'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'witnesses':{'minimum':witness(r),'min_q_sublevel':witness(rlo),'max_q_sublevel':witness(rhi)}}
        if d is not None:
            a=min((h+1)//2,d);b=min(h,d-1)
            out['information_gain']={'safe_bits':a,'fast_bits':b,'all_optimal_q':[1,1] if a>b else [0,0] if a<b else [0,1],'max_bits':max(a,b)}
            out['analytic_native_saturation']=h>=2*d-1
            if h>=2*d-1:
                assert qhi>=1 and qlo<=1
                out['analytic_native_all_optimal_q']=[1,1]
        else:
            out['lean_moving_all_optima_lower'] = fj((1-3*eps)/(2*(1-eps))) if case['schedule']=='moving' else None
        dump(BASE/'cells'/f'{ident}.json.gz',out)
        return {k:v for k,v in out.items() if k!='witnesses'}
    except Exception as e:
        out={**case,'id':ident,'status':'failed','error':repr(e),'elapsed_seconds':time.monotonic()-start}
        dump(BASE/'cells'/f'{ident}.json.gz',out);return out

def stream(world,safe,k):
    idx=k//2 if safe else k+1
    return 0 if safe and k%2 else world[idx] if idx<len(world) else 0

def full_records(h,d,q,seed=None):
    worlds=list(itertools.product((0,1),repeat=d)); rows=[];signals=set()
    for world in worlds:
        row={():1.0}
        for t in range(h):
            nxt=defaultdict(float)
            for hist,mass in row.items():
                if t==0: prob=float(q)
                elif seed is None: prob=1.0
                else:
                    word=f'{seed}:{hist}'.encode();prob=(int.from_bytes(hashlib.sha256(word).digest()[:4],'big')%5)/4
                for safe,p in [(1,prob),(0,1-prob)]:
                    if p:
                        branch=safe if t==0 else hist[0][0]
                        obs=stream(world,branch,t);nxt[hist+((safe,obs),)]+=mass*p
            row=dict(nxt)
        rows.append(row);signals.update(row)
    signals=sorted(signals);return np.array([[row.get(s,0) for s in signals] for row in rows]),signals

def literal_lp(E,T):
    W,X=E.shape;Y=T.shape[1];nv=X*Y+W*Y+1;delta=nv-1
    er=[];ec=[];ev=[]
    for x in range(X):
        er.extend([x]*Y);ec.extend(range(x*Y,(x+1)*Y));ev.extend([1]*Y)
    ae=coo_matrix((ev,(er,ec)),shape=(X,nv)).tocsr();be=np.ones(X)
    ur=[];uc=[];uv=[];bu=[];row=0
    for w in range(W):
        for y in range(Y):
            for sign in (1,-1):
                xs=np.flatnonzero(E[w]);ur.extend([row]*(len(xs)+1));uc.extend([int(x)*Y+y for x in xs]+[X*Y+w*Y+y]);uv.extend([sign*E[w,x] for x in xs]+[-1]);bu.append(sign*T[w,y]);row+=1
        ur.extend([row]*(Y+1));uc.extend(list(range(X*Y+w*Y,X*Y+(w+1)*Y))+[delta]);uv.extend([.5]*Y+[-1]);bu.append(0);row+=1
    au=coo_matrix((uv,(ur,uc)),shape=(row,nv)).tocsr();bu=np.array(bu);c=np.zeros(nv);c[delta]=1
    r=solve(c,ae,be,au,bu,[(0,1)]*nv)
    G=np.maximum(0,r.x[:X*Y].reshape(X,Y));G/=G.sum(axis=1)[:,None]
    upper=float(np.max(.5*np.abs(E@G-T).sum(axis=1)))
    lam=r.eqlin.marginals;mu=np.minimum(0,r.ineqlin.marginals)
    residual=c-ae.T@lam-au.T@mu;lower=float(be@lam+bu@mu+np.minimum(0,residual).sum())
    return r,upper,lower,{'E':E.tolist(),'T':T.tolist(),'G':G.tolist(),'dual_eq':lam.tolist(),'dual_ub':mu.tolist(),'lower_numeric':lower,'upper_replay':upper,'numeric_safety':1e-9}

def run_crosschecks():
    specifications=[]
    for h,n,d,q,p in itertools.product((1,2,3),(1,2,3),(1,2,3),(F(0),F(1,2),F(1)),(F(0),F(1,2),F(1))):specifications.append((h,n,d,q,p,None))
    for h,n,q,p in itertools.product((1,2,3),(1,2,3),(F(0),F(1,2),F(1)),(F(0),F(1,2),F(1))):specifications.append((h,n,max(h,n)+1,q,p,None))
    for i in range(32):specifications.append((2+i%2,2+(i//2)%2,2+(i//4)%2,F(i%5,4),F((i//5)%5,4),20260923+i))
    rows=[]; start=time.monotonic()
    for idx,(h,n,d,q,p,seed) in enumerate(specifications):
        E,se=full_records(h,d,q,seed);T,st=full_records(n,d,p,None if seed is None else seed+1000)
        ts=[(n,p,F(1))];c,ae,be,au,bu,bounds,cf=matrices(ts,h,d);bounds[0]=(float(q),float(q));r=solve(c,ae,be,au,bu,bounds);v=1+float(r.fun)
        rr,up,lo,wit=literal_lp(E,T);err=abs(v-float(rr.fun));passed=err<1e-8 and lo-1e-9<=v<=up+1e-9 and up-lo<1e-8
        row={'index':idx,'t':h,'n':n,'d':d,'q':str(q),'p':str(p),'later_seed':seed,'compressed':v,'literal':float(rr.fun),'absolute_difference':err,'literal_lower':lo,'literal_replayed_upper':up,'status':'passed' if passed else 'failed','source_signals':len(se),'target_signals':len(st)}
        dump(BASE/'crosscheck_witnesses'/f'{idx:03d}.json.gz',{**row,'compressed_witness':witness(r),'literal_witness':wit});rows.append(row)
    out={'status':'passed' if all(r['status']=='passed' for r in rows) else 'failed','cases':len(rows),'max_value_difference':max(r['absolute_difference'] for r in rows),'elapsed_seconds':time.monotonic()-start,'rows':rows}
    dump(BASE/'crosschecks.json',out);return out

def init_worker():
    import multiprocessing
    os.sched_setaffinity(0,{12+(multiprocessing.current_process()._identity[0]-1)%4})
    resource.setrlimit(resource.RLIMIT_AS,(4*1024**3,4*1024**3))

def grid():
    hs=list(range(1,33))+[48,64,96,128];sens=[1,2,4,8,16,32,64,128];out=[]
    for N,M,Hs,kind in [(12,4,hs,'primary'),(8,4,sens,'sensitivity'),(16,4,sens,'sensitivity'),(12,2,sens,'sensitivity'),(12,6,sens,'sensitivity')]:
        for h,d,e,s in itertools.product(Hs,(None,1,2,4,8,16),(F(1,100),F(1,20),F(1,4)),('fixed','moving')):
            out.append({'H':h,'d':d,'eps_num':e.numerator,'eps_den':e.denominator,'schedule':s,'N':N,'M':M,'grid':kind})
    return out

def main():
    pa=argparse.ArgumentParser();pa.add_argument('--crosschecks-only',action='store_true');pa.add_argument('--skip-crosschecks',action='store_true');pa.add_argument('--workers',type=int,default=4);args=pa.parse_args()
    os.sched_setaffinity(0,{12,13,14,15})
    tasks=grid();dump(BASE/'GRID.json',tasks)
    sources=[BASE/'PROTOCOL.md',BASE/'DERIVATION.md',Path(__file__),Path('Formal/Formal/AdaptiveNativeSafeFastOptimization.lean'),Path('Formal/Formal/AdaptiveNativeSafeFastCapability.lean'),Path('Formal/Formal/AdaptiveNativeOptimizationLimit.lean'),Path('Formal/Formal/AdaptiveNativeCertificates.lean'),Path('Paper/lit/pdf/review_2026-09-13/orseau2013universal_0.pdf')]
    dump(BASE/'RUN_METADATA.json',{'started_unix':time.time(),'cpu_affinity':[12,13,14,15],'workers':args.workers,'gpu':False,'source_sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},'grid_cells':len(tasks),'solver':'scipy.linprog highs','scipy_version':__import__('scipy').__version__})
    if not args.skip_crosschecks:
        cc=run_crosschecks();print(json.dumps({k:v for k,v in cc.items() if k!='rows'}),flush=True)
        if cc['status']!='passed': raise SystemExit('Compressed derivation crosscheck failed; primary grid not started.')
    if args.crosschecks_only:return
    start=time.monotonic();out=[]
    with concurrent.futures.ProcessPoolExecutor(args.workers,initializer=init_worker) as pool:
        for i,r in enumerate(pool.map(run_case,tasks,chunksize=3)):
            out.append(r)
            if (i+1)%72==0: print(json.dumps({'complete':i+1,'total':len(tasks),'failed':sum(x['status']!='passed' for x in out),'elapsed':time.monotonic()-start}),flush=True)
    dump(BASE/'RESULTS.json',{'status':'passed' if all(r['status']=='passed' for r in out) else 'failed','cells':len(out),'elapsed_seconds':time.monotonic()-start,'rows':out})
    print(json.dumps({'finished':len(out),'failed':sum(r['status']!='passed' for r in out),'elapsed':time.monotonic()-start}),flush=True)
if __name__=='__main__':main()
