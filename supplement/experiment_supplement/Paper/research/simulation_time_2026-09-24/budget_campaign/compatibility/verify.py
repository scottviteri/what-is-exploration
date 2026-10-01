"""No optimizer import: bind LP, check primal/dual and replay the physical policy."""
from common import *
from scipy import sparse
from check import lp,matrix,norm,pos
import argparse,time

def verify_arrays(T,Z,t,F,method,epsilon,margin,folder):
    certificate,a=lp(folder/'lp.npz')
    with np.load(folder/'policy_decoder.npz') as z:
        E=z['E'];rows=z['rows'];leaf=z['leaf'];G=z['G'];assert norm(z['F']-F)<1e-12
    E,leaf,raw,physical=replay(T,Z,t,rows,E,leaf)
    layers=levels(t);decisions=sum(layers[:-1],[]);di={h:i for i,h in enumerate(decisions)}
    Q,S=raw.shape;Y=F.shape[1];P=2*len(decisions);d=P;zz=P+1;ee=zz+S*Y;V=ee+Q*Y
    # Reconstruct objective from the literal model, independent of planner coefficients.
    m=raw.mean(0);post=np.divide(raw,Q*m,out=np.zeros_like(raw),where=m>0)
    if method=='information':
        logs=np.zeros_like(post);np.log2(post,out=logs,where=post>0);score=np.log2(Q)+(post*logs).sum(0)
    else:assert method=='brier';score=(post*post).sum(0)-1/Q
    coeff=m*score;li=np.array([2*di[h[:-1]]+h[-1][0] for h in layers[-1]])
    cost=np.zeros(V);np.add.at(cost,li,-coeff)
    # Independent sparse constraint construction by indexed entries.
    er=[];ec=[];ev=[]
    def eq(r,c,v):er.append(r);ec.append(c);ev.append(v)
    for i,h in enumerate(decisions):
        eq(i,2*i,1.);eq(i,2*i+1,1.)
        if h:eq(i,2*di[h[:-1]]+h[-1][0],-1.)
    for s in range(S):
        r=len(decisions)+s;eq(r,li[s],-1.)
        for y in range(Y):eq(r,zz+s*Y+y,1.)
    Ae=sparse.coo_matrix((ev,(er,ec)),shape=(len(decisions)+S,V)).tocsr();be=np.zeros(Ae.shape[0]);be[0]=1.
    ur=[];uc=[];uv=[]
    def ub(r,c,v):ur.append(r);uc.append(c);uv.append(v)
    for q in range(Q):
        for y in range(Y):
            r=q*Y+y
            ub(r,ee+r,-1.);ub(Q*Y+r,ee+r,-1.)
            for s in np.flatnonzero(raw[q]):
                ub(r,zz+s*Y+y,raw[q,s]);ub(Q*Y+r,zz+s*Y+y,-raw[q,s])
            ub(2*Q*Y+q,ee+r,.5)
        ub(2*Q*Y+q,d,-1.)
    ub(2*Q*Y+Q,d,1.)
    Au=sparse.coo_matrix((uv,(ur,uc)),shape=(2*Q*Y+Q+1,V)).tocsr()
    bu=np.r_[F.ravel(),-F.ravel(),np.zeros(Q),epsilon-margin]
    residual=max(norm(a['cost']-cost),norm((matrix(a,'A_eq')-Ae).data),norm((matrix(a,'A_ub')-Au).data),norm(a['b_eq']-be),norm(a['b_ub']-bu),norm(a['bounds']-np.tile([0.,1.],(V,1))))
    assert residual<1e-10,('LP binding',residual)
    assert G.shape==(S,Y) and np.isfinite(G).all() and G.min()>=0 and norm(G.sum(1)-1)<1e-10
    cap=float(np.max(np.abs(E@G-F).sum(1))/2);assert cap<=epsilon-1e-9,('cap',cap)
    actual=rewards(E,layers[-1])[method];assert abs(actual-np.dot(leaf,coeff))<1e-10
    # Independently solve the unconstrained Bellman recurrence, without numerical optimizer.
    values=dict(zip(layers[-1],coeff))
    for layer in reversed(layers[:-1]):
        for h in layer:values[h]=max(sum(values[h+((act,o),)] for o in (0,1)) for act in (0,1))
    optimum=float(values[()]);cap_dual=min(float(a['ub_dual'][-1]),0.)
    constrained_upper=-(certificate['lower']+margin*cap_dual)
    assert actual<=constrained_upper+TOL and actual<=optimum+TOL
    regret_lower=max(0.,optimum-constrained_upper);regret_upper=max(0.,optimum-actual)
    classification='positive_reward_cost' if regret_lower>TOL else ('compatible_within_numerical_tolerance' if regret_upper<=TOL else 'unresolved_reward_gap')
    return dict(unconstrained_optimum=optimum,constrained_reward_lower=actual,constrained_reward_upper=constrained_upper,
                reward_regret_lower=regret_lower,reward_regret_upper=regret_upper,classification=classification,
                cap_upper=cap,epsilon=epsilon,physical_residual=physical,binding_residual=residual,lp=certificate,
                scope='Float64 replay and box-repaired LP dual bounds; existential, reference-aware compatibility, not all-optima or formal exact arithmetic.')

def verify(folder):
    start=time.monotonic();r=json.loads((folder/'result.json').read_text());assert r['status']=='complete'
    assert r['sources_sha256']==verify_sources();T,Z,F=inputs(r['job'])
    for name,digest in r['files'].items():assert sha(folder/name)==digest
    out=verify_arrays(T,Z,r['t'],F,r['method'],r['epsilon'],r['cap_tightening'],folder)
    assert abs(out['constrained_reward_lower']-r['achieved_reward'])<1e-10
    assert abs(out['constrained_reward_upper']-r['constrained_reward_upper'])<1e-10
    assert abs(out['cap_upper']-r['cap_upper'])<1e-10
    out.update(status='passed',checked_utc=now(),result_sha256=sha(folder/'result.json'),seconds=time.monotonic()-start)
    write(folder/'CHECK.json',out);return out

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('folder',type=Path);a=p.parse_args()
    os.sched_setaffinity(0,{10})
    try:print(json.dumps(verify(a.folder)),flush=True)
    except Exception as exc:write(a.folder/'CHECK.json',dict(status='failed',error=repr(exc),checked_utc=now()));raise
