"""Maximize original posterior reward subject to one fixed-record TV cap.
This is a reference-aware existence diagnostic, never a primary collector.
"""
from common import *
import argparse,time,traceback,resource
sys.path.insert(0,str(PARENT/'deps'))
import scaling_core as core
from scipy import sparse
MARGIN=1e-7

def solve(T,Z,t,F,method,epsilon,out,seconds=150.):
    assert method in ('information','brier') and epsilon>MARGIN
    start=time.monotonic();g=core.geometry(T,Z,t);Q,S=g.raw.shape;Y=F.shape[1];P=g.flow.shape[1]
    coeff=core.reward_coefficients(g)[method]
    L=core.Builder();L.variables(P);L.cost[:P]=(-np.bincount(g.leaf_index,weights=coeff,minlength=P)).tolist()
    L.rows([(0,g.flow)],g.flow_rhs,True)
    d=L.variables(1);z=L.variables(S*Y);e=L.variables(Q*Y)
    assign=sparse.coo_matrix((np.ones(S),(np.arange(S),g.leaf_index)),shape=(S,P)).tocsr()
    normal=sparse.kron(sparse.eye(S),np.ones((1,Y)),format='csr')
    L.rows([(z,normal),(0,-assign)],np.zeros(S),True)
    decoded=sparse.kron(sparse.csr_matrix(g.raw),sparse.eye(Y),format='csr');eye=sparse.eye(Q*Y,format='csr')
    L.rows([(z,decoded),(e,-eye)],F.ravel());L.rows([(z,-decoded),(e,-eye)],-F.ravel())
    total=.5*sparse.kron(sparse.eye(Q),np.ones((1,Y)),format='csr')
    L.rows([(e,total),(d,-np.ones((Q,1)))],np.zeros(Q))
    L.rows([(d,sparse.csr_matrix([[1.]]))],[epsilon-MARGIN])
    Ae,Au=L.matrix(True),L.matrix(False)
    sol,report=core.solve_arrays(L.cost,Ae,L.be,Au,L.bu,[(0,1)]*len(L.cost),'highs',seconds)
    E,rows,leaf=core.replay(g,sol.x[:P]);replay(T,Z,t,rows,E,leaf)
    G=np.maximum(sol.x[z:e].reshape(S,Y),0.)
    total=G.sum(1);G=np.divide(G,total[:,None],out=np.full_like(G,1/Y),where=total[:,None]>0)
    tv=float(np.max(np.abs(E@G-F).sum(1))/2)
    if tv>epsilon-1e-9:raise RuntimeError(f'Replayed cap not certified: {tv} > {epsilon-1e-9}')
    # The same feasible dual gives a bound for the untightened problem.
    cap_dual=min(float(sol.ineqlin.marginals[-1]),0.)
    reward_upper=-(report['dual']+MARGIN*cap_dual)
    value=rewards(E,g.layers[-1])[method]
    arrays=dict(cost=np.array(L.cost),bounds=np.array([(0.,1.)]*len(L.cost)),solution=sol.x,
                b_eq=np.array(L.be),b_ub=np.array(L.bu),eq_dual=sol.eqlin.marginals,
                ub_dual=sol.ineqlin.marginals,lower_dual=sol.lower.marginals,upper_dual=sol.upper.marginals)
    for name,A in [('A_eq',Ae),('A_ub',Au)]:
        arrays.update({name+'_data':A.data,name+'_indices':A.indices,name+'_indptr':A.indptr,name+'_shape':np.array(A.shape)})
    out.mkdir(parents=True,exist_ok=True)
    save(out/'lp.npz',**arrays);save(out/'policy_decoder.npz',E=E,rows=rows,leaf=leaf,G=G,F=F)
    return dict(status='complete',method=method,t=t,epsilon=epsilon,cap_tightening=MARGIN,
                achieved_reward=value,constrained_reward_upper=reward_upper,
                cap_upper=tv,cap_dual=cap_dual,lp=report,seconds=time.monotonic()-start,
                files={p.name:sha(p) for p in [out/'lp.npz',out/'policy_decoder.npz']})

def run(job,out):
    source=verify_sources();T,Z,F=inputs(job);out.mkdir(parents=True,exist_ok=False);start=time.monotonic()
    r=dict(status='running',started_utc=now(),job=job,sources_sha256=source)
    write(out/'result.json',r)
    try:r.update(solve(T,Z,job['t'],F,job['method'],job['epsilon'],out))
    except Exception as exc:r.update(status='failed',error=repr(exc),traceback=traceback.format_exc())
    r.update(finished_utc=now(),wall_seconds=time.monotonic()-start,peak_rss_mib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024)
    assert source==verify_sources();write(out/'result.json',r);print(job['id'],r['status'],flush=True)
    return r

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('job');a=p.parse_args()
    os.sched_setaffinity(0,{10});resource.setrlimit(resource.RLIMIT_AS,(8*1024**3,)*2)
    job=next(j for j in json.loads((HERE/'JOBS.json').read_text())['jobs'] if j['id']==a.job)
    if run(job,HERE/'results'/job['id'])['status']!='complete':raise SystemExit(1)
