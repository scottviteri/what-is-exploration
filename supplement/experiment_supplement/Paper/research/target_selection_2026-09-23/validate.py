"""Bounded independent checks before freezing the larger campaign."""
import hashlib,json,itertools,os,sys,tempfile
from pathlib import Path
from types import SimpleNamespace
sys.dont_write_bytecode=True
import numpy as np
import scaling_core as c
import scale_one as run
from extra_objectives import fixed_history_scores
from fast_decoder import NativeDecoder
from certified_decoder import StableDecoder
HERE=Path(__file__).resolve().parent
checks=[]

def check(name,err,tol=2e-7):
    err=float(err)
    if not np.isfinite(err) or err>tol:raise AssertionError((name,err,tol))
    checks.append({'name':name,'error':err,'tolerance':tol})

def literal_target(T,Z,n,index):
    choices=[(index>>(2**n-2-k))&1 for k in range(2**n-1)]
    values=[]
    for observations in itertools.product(range(2),repeat=n):
        state=np.zeros((len(T),T.shape[-1]));state[:,0]=1;node=0
        for o in observations:
            a=choices[node];out=np.zeros_like(state)
            for q in range(len(T)):
                for v in range(T.shape[-1]):
                    for u in range(T.shape[-1]):out[q,v]+=state[q,u]*T[q,a,u,v]*Z[q,a,v,o]
            state=out;node=2*node+1+o
        values.append(state.sum(1))
    return np.array(values).T

for case in [c.model('sensors_0.1_0.3'),c.random_model(928001,4,concentration=.2)]:
    ts=c.Targets(case['T'],case['Z'],3)
    for j in range(ts.count):check('literal target',abs(ts.get(j)['kernel']-literal_target(case['T'],case['Z'],3,j)).max(),1e-12)
    for strategy in ['random','structured','adaptive']:
        order=run.order_targets(ts,strategy,17)
        assert sorted(order)==list(range(128)) and order==run.order_targets(ts,strategy,17)
    g=c.geometry(case['T'],case['Z'],3)
    allscores=fixed_history_scores(g)
    for name in ['information','brier','surprisal','prediction_error']:
        _,_,_,dp=run.dp_plan(g,allscores[name]);coeff=g.raw.mean(0)*allscores[name]
        _,_,_,lp=c.reward_plan(g,coeff,'highs-ipm',30)
        check('DP versus independent LP '+name,abs(dp['reward']-lp['reward']))
    library=c.target_library(case['T'],case['Z'])
    _,_,_,original=c.native_plan(g,library,'native_minimax','highs-ipm',30)
    _,_,_,pruned=c.native_plan(g,[ts.get(j) for j in ts.fixed_indices()],'native_minimax','highs-ipm',30)
    check('prefix/mixture minimax reduction',abs(original['primal']-pruned['primal']))

case=c.model('sensors_0.1_0.3');g=c.geometry(case['T'],case['Z'],3);ts=c.Targets(case['T'],case['Z'],3)
score=fixed_history_scores(g)['brier'];_,bestrows,_,best=run.dp_plan(g,score)
constraint=(g.raw.mean(0)*score,best['reward']-1e-10)
args=SimpleNamespace(method='highs-ipm',max_variables=1200000,objective='native_minimax',solve_limit=30)
with tempfile.TemporaryDirectory(prefix='target-selection-validation-') as tmp:
    path=Path(tmp);library=[ts.get(j) for j in ts.fixed_indices()]
    E,rows,leaf,plan=run.master(g,library,args,path,constraint,(bestrows,best['reward']))
    check('reward face feasibility',max(0.,constraint[1]-leaf@constraint[0]),0.)
    data=np.load(path/'master_certificate.npz');original_solve=c.solve_arrays
    def verify(cvec,Ae,be,Au,bu,bounds,method,time_limit):
        for key,matrix in [('A_eq',Ae),('A_ub',Au)]:
            assert hashlib.sha256(matrix.data.tobytes()+matrix.indices.tobytes()+matrix.indptr.tobytes()).hexdigest()==str(data[key+'_sha256'])
        check('reconstructed LP objective',np.max(abs(np.asarray(cvec)-data['cost'])),0.)
        sol=SimpleNamespace(x=data['solution'],fun=float(data['objective']),nit=0,
            eqlin=SimpleNamespace(marginals=data['eq_dual']),ineqlin=SimpleNamespace(marginals=data['ub_dual']),
            lower=SimpleNamespace(marginals=data['lower_dual']),upper=SimpleNamespace(marginals=data['upper_dual']))
        checked=c.check_solution(np.array(cvec),Ae,np.array(be),Au,np.array(bu),data['bounds'][:,0],data['bounds'][:,1],sol)
        check('compact certificate reconstruction',max(checked['residuals'].values()))
        return sol,checked
    c.solve_arrays=verify
    try:c.native_plan(g,library,'native_minimax','highs-ipm',30,reward_constraint=constraint)
    finally:c.solve_arrays=original_solve
    # Force a severely infeasible recovered policy to exercise the mixture repair.
    original_plan=c.native_plan
    def perturb(*a,**kw):
        _,_,_,certificate=original_plan(*a,**kw)
        badrows=np.full((len(g.decisions),2),.5)
        badE,badrows,badleaf=c.replay(g,run.action_weights(g,badrows))
        return badE,badrows,badleaf,certificate
    c.native_plan=perturb
    try:
        # Replaying the repaired objective may differ from the master by at most the mixture mass.
        _,_,repaired,proof=run.master(g,library,args,path,constraint,(bestrows,best['reward']))
        check('forced face repair feasibility',max(0.,constraint[1]-repaired@constraint[0]),0.)
        assert proof['reward_face_repair']['fraction']>0
    finally:c.native_plan=original_plan

# Validate original inputs before zero/tiny-column numerical coarsening.
for bad in [np.array([1.,0.]),np.empty((0,2)),np.empty((2,0)),
            np.array([[1.,np.nan],[1.,0.]]),np.array([[1.,np.inf],[1.,0.]]),
            np.array([[1.,-1e-12],[1.,0.]]),np.array([[.5,0.],[1.,0.]])]:
    try:StableDecoder(bad,2)
    except ValueError:check('invalid original source rejected',0.,0.)
    else:raise AssertionError('Invalid original source accepted')
for epsilon in [1e-12,1e-10,5e-10]:
    source=np.array([[.9-epsilon,.1,epsilon],[.1,.9-epsilon,epsilon]])
    decoder=StableDecoder(source,2);bracket,witness=decoder.solve(np.eye(2))
    exact=.1+epsilon/2
    check('coarsened binary analytic bracket',max(0.,bracket['lower']-exact,exact-bracket['upper']),1e-14)
    assert witness['decoder'].shape==(3,2)

singleton=c.random_model(928002,worlds=1);sg=c.geometry(singleton['T'],singleton['Z'],2)
E=sg.raw/4;ss=c.Targets(singleton['T'],singleton['Z'],2)
audit=c.audit(E,ss,method='native-simplex',time_limit=30)
check('known singleton experiment is vacuous',abs(audit['upper']))
report={'status':'passed','checks':checks,'count':len(checks),'maximum_error':max(x['error'] for x in checks),
        'scope':'Independent literal target propagation, DP versus LP, prefix/mixture values, reward-face repair, compact certificate reconstruction and singleton zero control. No new theorem or large training.'}
(HERE/'VALIDATION.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='checks'},indent=2))
