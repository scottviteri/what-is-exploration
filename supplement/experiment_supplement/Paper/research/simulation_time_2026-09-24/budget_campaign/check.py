"""Independent physical replay, LP/cut arithmetic and decoder witness checking.
No planner or decoder imports, no new optimization, float64 rather than interval proof.
"""
from io_utils import *
from scipy import sparse
import argparse,time

def norm(v):return float(np.max(abs(v),initial=0.))
def pos(v):return float(np.max(np.maximum(v,0),initial=0.))
def matrix(z,name):return sparse.csr_matrix((z[name+'_data'],z[name+'_indices'],z[name+'_indptr']),shape=z[name+'_shape'])
def lp(path):
    z=np.load(path);c=z['cost'];x=z['solution'];Ae=matrix(z,'A_eq');Au=matrix(z,'A_ub');be=z['b_eq'];bu=z['b_ub'];ye=z['eq_dual'];yu=z['ub_dual'];yl=z['lower_dual'];yh=z['upper_dual']
    assert all(np.isfinite(v).all() for v in [c,x,Ae.data,Au.data,be,bu,ye,yu,yl,yh])
    residual=max(norm(Ae@x-be),pos(Au@x-bu),pos(-x),pos(x-1),pos(yu),pos(-yl),pos(yh),norm(c-Ae.T@ye-Au.T@yu-yl-yh))
    uy=np.minimum(yu,0.);rem=c-Ae.T@ye-Au.T@uy;lower=float(be@ye+bu@uy+np.minimum(rem,0.).sum());upper=float(c@x)
    residual=max(residual,abs(upper-lower));assert residual<=TOL,('master LP',residual)
    return dict(lower=lower,upper=upper,residual=residual),z

def check_native(folder,T,Z,t,E,rows,leaf,raw,kind):
    z=np.load(folder/'decomposition.npz');layers=levels(t);decisions=sum(layers[:-1],[]);di={h:i for i,h in enumerate(decisions)};P=2*len(decisions)
    li=np.array([2*di[h[:-1]]+h[-1][0] for h in layers[-1]]);assert np.array_equal(li,z['leaf_index'])
    Fs=np.array([target(T,Z,3,j) for j in range(128)]);res=max(norm(Fs-z['target_kernels']),norm(raw-z['raw']),norm(E-z['E']),norm(rows-z['rows']),norm(leaf-z['leaf']))
    slopes=z['cut_slopes'].reshape(-1,P)
    for j,(idx,c,s,a,b) in enumerate(zip(z['cut_targets'],z['cut_intercepts'],slopes,z['cut_alpha'],z['cut_b'])):
        assert all(np.isfinite(v).all() for v in [c,s,a,b]);res=max(res,abs(a.sum()-1),pos(-a),pos(-b),pos(b-a[:,None]))
        expected=np.bincount(li,weights=np.max(raw.T@b,axis=1),minlength=P)
        res=max(res,abs(c-np.sum(Fs[idx]*b)),norm(s-expected))
    lows=[];highs=[]
    for j,F in enumerate(Fs):
        w={k:z[f'witness_{j}_{k}'] for k in ['source_indices','decoder','alpha','b']};l,u=check_witness(E,F,w)
        res=max(res,abs(l-z['target_lower'][j]),abs(u-z['target_upper'][j]));lows.append(l);highs.append(u)
    m,a=lp(folder/'master_certificate.npz');D=1 if kind=='native_minimax' else 128;weights=np.full(128,1/128)
    expected_c=np.r_[np.zeros(P),[1.] if D==1 else weights];res=max(res,norm(a['cost']-expected_c),norm(z['target_weights']-weights))
    er=[];ec=[];ev=[]
    for i,h in enumerate(decisions):
        er.extend([i,i]);ec.extend([2*i,2*i+1]);ev.extend([1.,1.])
        if h:er.append(i);ec.append(2*di[h[:-1]]+h[-1][0]);ev.append(-1.)
    eq=sparse.coo_matrix((ev,(er,ec)),shape=(len(decisions),P+D)).tocsr();be=np.zeros(len(decisions));be[0]=1.
    res=max(res,norm((matrix(a,'A_eq')-eq).data),norm(a['b_eq']-be))
    R=len(a['b_ub']);sl=sparse.csr_matrix(-slopes[:R]);tail=sparse.coo_matrix((-np.ones(R),(np.arange(R),np.zeros(R,dtype=int) if D==1 else z['cut_targets'][:R])),shape=(R,D)).tocsr();ineq=sparse.hstack([sl,tail],format='csr')
    res=max(res,norm((matrix(a,'A_ub')-ineq).data),norm(a['b_ub']+z['cut_intercepts'][:R]))
    upper=max(highs) if D==1 else float(np.mean(highs));gap=upper-m['lower'];assert res<=TOL,('native replay',res)
    return dict(residual=res,lower=m['lower'],upper=upper,gap=gap,certified=-TOL<=gap<=TOL,cuts=len(slopes),master=m)

def check_dp(folder,T,Z,t,E,rows,raw,method):
    layers=levels(t);histories=layers[-1];Q=len(T);m=raw.mean(0);post=np.divide(raw,Q*m,out=np.zeros_like(raw),where=m>0)
    if method=='information':
        logs=np.zeros_like(post);np.log2(post,out=logs,where=post>0);score=np.log2(Q)+(post*logs).sum(0)
    elif method=='brier':score=(post*post).sum(0)-1/Q
    else:
        vals=[]
        for h in histories:
            count=[0,0];total=0.
            for a,o in h:total+=1/np.sqrt(1+count[o]);count[o]+=1
            vals.append(total)
        score=np.array(vals)
    coeff=m*score;v=dict(zip(histories,coeff))
    for layer in reversed(layers[:-1]):
        for h in layer:v[h]=max(sum(v[h+((a,o),)] for o in (0,1)) for a in (0,1))
    actual=float(E.mean(0)@score);gap=v[()]-actual;z=np.load(folder/'dp_certificate.npz')
    residual=max(norm(coeff-z['coefficients']),norm(np.array([v[h] for layer in layers for h in layer])-z['values']),abs(actual-rewards(E,histories)[method]))
    assert residual<=TOL and -TOL<=gap<=TOL
    return dict(optimum=float(v[()]),attained=actual,gap=gap,residual=residual,certified=True)

def check(folder):
    start=time.monotonic();r=json.loads((folder/'result.json').read_text());assert r['status'] in ['complete','incomplete_optimization']
    verify_sources();assert r['sources_sha256']==sha(HERE/'SOURCES.json')
    assert r['manifest_sha256']==sha(HERE/'MANIFEST.json')
    refs=json.loads((HERE/'REFERENCES.json').read_text());refs=[x for x in refs['records'] if x['case_id']==r['spec']['case_id']];modelpath=HERE/refs[0]['model'];assert sha(modelpath)==r['model_sha256']
    with np.load(modelpath) as z:T=z['T'];Z=z['Z']
    pp=folder/'policy.npz';assert sha(pp)==r['policy_sha256']
    with np.load(pp) as z:E=z['E'];rows=z['rows'];leaf=z['leaf']
    t=r['spec']['t'];method=r['spec']['method'];actual,w,raw,res=replay(T,Z,t,rows,E,leaf)
    rew=rewards(actual,levels(t)[-1]);assert max(abs(rew[k]-r['rewards'][k]) for k in rew)<1e-10
    plan=dict(certified=True,scope='Frozen selected reference or literal uniform control')
    if r['spec']['mode']=='plan':
        if method in ('weighted128','minimax'):plan=check_native(folder,T,Z,t,E,rows,leaf,raw,r['planning']['kind'])
        elif method!='uniform':plan=check_dp(folder,T,Z,t,E,rows,raw,method)
    assert plan['certified']==r['planning_certified']
    assert len(r['audits'])==6
    for ar in r['audits']:
        ref=next(x for x in refs if x['method']==ar['reference']);assert sha(HERE/ref['path'])==ref['sha256']
        with np.load(HERE/ref['path']) as z:F=z['E']
        path=folder/ar['witness'];assert sha(path)==ar['witness_sha256']
        with np.load(path) as z:
            assert norm(z['E']-E)<1e-12 and norm(z['F']-F)<1e-12
            l,u=check_witness(actual,F,z)
        assert abs(l-ar['lower'])<1e-10 and abs(u-ar['upper'])<1e-10
        assert {str(e):classify(l,u,e) for e in [.05,.02,.01]}==ar['classification']
        if t==3 and ar['reference']==method:assert u<TOL,'Own-reference reproduction must be zero'
    out=dict(status='passed',checked_utc=now(),result_sha256=sha(folder/'result.json'),planning=plan,reference_comparisons=6,replay_residual=res,seconds=time.monotonic()-start,scope='Independent physical replay, full training-library cut/master and decoder witnesses, float64 checks; no exact arithmetic or all-optima claim.')
    write(folder/'CHECK.json',out);return out

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('folder',type=Path);a=p.parse_args()
    try:print(json.dumps(check(a.folder)),flush=True)
    except Exception as e:
        write(a.folder/'CHECK.json',dict(status='failed',error=repr(e),checked_utc=now()));raise
