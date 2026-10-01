"""Reconstruct all available saved certificates without invoking an optimizer.

Checks literal laws, policy replay, Bellman values, compact LP matrices/duals,
complete profile arithmetic and both saved original-source witnesses. The old
archive retains only hardest/revelation decoder witnesses, not every decoder;
this audit does not pretend to reconstruct unretained witnesses.
"""
from common import *
import argparse,time,traceback,resource
from collections import Counter
from datetime import datetime,timezone
from types import SimpleNamespace
from scale_one import action_weights
from extra_objectives import fixed_history_scores
TOL=2e-7

def check(name,error,tol=TOL):
    error=float(error)
    if not np.isfinite(error) or error>tol:raise AssertionError((name,error,tol))
    return error

def bellman(g,score):
    mu=np.full(g.raw.shape[0],1/g.raw.shape[0]);v={h:float(mu@g.p[h])*float(score[i]) for i,h in enumerate(g.layers[-1])}
    for layer in reversed(g.layers[:-1]):
        for h in layer:v[h]=max(sum(v[h+((a,o),)] for o in [0,1]) for a in [0,1])
    return v[()]

def replay_audit(folder,prefix,E,T,Z,n,report):
    targets=core.Targets(T,Z,n)
    with np.load(folder/(prefix+'_profile.npz'),allow_pickle=False) as z:
        ids=z['indices'];lo=z['lower'];hi=z['upper']
        assert np.array_equal(ids,np.arange(targets.count)) and report['exhaustive']
        assert np.isfinite(lo).all() and np.isfinite(hi).all()
        check('profile gaps',np.max(hi-lo));check('profile ordering',np.max(lo-hi))
        for actual,expected in [(lo.max(),report['lower']),(hi.max(),report['upper']),
                                (lo.mean(),report['mean_lower']),(hi.mean(),report['mean_upper'])]:
            check('profile aggregate',abs(actual-expected),1e-13)
    with np.load(folder/(prefix+'_witness.npz'),allow_pickle=False) as z:
        assert str(z['source_sha256'])==hashlib.sha256(np.ascontiguousarray(E).tobytes()).hexdigest()
        F=targets.get(int(z['target_index']))['kernel']
        check('target law',np.max(abs(F-z['target_kernel'])),1e-14)
        # Direct latent-state recursion for the reported hardest target.
        choices=targets.choices(int(z['target_index']));columns=[]
        import itertools
        for obs in itertools.product([0,1],repeat=n):
            h=();node=0
            for o in obs:h+=((choices[node],o),);node=2*node+1+o
            columns.append(independent_law(T,Z,[[h]])[h])
        check('independent target law',np.max(abs(F-np.array(columns).T)),1e-12)
        for stem,F,upper in [('',F,report['upper']),('revelation_',np.eye(E.shape[0]),report['full_revelation_upper'])]:
            keep=z[stem+'source_indices'];G=z[stem+'decoder'];alpha=z[stem+'alpha'];b=z[stem+'b'];source=E[:,keep]
            assert np.array_equal(keep,np.flatnonzero(E.max(axis=0)>0))
            check('decoder rows',np.max(abs(G.sum(1)-1)));check('decoder nonnegative',max(0.,-G.min()),0.)
            check('decision prior',abs(alpha.sum()-1));check('decision nonnegative',max(0.,-alpha.min(),-b.min()),0.)
            check('bounded loss',max(0.,(b-alpha[:,None]).max()),1e-15)
            hi=float(np.max(abs(source@G-F).sum(1))/2)
            lo=float(np.sum(F*b)-np.max(source.T@b,axis=1).sum())
            check('original-source upper',abs(hi-upper),1e-12)
            check('witness gap',hi-lo);check('witness ordering',lo-hi)
    return dict(profile_entries=targets.count,witnesses=2)

def audit_one(cell):
    folder=ORIGINAL/'main_results'/cell;r=json.loads((folder/'result.json').read_text());a=r['arguments']
    job=next(x for x in MANIFEST['jobs'] if x['id']==cell)
    assert r['manifest_sha256']==digest(ORIGINAL/'main_manifest.json')
    assert r['job_sha256']==hashlib.sha256(json.dumps(job,sort_keys=True).encode()).hexdigest()
    with np.load(folder/'model.npz',allow_pickle=False) as m:T=m['T'].copy();Z=m['Z'].copy()
    model=core.random_model(a['seed'],worlds=a['worlds'],concentration=a['concentration']) if a['case']=='fresh' else core.model(a['case'])
    check('frozen model T',np.max(abs(T-model['T'])),0.);check('frozen model Z',np.max(abs(Z-model['Z'])),0.)
    g=core.geometry(T,Z,a['t']);ind=independent_law(T,Z,g.layers)
    for h in ind:check('literal controlled law',np.max(abs(ind[h]-g.p[h])),1e-12)
    targets=core.Targets(T,Z,a['n']);scores=None;rows=[];certs=0;profiles=0;witnesses=0
    for cp in r.get('checkpoints',[]):
        assert cp['status']=='complete'
        d=folder/f"checkpoint_{cp['k']:03d}"
        with np.load(d/'policy.npz',allow_pickle=False) as z:E=z['E'].copy();policy=z['rows'].copy();leaf=z['leaf'].copy()
        weights={():1.}
        for h,row in zip(g.decisions,policy):
            check('policy stochasticity',abs(row.sum()-1));check('policy nonnegative',max(0.,-row.min()),0.)
            for a0 in [0,1]:
                for o in [0,1]:weights[h+((a0,o),)]=weights[h]*row[a0]
        want_leaf=np.array([weights[h] for h in g.layers[-1]])
        want_E=np.array([ind[h] for h in g.layers[-1]]).T*want_leaf
        check('independent policy law',np.max(abs(E-want_E)),1e-12)
        check('independent realization',np.max(abs(leaf-want_leaf)),1e-12)
        constraint=None
        face=cp.get('reward_face')
        if face or cp['planning']['method']=='exact_tree_dp':
            if scores is None:scores=fixed_history_scores(g)
            obj=face['objective'] if face else a['objective'];score=scores[obj]
            high=bellman(g,score);attained=float((E.mean(0))@score)
            if face:
                check('face optimum',abs(high-face['optimum']),1e-12)
                check('face minimum',abs(-bellman(g,-score)-face['minimum']),1e-12)
                coeff=g.raw.mean(0)*score;constraint=(coeff,face['threshold'])
                check('face feasible',face['threshold']-attained,1e-12)
                check('face regret',abs(high-attained-cp['actual_reward_gap']),1e-12)
            else:check('Bellman-optimal return',abs(high-attained),1e-12)
        ar=replay_audit(d,'audit',E,T,Z,a['n'],cp['audit']);profiles+=ar['profile_entries'];witnesses+=2
        cert=d/'master_certificate.npz'
        if cert.exists():
            with np.load(cert,allow_pickle=False) as z:saved={k:z[k].copy() for k in z.files}
            original=core.solve_arrays
            def verify(cost,Ae,be,Au,bu,bounds,method,time_limit):
                cost=np.asarray(cost);be=np.asarray(be);bu=np.asarray(bu);bounds=np.asarray(bounds)
                for key,mat in [('A_eq',Ae),('A_ub',Au)]:
                    assert hashlib.sha256(mat.data.tobytes()+mat.indices.tobytes()+mat.indptr.tobytes()).hexdigest()==str(saved[key+'_sha256'])
                for key,v in [('cost',cost),('bounds',bounds),('b_eq',be),('b_ub',bu)]:
                    check('certificate reconstruction '+key,np.max(abs(v-saved[key]),initial=0),0.)
                x=saved['solution'];y=saved['eq_dual'];z=saved['ub_dual'];ld=saved['lower_dual'];ud=saved['upper_dual']
                lo,hi=bounds.T
                errors=[np.max(abs(Ae@x-be),initial=0),np.max(Au@x-bu,initial=0),np.max(lo-x),np.max(x-hi),np.max(z,initial=0),np.max(-ld),np.max(ud),np.max(abs(cost-Ae.T@y-Au.T@z-ld-ud))]
                rawdual=float(be@y+bu@z+lo@ld+hi@ud)
                remaining=cost-Ae.T@y-Au.T@np.minimum(z,0)
                dual=float(be@y+bu@np.minimum(z,0)+np.minimum(lo*remaining,hi*remaining).sum())
                primal=float(cost@x);errors.extend([abs(primal-rawdual),abs(primal-dual)])
                check('independent KKT/box repair',max(errors))
                check('saved primal',abs(primal-cp['planning']['primal']),1e-12)
                check('saved dual',abs(dual-cp['planning']['dual']),1e-12)
                sol=SimpleNamespace(x=x,fun=primal,nit=0,eqlin=SimpleNamespace(marginals=y),ineqlin=SimpleNamespace(marginals=z),lower=SimpleNamespace(marginals=ld),upper=SimpleNamespace(marginals=ud))
                return sol,dict(primal=primal,dual=dual)
            library=core.target_library(T,Z) if a['strategy']=='baseline' else [dict(targets.get(j),weight=1/cp['k']) for j in cp['selected_targets']]
            core.solve_arrays=verify
            try:
                certE,_,_,_=core.native_plan(g,library,a['objective'],'highs-ipm',1,reward_constraint=constraint)
            finally:core.solve_arrays=original
            repair=cp['planning'].get('reward_face_repair',{}).get('fraction',0.)
            # With repair, the saved feasible policy may differ from the raw LP optimizer.
            check('policy vs LP experiment',np.max(abs(E-certE)),repair+TOL)
            certs+=1
        rows.append(dict(k=cp['k'],master_certificate=cert.exists()))
    held=r.get('held_out_horizon',{})
    if held:
        assert held['selection_used'] is False
        if 'audit' in held:
            with np.load(folder/held['policy_checkpoint']/'policy.npz',allow_pickle=False) as z:E=z['E'].copy()
            ar=replay_audit(folder/held['policy_checkpoint'],'held_out',E,T,Z,held['n'],held['audit']);profiles+=ar['profile_entries'];witnesses+=2
    return dict(cell=cell,original_status=r['status'],result_sha256=digest(folder/'result.json'),checkpoints=len(rows),master_certificates=certs,profile_entries=profiles,original_source_witnesses=witnesses,status='passed')

def main():
    p=argparse.ArgumentParser();p.add_argument('--cells',nargs='*');p.add_argument('--output',type=Path,required=True);args=p.parse_args()
    args.output.mkdir(parents=True,exist_ok=True)
    cells=args.cells or [j['id'] for j in MANIFEST['jobs'] if (ORIGINAL/'main_results'/j['id']/'result.json').exists()]
    start=time.monotonic();results=[]
    for cell in cells:
        ts=time.monotonic()
        try:r=audit_one(cell)
        except Exception as exc:r=dict(cell=cell,status='failed',error=repr(exc),traceback=traceback.format_exc())
        r['seconds']=time.monotonic()-ts;write(args.output/(cell+'.json'),r);results.append(r)
        summary=dict(status='running',completed_cells=len(results),expected_cells=len(cells),counts=dict(Counter(x['status'] for x in results)),seconds=time.monotonic()-start,
                     checkpoints=sum(x.get('checkpoints',0) for x in results),master_certificates=sum(x.get('master_certificates',0) for x in results),profile_entries=sum(x.get('profile_entries',0) for x in results),original_source_witnesses=sum(x.get('original_source_witnesses',0) for x in results),failures=[x for x in results if x['status']=='failed'])
        write(args.output/'SUMMARY.json',summary)
        print(cell,r['status'],round(r['seconds'],3),flush=True)
    summary.update(status='passed' if not summary['failures'] else 'issues_found',finished_utc=datetime.now(timezone.utc).isoformat(),scope='Reconstructed all stored master certificates and hardest/revelation original-source witnesses; per-target profile arithmetic. Other per-target decoder witnesses were not retained by the original run and cannot be reconstructed without new solves.')
    write(args.output/'SUMMARY.json',summary)
if __name__=='__main__':main()
