#!/usr/bin/env python3
"""Independent literal-law, decision, LP and pure-control replay."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import time

import numpy as np
from scipy import sparse
from scipy.optimize import linprog

HERE = Path(__file__).resolve().parent
ERRORS = {}
COUNT = 0
TOL = 2e-7
LABELS = np.array([[0,0,1,1], [0,1,0,1], [0,1,1,0],
                   [1,0,0,0], [0,1,0,0], [0,0,1,0], [0,0,0,1]])


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(name, difference, tolerance=TOL):
    global COUNT
    value = float(np.max(np.abs(difference), initial=0))
    ERRORS[name] = max(ERRORS.get(name, 0), value); COUNT += 1
    assert value <= tolerance, (name, value, tolerance)


def history_layers(H):
    return [[tuple(zip(actions, observations))
             for interleaved in itertools.product(range(2), repeat=2*t)
             for actions, observations in [(interleaved[::2], interleaved[1::2])]]
            for t in range(H+1)]


def literal_probability(T, Z, h):
    answer = []
    for world in range(4):
        f = np.zeros(T.shape[-1]); f[0] = 1
        for action, observation in h:
            f = (f@T[world, action])*Z[world, action, :, observation]
        answer.append(f.sum())
    return np.array(answer)


def values(E):
    return np.array([np.maximum(E[label == 0].sum(axis=0),
                                E[label == 1].sum(axis=0)).sum()/4 for label in LABELS])


def posterior_gains(E):
    m = E.sum(axis=0)/4
    p = np.divide(E, 4*m[None], out=np.zeros_like(E), where=m[None]>0)
    terms = np.zeros_like(p); positive=p>0
    terms[positive] = p[positive]*np.log2(p[positive])
    return float(2+terms.sum(axis=0)@m), float((p*p).sum(axis=0)@m-.25)


def decoder_error(E, Q):
    E=E[:,np.max(E,axis=0)>0]
    M,X=E.shape; Y=Q.shape[1]; N=X*Y+M*Y+1
    er,ec,ev=[],[],[]; ur,uc,uv=[],[],[]; rhs=[]
    for x in range(X):
        for y in range(Y): er.append(x); ec.append(x*Y+y); ev.append(1.)
    for m in range(M):
        for y in range(Y):
            for sign in [1,-1]:
                row=len(rhs)
                for x in range(X):
                    ur.append(row);uc.append(x*Y+y);uv.append(sign*E[m,x])
                ur.append(row);uc.append(X*Y+m*Y+y);uv.append(-1.)
                rhs.append(sign*Q[m,y])
        row=len(rhs)
        for y in range(Y):
            ur.append(row);uc.append(X*Y+m*Y+y);uv.append(.5)
        ur.append(row);uc.append(N-1);uv.append(-1.);rhs.append(0.)
    eq=sparse.coo_matrix((ev,(er,ec)),shape=(X,N)).tocsr()
    ub=sparse.coo_matrix((uv,(ur,uc)),shape=(len(rhs),N)).tocsr()
    cost=np.zeros(N);cost[-1]=1.
    fit=linprog(cost,A_eq=eq,b_eq=np.ones(X),A_ub=ub,b_ub=rhs,bounds=(0,1),
                method='highs',options={'primal_feasibility_tolerance':1e-9,
                                        'dual_feasibility_tolerance':1e-9})
    assert fit.success,fit.message
    G=np.maximum(fit.x[:X*Y].reshape(X,Y),0);G/=G.sum(axis=1,keepdims=True)
    upper=.5*abs(E@G-Q).sum(axis=1).max()
    dual=fit.eqlin.marginals.sum()+np.array(rhs)@fit.ineqlin.marginals+fit.upper.marginals.sum()
    check('fresh_decoder_bracket',upper-dual)
    return float(upper)


def certificate(path):
    a=np.load(path)
    def matrix(prefix):
        return sparse.csr_matrix((a[prefix+'_data'],a[prefix+'_indices'],
                                  a[prefix+'_indptr']),shape=tuple(a[prefix+'_shape']))
    eq,ub=matrix('A_eq'),matrix('A_ub');x=a['solution'];lo,hi=a['bounds'].T
    check('lp_eq',eq@x-a['b_eq']);check('lp_ub',np.maximum(ub@x-a['b_ub'],0))
    check('lp_bounds',np.maximum(np.maximum(lo-x,x-hi),0))
    check('dual_sign_ub',np.maximum(a['ub_dual'],0))
    check('dual_sign_lower',np.minimum(a['lower_dual'],0))
    check('dual_sign_upper',np.maximum(a['upper_dual'],0))
    check('lp_stationarity',a['cost']-eq.T@a['eq_dual']-ub.T@a['ub_dual']-
          a['lower_dual']-a['upper_dual'])
    dual=a['b_eq']@a['eq_dual']+a['b_ub']@a['ub_dual']+lo@a['lower_dual']+hi@a['upper_dual']
    check('lp_primal_dual',a['cost']@x-dual)
    check('lp_objective',a['objective']-a['cost']@x)
    return a


def enumerate_pure_paths(depth):
    if depth==0:
        return [[()]]
    sub=enumerate_pure_paths(depth-1)
    return [[((a,0),)+h for h in left]+[((a,1),)+h for h in right]
            for a in range(2) for left in sub for right in sub]


def audit_case(folder):
    meta=json.loads((folder/'results.json').read_text());assert meta['status']=='complete'
    check('source_hash',int(meta['code_sha256']!=digest(HERE/'compute.py')))
    check('protocol_hash',int(meta['protocol_sha256']!=digest(HERE/'PROTOCOL.md')))
    check('core_hash',int(meta['core_sha256']!=digest(HERE.parent/'noisy_diagnostic_transfer_2026-09-13/compute.py')))
    model=np.load(folder/'model.npz');T,Z=model['T'],model['Z'];H=meta['H']
    check('transition_normalization',T.sum(axis=-1)-1)
    check('emission_normalization',Z.sum(axis=-1)-1)
    lev=history_layers(H);leaves=lev[-1]
    raw=np.array([literal_probability(T,Z,h) for h in leaves]).T
    check('literal_mass',raw-model['source_controlled_masses'])
    targets=json.loads((folder/'targets.json').read_text());Qs=[]
    for j,t in enumerate(targets):
        Q=np.array([literal_probability(T,Z,h) for h in t['signals']]).T
        if t['name'].startswith('tagged'): Q*=.5
        check('literal_target',Q-model[f'target_{j}']);Qs.append(Q)
    target_weights=np.array([t['weight'] for t in targets])
    pure=np.load(folder/'pure_controls.npz');check('pure_hash',int(str(pure['code_sha256'])!=meta['code_sha256']))
    paths=enumerate_pure_paths(H);assert len(paths)==128
    pure_map={tuple(w.astype(int)):i for i,w in enumerate(pure['weights'])}
    assert len(pure_map)==128
    independent_rewards={k:[] for k in ['information','brier','surprisal','first_visit']}
    pure_values=[]
    for j,allowed in enumerate(paths):
        allowed=set(allowed);weight=np.array([float(h in allowed) for h in leaves])
        i=pure_map[tuple(weight.astype(int))];E=raw*weight
        check('pure_source_sum',E.sum(axis=1)-1)
        ds=np.array([decoder_error(E,Q) for Q in Qs])
        check('pure_deficiencies',ds-pure['deficiencies'][i])
        vv=values(E);pure_values.append(vv);check('pure_decisions',vv-pure['decision_values'][i])
        ig,brier=posterior_gains(E)
        independent_rewards['information'].append(ig);independent_rewards['brier'].append(brier)
        surprise=0.;visit=0.
        for k,h in enumerate(leaves):
            if h not in allowed:continue
            p=E[:,k].mean();surprise-=p*np.log2(p)
            visit+=p*len(set(o for _,o in h))
        independent_rewards['surprisal'].append(surprise)
        independent_rewards['first_visit'].append(visit)
    check('best_mean',np.mean(pure_values,axis=1).max()-meta['unconstrained_best_mean'])
    check('best_each',np.max(pure_values,axis=0)-meta['unconstrained_best_each'])
    check('maximum_native_sum',(pure['deficiencies']@target_weights).max()-meta['maximal_costs']['native_weighted'])
    check('maximum_native_max',pure['deficiencies'].max()-meta['maximal_costs']['native_minimax'])
    prefixes=[h for layer in lev[:-1] for h in layer];row_index={h:i for i,h in enumerate(prefixes)}
    optima={r['objective']:r for r in meta['optima']};optimum_sources={}
    for record in meta['optima']+meta['endpoints']:
        objective=record['objective'];endpoint='purpose' in record
        stem=(f"{objective}_f{record['fraction']}_{record['purpose']}" if endpoint else objective+'_optimum')
        cert=certificate(folder/(stem+'.npz'))
        data=np.load(folder/(stem+'_policy.npz'));rows=data['rows']
        check('policy_rows',rows.sum(axis=1)-1);check('policy_nonnegative',np.minimum(rows,0))
        weight=np.array([np.prod([rows[row_index[h[:t]],a] for t,(a,o) in enumerate(h)]) for h in leaves])
        E=raw*weight;check('literal_source',E-data['E']);check('source_stochastic',E.sum(axis=1)-1)
        check('realization_recovery',weight-cert['solution'][data['terminal_w_indices']])
        vv=values(E);check('saved_decisions',vv-record['decision_values'])
        if endpoint:
            idx={'U':0,'V':1,'parity':2}.get(record['purpose'])
            value=float(vv.mean() if idx is None else vv[idx])
            check('endpoint_value',value-record['value']);check('endpoint_lp',value-cert['objective'])
            check('eta',record['eta']-record['fraction']*optima[objective]['range'])
        else:
            optimum_sources[objective]=E
        if objective in independent_rewards:
            check('exhaustive_optimum',-max(independent_rewards[objective])-optima[objective]['cost'])
            check('linear_max_cost',-min(independent_rewards[objective])-meta['maximal_costs'][objective])
            gains=posterior_gains(E)
            actual=(-gains[0] if objective=='information' else -gains[1] if objective=='brier' else
                    float(sum(weight[k]*raw[:,k].mean()*np.log2(raw[:,k].mean()) for k in range(len(leaves))))
                    if objective=='surprisal' else
                    -float(sum(E[:,k].mean()*len(set(o for _,o in h)) for k,h in enumerate(leaves))))
            if endpoint:check('linear_threshold',max(0,actual-record['threshold']))
            else:check('linear_cost',actual-record['cost'])
        elif endpoint:
            bounds=[]
            for j,Q in enumerate(Qs):
                z=data[f'allocations_{j}']
                check('allocation_sums',z.sum(axis=1)-weight)
                # The allocation law avoids dividing by tiny realized weights.
                output=raw@z
                error=.5*abs(output-Q).sum(axis=1).max()
                check('decoder_bound',max(0,error-data['deficit_upper'][j]))
                bounds.append(error)
            cost=max(bounds) if objective=='native_minimax' else target_weights@bounds
            check('native_threshold',max(0,cost-record['threshold']))
        else:
            ds=np.array([decoder_error(E,Q) for Q in Qs])
            cost=max(ds) if objective=='native_minimax' else target_weights@ds
            check('native_minimum',cost-record['cost'])
    for row in meta['optimum_pair_witnesses']:
        B=optimum_sources[row['objective']];N=optimum_sources['native_weighted']
        check('pair_forward',decoder_error(N,B)-row['native_to_baseline'])
        check('pair_reverse',decoder_error(B,N)-row['baseline_to_native'])
    return {'case':meta['name'],'status':'passed','endpoints':len(meta['endpoints'])}


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--case',default='all')
    parser.add_argument('--input',type=Path,default=HERE/'results');args=parser.parse_args()
    start=time.monotonic();rows=[]
    for path in sorted(args.input.glob('*/results.json')):
        if args.case not in ['all',path.parent.name]:continue
        rows.append(audit_case(path.parent));print(path.parent.name,'audit passed',flush=True)
    result=dict(status='passed',scope='Fresh floating-point independent replay, not interval proof.',
                cases=rows,check_count=COUNT,max_errors=ERRORS,seconds=time.monotonic()-start,
                auditor_sha256=digest(Path(__file__)))
    target=args.input/('audit.json' if args.case=='all' else 'audit_'+args.case+'.json')
    target.write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
