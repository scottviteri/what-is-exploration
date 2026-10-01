#!/usr/bin/env python3
"""Explain frozen benchmark results; preserve all parent outputs."""
import copy
from fractions import Fraction as F
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import sys

import numpy as np

HERE=Path(__file__).resolve().parent
PARENT=HERE.parent


def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    mod=importlib.util.module_from_spec(spec);sys.modules[name]=mod
    spec.loader.exec_module(mod)
    return mod


b=load('native_diagnostics_benchmark',PARENT/'compute.py')
a=load('native_diagnostics_auditor',PARENT/'audit.py')


def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def score(E,raw,histories):
    m=E.sum(axis=0)/4
    post=np.divide(E,4*m[None],out=np.zeros_like(E),where=m[None]>0)
    entropy=np.zeros_like(post);positive=post>0
    entropy[positive]=post[positive]*np.log2(post[positive])
    return dict(information=float(2+entropy.sum(axis=0)@m),
                brier=float((post*post).sum(axis=0)@m-.25),
                mean=float(b.decision_values(E).mean()),
                each=b.decision_values(E).tolist())


def native(E,Qs,weights):
    ds=np.array([a.decoder_error(E,Q) for Q in Qs])
    return float(weights@ds),ds


def check_score_identity():
    examples=[];tested=0
    for counts in itertools.product(range(13),repeat=3):
        last=12-sum(counts)
        if last<0:continue
        p=[F(c,12) for c in (*counts,last)]
        probs=[sum(p[i] for i in range(4) if label[i]) for label in b.LABELS]
        mean_accuracy=sum(max(q,1-q) for q in probs)/7
        mean_quadratic=sum(q*q+(1-q)*(1-q) for q in probs)/7
        norm=sum(q*q for q in p)
        assert mean_quadratic==(3+4*norm)/7
        top=max(p);bottom=min(p)
        singleton=(3 if top<=F(1,2) else 2+2*top)
        assert mean_accuracy==(singleton+max(1+2*top,2-2*bottom))/7
        if top>=F(1,2):assert mean_accuracy==(3+4*top)/7
        tested+=1
    for p in [[F(3,5),F(2,5),0,0],[F(2,3),F(1,9),F(1,9),F(1,9)]]:
        probs=[sum(p[i] for i in range(4) if label[i]) for label in b.LABELS]
        examples.append(dict(posterior=[str(x) for x in p],
                             squared_norm=str(sum(q*q for q in p)),
                             mean_accuracy=str(sum(max(q,1-q) for q in probs)/7)))
    return dict(rational_vectors_checked=tested,ranking_reversal_vectors=examples,
                identity='mean binary quadratic potential = (3+4*sum(p_i^2))/7',
                accuracy_when_max_p_at_least_half='(3+4*max(p_i))/7')


def main():
    out=HERE/'results';out.mkdir(exist_ok=True)
    design=json.loads((PARENT/'results/design.json').read_text())
    result=dict(scope='Exploratory analysis of frozen H=3 results; numerical LPs and exact rational score checks.',
                parent_compute_sha256=digest(PARENT/'compute.py'),
                parent_auditor_sha256=digest(PARENT/'audit.py'),
                analysis_sha256=digest(Path(__file__)),
                score_identity=check_score_identity(),cases=[],simple_schedules=[])
    for case in design['cases']:
        folder=PARENT/'results'/case['name']
        meta=json.loads((folder/'results.json').read_text())
        model=np.load(folder/'model.npz');lev=b.levels(3)
        p=b.masses(model['T'],model['Z'],lev)
        raw=np.array([p[h] for h in lev[-1]]).T
        targets=b.target_library(model['T'],model['Z'])
        Qs=[t['kernel'] for t in targets];weights=np.array([t['weight'] for t in targets])
        rewards=b.reward_coefficients(lev,p)
        c=np.array([sum(max(p[h][label==d].sum()/4 for d in [0,1]) for label in b.LABELS)/7 for h in lev[-1]])
        optima={r['objective']:r for r in meta['optima']}
        row=dict(name=case['name'],family=case['family'],best_native=[],cross_scores=[],
                 native_vs_brier_saved_pair=next(x for x in meta['optimum_pair_witnesses'] if x['objective']=='brier'))
        template,w,x,allocations,ds=b.program(lev,p,targets,'native_weighted',rewards)
        for fraction in [0.,.01,.05]:
            endpoint=next(r for r in meta['endpoints'] if r['objective']=='native_weighted' and r['fraction']==fraction and r['purpose']=='mean_seven')
            lp=copy.deepcopy(template);original=np.array(lp.cost)
            lp.row({i:float(v) for i,v in enumerate(original) if v},endpoint['threshold'])
            lp.cost=[0.]*len(lp.cost)
            for h,value in zip(lev[-1],c):lp.cost[w[h]]=-float(value)
            stem=f'{case["name"]}_native_best_f{fraction}'
            sol,cert=b.core.solve(lp,out/(stem+'.npz'))
            E,rows,rw=b.replay(lev,p,x,sol)
            actual,actual_ds=native(E,Qs,weights)
            value=score(E,raw,lev[-1])['mean']
            a.check('best_mean_value',value+sol.fun)
            a.check('best_native_feasibility',max(0,actual-endpoint['threshold']))
            a.certificate(out/(stem+'.npz'))
            literal=np.array([a.literal_probability(model['T'],model['Z'],h) for h in lev[-1]]).T
            a.check('independent_source_masses',literal-raw)
            np.savez_compressed(out/(stem+'_policy.npz'),E=E,rows=rows,weights=rw,
                                target_errors=actual_ds)
            row['best_native'].append(dict(fraction=fraction,best=value,worst=endpoint['value'],
                                           native_cost=actual,threshold=endpoint['threshold']))
        for objective in ['native_weighted','information','brier']:
            for fraction in [0.,.01]:
                data=np.load(folder/f'{objective}_f{fraction}_mean_seven_policy.npz')
                E=data['E'];ss=score(E,raw,lev[-1]);cost,errors=native(E,Qs,weights)
                brier_width=optima['brier']['range'];native_width=optima['native_weighted']['range']
                row['cross_scores'].append(dict(objective=objective,fraction=fraction,
                    root_L=float(data['rows'][0,0]),native_cost=cost,errors=errors.tolist(),**ss,
                    native_regret_fraction=(cost-optima['native_weighted']['cost'])/native_width if native_width>1e-12 else None,
                    brier_regret_fraction=(-ss['brier']-optima['brier']['cost'])/brier_width if brier_width>1e-12 else None))
        row['targets']=[t['name'] for t in targets]
        row['weights']=weights.tolist()
        row['oracle_mean']=meta['unconstrained_best_mean']
        result['cases'].append(row)
        if case['name'] in ['delayed_0.25_0.1','sensors_0.1_0.3','irreversible_0.1_0.3']:
            for word in itertools.product(range(2),repeat=3):
                mask=np.array([tuple(aa for aa,oo in h)==word for h in lev[-1]],float)
                E=raw*mask;ss=score(E,raw,lev[-1]);cost,errors=native(E,Qs,weights)
                result['simple_schedules'].append(dict(case=case['name'],word=''.join('LR'[x] for x in word),
                                                       native_cost=cost,**ss))
        print(case['name'],'analysis complete',flush=True)
    result['verification']=dict(status='passed',checks=a.COUNT,max_errors=a.ERRORS,
                                maximum_residual=max(a.ERRORS.values()))
    (HERE/'results.json').write_text(json.dumps(result,indent=2,allow_nan=False)+'\n')
    for row in result['cases']:
        zero=row['best_native'][0]
        brier=next(s for s in row['cross_scores'] if s['objective']=='brier' and s['fraction']==0)
        print(row['name'],'native worst/best/Brier',zero['worst'],zero['best'],brier['mean'])


if __name__=='__main__':main()
