#!/usr/bin/env python3
"""Linear policy oracle on the exact native-repeats optimum face.

Histories with equal signed observation counts have proportional likelihood
columns. Their 28-state experiment is exactly equivalent for each fixed policy;
the inverse garbling depends on that policy but not on the world.

The exact Bellman restriction is necessary for native optimality. Inside it,
delta(E,LR)=0 and delta(E,LLL)+delta(E,RRR)<=.072 characterize the original
weighted cost sublevel S<=.0072: LR garbles to L, R, and the tagged target.
Repeated targets are compressed to their sufficient Binomial3 count.
"""
from pathlib import Path
from fractions import Fraction as Q
import importlib.util
import json
import sys
import time

import numpy as np
from scipy.optimize import linprog

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location('sharp_search_compressed_oracle',HERE/'search.py')
SEARCH = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = SEARCH
SPEC.loader.exec_module(SEARCH)
BASE = SEARCH.BASE


def signed_counts(h):
    return tuple(sum(2*o-1 for a,o in h if a==side) for side in (0,1))


def compressed_targets():
    answer = {}
    for target in BASE.target_library((.1,.1)):
        if target['name'] not in ('LR','LLL','RRR','adaptive_L'):
            continue
        groups = {}
        for y,h in enumerate(target['signals']):
            if target['name'] in ('LLL','RRR'):
                key = sum(o for _,o in h)
            elif target['name']=='adaptive_L':
                key = (h[0][1],sum(o for _,o in h[1:]))
            else:
                key = tuple(o for _,o in h)
            groups.setdefault(key,[]).append(y)
        full = [[np.prod([Q(9,10) if o==theta[a] else Q(1,10) for a,o in h])
                 for h in target['signals']] for theta in BASE.WORLDS]
        for group in groups.values():
            assert all(full[t][i]==full[t][group[0]] for t in range(4) for i in group)
        exact = [[sum(full[t][i] for i in group) for group in groups.values()] for t in range(4)]
        assert all(sum(row)==1 for row in exact)
        answer[target['name']] = {'exact':exact,'kernel':np.asarray(exact,dtype=float),
                                 'groups':list(groups.values()),'labels':list(groups),
                                 'full':full}
    return answer


class CompressedPolicyOracle:
    """Maximize coefficients @ state_weights on the exact native optimum face.

    Public properties: rays (4,S), states (ordered signed-count pairs), histories
    (all625 parent terminal histories), reachable, targets, target_kernels.
    optimize returns value, dual_upper_bound, state_weights, source_kernel (4,S),
    full_source_kernel (4,625), action_rows (156,3), realization_weights,
    residuals and native_epigraph_cost. Bounds are float64 solver certificates.
    """
    def __init__(self,cost_bound=.0072,exact_face=True):
        if not exact_face or Q(str(cost_bound))!=Q(9,1250):
            raise ValueError('This compressed oracle is only for the exact S<=9/1250 face')
        self.cost_bound=float(cost_bound)
        self.exact_face=True
        self.bellman=SEARCH.exact_bellman()
        self.levels=self.bellman['levels']; self.histories=self.levels[-1]
        p=self.bellman['prefix_laws']; allowed=self.bellman['allowed']
        self.reachable=[[()]]
        for _ in range(4):
            self.reachable.append([h+((a,o),) for h in self.reachable[-1]
                                   for a,o in BASE.EDGES if a in allowed[h]])
        self.states=sorted({signed_counts(h) for h in self.reachable[-1]})
        self.state_index={s:i for i,s in enumerate(self.states)}
        self.exact_rays=[]
        for state in self.states:
            h=next(h for h in self.reachable[-1] if signed_counts(h)==state)
            scale=max(p[h]); ray=[q/scale for q in p[h]]
            self.exact_rays.append(ray)
        self.rays=np.asarray(self.exact_rays,dtype=float).T
        self.history_state=np.asarray([self.state_index.get(signed_counts(h),-1) for h in self.histories])
        self.history_scale=np.asarray([float(max(p[h])) for h in self.histories])
        for h in self.reachable[-1]:
            s=self.state_index[signed_counts(h)]
            assert all(p[h][t]==max(p[h])*self.exact_rays[s][t] for t in range(4))
        self.targets=compressed_targets()
        self.target_kernels={name:t['kernel'] for name,t in self.targets.items()}
        lp=BASE.LP(); self.lp=lp
        self.w={h:lp.var() for layer in self.reachable for h in layer}
        self.x={}
        lp.row({self.w[()]:1},1,True)
        for layer in self.reachable[:-1]:
            for h in layer:
                row={self.w[h]:-1}
                for a in allowed[h]:
                    var=lp.var(); self.x[h,a]=var; row[var]=1
                    for aa,o in BASE.EDGES:
                        if aa==a:
                            lp.row({self.w[h+((a,o),)]:1,var:-1},0,True)
                lp.row(row,0,True)
        self.z=np.asarray([lp.var() for _ in self.states])
        for state,s in self.state_index.items():
            row={self.w[h]:float(max(p[h])) for h in self.reachable[-1] if signed_counts(h)==state}
            lp.row(row|{self.z[s]:-1},0,True)
        self.deficit_indices={}; self.allocation_indices={}
        for name in ('LR','LLL','RRR'):
            T=self.target_kernels[name]; Y=T.shape[1]
            alloc=np.asarray([[lp.var() for _ in range(Y)] for _ in self.states])
            self.allocation_indices[name]=alloc
            for s in range(len(self.states)):
                lp.row({i:1 for i in alloc[s]}|{self.z[s]:-1},0,True)
            if name!='LR':
                deficit=lp.var(); self.deficit_indices[name]=deficit
            for theta in range(4):
                errs=[]
                for y in range(Y):
                    row={alloc[s,y]:self.rays[theta,s] for s in range(len(self.states))}
                    if name=='LR':
                        lp.row(row,T[theta,y],True)
                    else:
                        error=lp.var(); errs.append(error)
                        lp.row(row|{error:-1},T[theta,y])
                        lp.row({i:-v for i,v in row.items()}|{error:-1},-T[theta,y])
                if name!='LR':
                    lp.row({i:.5 for i in errs}|{deficit:-1},0)
        lp.row({i:1 for i in self.deficit_indices.values()},.072)
        self.ae=lp.matrix(lp.eq);self.au=lp.matrix(lp.ub)
        self.be=np.asarray([b for _,b in lp.eq]);self.bu=np.asarray([b for _,b in lp.ub])
        self.bounds=np.asarray(lp.bounds)
        self.calls=0;self.total_seconds=0.

    def optimize(self,coefficients,certificate_path=None):
        coefficients=np.asarray(coefficients,dtype=float)
        if coefficients.shape!=(len(self.states),):
            raise ValueError(f'Expected {len(self.states)} state coefficients')
        c=np.zeros(len(self.lp.cost));c[self.z]=-coefficients
        start=time.monotonic()
        sol=linprog(c,A_eq=self.ae,b_eq=self.be,A_ub=self.au,b_ub=self.bu,
                    bounds=self.lp.bounds,method=SEARCH.METHOD,options=SEARCH.OPTIONS)
        seconds=time.monotonic()-start;self.calls+=1;self.total_seconds+=seconds
        if not sol.success:
            raise RuntimeError(sol.message)
        lo,hi=self.bounds.T
        dual=float(self.be@sol.eqlin.marginals+self.bu@sol.ineqlin.marginals+
                   lo@sol.lower.marginals+hi@sol.upper.marginals)
        residuals={'equality':float(np.max(abs(self.ae@sol.x-self.be),initial=0)),
                   'inequality':float(np.max(self.au@sol.x-self.bu,initial=0)),
                   'bounds':float(np.max(np.maximum(lo-sol.x,sol.x-hi),initial=0)),
                   'stationarity':float(np.max(abs(c-self.ae.T@sol.eqlin.marginals-
                                       self.au.T@sol.ineqlin.marginals-sol.lower.marginals-sol.upper.marginals),initial=0)),
                   'duality_gap':abs(float(sol.fun)-dual)}
        assert max(residuals.values())<=5e-8,residuals
        action_rows=[]
        for layer in self.levels[:-1]:
            for h in layer:
                row=np.zeros(3)
                if h in self.w and sol.x[self.w[h]]>1e-12:
                    for a in range(3):
                        if (h,a) in self.x:
                            row[a]=max(0.,sol.x[self.x[h,a]]/sol.x[self.w[h]])
                    row/=row.sum()
                else:
                    row[self.bellman['allowed'][h][0]]=1.
                action_rows.append(row)
        action_rows=np.asarray(action_rows)
        weights=BASE.realization(self.levels,action_rows)
        full=BASE.experiment(self.levels,{h:np.asarray(v,dtype=float)
                             for h,v in self.bellman['prefix_laws'].items()},weights)
        state_weights=sol.x[self.z]
        source=self.rays*state_weights
        compressed=np.asarray([full[:,self.history_state==s].sum(axis=1) for s in range(len(self.states))]).T
        residuals['policy_replay']=float(np.max(abs(compressed-source),initial=0))
        assert residuals['policy_replay']<=5e-8,residuals
        if certificate_path is not None:
            self.lp.cost=c.tolist()
            arrays=BASE.certificate_arrays(self.lp,sol,self.ae,self.au,self.be,self.bu)
            arrays.update(state_indices=self.z,state_coefficients=coefficients,rays=self.rays,
                          states=np.asarray(self.states),source_kernel=source,action_rows=action_rows,
                          full_source_kernel=full,history_state=self.history_state,
                          history_scale=self.history_scale,
                          native_deficit_indices=np.asarray(list(self.deficit_indices.values())))
            np.savez_compressed(certificate_path,**arrays)
        return {'value':float(coefficients@state_weights),'dual_upper_bound':-dual,
                'state_weights':state_weights,'source_kernel':source,'full_source_kernel':full,
                'action_rows':action_rows,'policy':action_rows,
                'realization_weights':np.asarray([weights[h] for layer in self.levels for h in layer]),
                'solution':sol,'solver_seconds':seconds,'residuals':residuals,
                'native_epigraph_cost':.1*sum(sol.x[i] for i in self.deficit_indices.values())}

    maximize=optimize

    def export_metadata(self,path):
        SEARCH.write_json(path,{'source_sha256':SEARCH.digest(__file__),
            'search_sha256':SEARCH.digest(HERE/'search.py'),
            'parent_compute_sha256':SEARCH.digest(HERE.parent/'compute.py'),
            'cost_bound':'9/1250','bellman_root_value':'234/125',
            'states':self.states,'rays':[[str(v) for v in row] for row in self.exact_rays],
            'rays_orientation':'state by world; API numpy rays is world by state',
            'reachable_sizes':[len(x) for x in self.reachable],
            'terminal_histories':self.histories,'history_state':self.history_state.tolist(),
            'history_scale':[str(max(self.bellman['prefix_laws'][h])) for h in self.histories],
            'targets':{name:{'rows':[[str(v) for v in row] for row in t['exact']],
                             'groups':t['groups'],'labels':t['labels'],
                             'full_rows':[[str(v) for v in row] for row in t['full']]}
                       for name,t in self.targets.items()},
            'variables':len(self.lp.cost),'equalities':len(self.lp.eq),'inequalities':len(self.lp.ub),
            'native_constraints':'LR exact; triple-count deficiency sum <=9/125; necessary exact Bellman face'})


def smoke():
    oracle=CompressedPolicyOracle()
    oracle.export_metadata(HERE/'compressed_oracle_metadata.json')
    rng=np.random.default_rng(9132026)
    reports=[]
    old=SEARCH.PolicyOracle(exact_face=True)
    for k in range(3):
        coefficient=rng.normal(size=len(oracle.states))
        got=oracle.optimize(coefficient,HERE/f'compressed_oracle_smoke_{k}.npz')
        full=np.asarray([coefficient[s]*scale if s>=0 else 0.
                         for s,scale in zip(oracle.history_state,oracle.history_scale)])
        reference=old.optimize(full)
        errors={name:BASE.fixed_deficiency(got['full_source_kernel'],T)[0]
                for name,T in old.target_kernels.items() if name in ('L','R','tagged','LR','LLL','RRR','adaptive_L')}
        cost=sum(t['weight']*errors[t['name']] for t in old.targets[:6])
        assert abs(got['value']-reference['value'])<=1e-8
        assert cost<=.0072+1e-8
        reports.append({'test':k,'value':got['value'],'full_oracle_value':reference['value'],
                        'native_recomputed_cost':cost,'target_deficiencies':errors,
                        'compressed_seconds':got['solver_seconds'],'full_seconds':reference['solver_seconds'],
                        'residuals':got['residuals']})
    report={'status':'passed_smoke','source_sha256':SEARCH.digest(__file__),
            'states':len(oracle.states),'variables':len(oracle.lp.cost),'tests':reports}
    SEARCH.write_json(HERE/'compressed_oracle_smoke.json',report)
    print(json.dumps(report,indent=2))


if __name__=='__main__':
    smoke()
