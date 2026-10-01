#!/usr/bin/env python3
"""Bounded lower-witness search and a reusable full-policy separation oracle.

Alternating a target-deficiency dual with a policy best response supplies lower
witnesses only. It is not a global convex-maximization certificate. The oracle
optimizes a LINEAR functional of terminal policy realization weights over the
actual native weighted-loss sublevel, never a maximized deficiency epigraph.

API: oracle=PolicyOracle(cost_bound=.0072, exact_face=True)
     result=oracle.optimize(coefficients)  # maximize sum_h coefficients[h]*w[h]
Terminal history order is oracle.levels[-1], identical to the frozen parent.
Result keys include value, dual_upper_bound, source_kernel, action_rows,
realization_weights, terminal_weights, solution, solver_seconds, residuals.
All returned LP bounds are float64 numerical certificates, not interval bounds.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
from fractions import Fraction as Q
import hashlib
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys
import time
import traceback

import numpy as np
from scipy.optimize import linprog

HERE=Path(__file__).resolve().parent
PARENT=HERE.parent
SPEC=importlib.util.spec_from_file_location('frozen_noisy_planner_for_sharp',PARENT/'compute.py')
BASE=importlib.util.module_from_spec(SPEC);sys.modules[SPEC.name]=BASE;SPEC.loader.exec_module(BASE)
TOL=5e-8
S_OPT=Q(9,1250)
METHOD='highs-ipm'
OPTIONS={'primal_feasibility_tolerance':1e-9,'dual_feasibility_tolerance':1e-9,
         'ipm_optimality_tolerance':1e-10}


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write_json(path,value):
    path=Path(path);temporary=path.with_suffix(path.suffix+'.tmp')
    temporary.write_text(json.dumps(value,indent=2,allow_nan=False)+'\n');temporary.replace(path)


def exact_bellman(H=4):
    """Exact terminal sum of uniform Bayes accuracies for U and V."""
    levels=BASE.histories(H);p={():[Q(1)]*4}
    for layer in levels[:-1]:
        for h in layer:
            for a,o in BASE.EDGES:
                p[h+((a,o),)]=[mass*(Q(1) if a==2 else Q(9,10) if int(theta[a])==o else Q(1,10))
                               for mass,theta in zip(p[h],BASE.WORLDS)]
    value={}
    for h in levels[-1]:
        value[h]=sum(max(sum(p[h][i]/4 for i,theta in enumerate(BASE.WORLDS) if theta[side]==decision)
                         for decision in (0,1)) for side in (0,1))
    allowed={};qvalues={}
    for layer in reversed(levels[:-1]):
        for h in layer:
            qs=[sum(value[h+((a,o),)] for aa,o in BASE.EDGES if aa==a) for a in range(3)]
            value[h]=max(qs);qvalues[h]=qs
            allowed[h]=tuple(a for a,q in enumerate(qs) if q==value[h])
    assert value[()]==Q(234,125) if H==4 else True
    return {'levels':levels,'prefix_laws':p,'value':value,'qvalues':qvalues,'allowed':allowed}


def export_bellman(data,path):
    active={()}
    for layer in data['levels'][:-1]:
        for h in layer:
            if h in active:
                active.update(h+((a,o),) for a,o in BASE.EDGES if a in data['allowed'][h])
    rows=[]
    for layer in data['levels'][:-1]:
        for h in layer:
            rows.append({'history':h,'value':str(data['value'][h]),
                         'action_values':list(map(str,data['qvalues'][h])),
                         'advantages':[str(data['value'][h]-q) for q in data['qvalues'][h]],
                         'allowed_actions':data['allowed'][h],'reachable_on_optimal_face':h in active})
    report={'status':'exact_rational_bellman','H':len(data['levels'])-1,
            'root_value':str(data['value'][()]),'native_lower_bound':str(Q(1,10)*(2*Q(243,250)-data['value'][()])),
            'rows':rows,'terminal_coefficients':[str(data['value'][h]) for h in data['levels'][-1]],
            'reachable_terminal_histories':sum(h in active for h in data['levels'][-1]),
            'allowed_actions_reachable':sum(len(data['allowed'][h]) for h in data['allowed'] if h in active),
            'scope':'Necessary optimal-face restriction only; native constraints remain in the oracle'}
    write_json(path,report)
    return report


class PolicyOracle:
    """Maximize a terminal-w linear functional over S<=cost_bound.

    exact_face=True is permitted only at exactly9/1250. It removes actions
    with strictly positive EXACT Bellman advantage and fixes the four cheaper
    diagnostic deficits to zero. Necessity follows from
    S >= .1*(2*.972 - V_U - V_V) >= .0072; no converse is assumed.
    """
    def __init__(self,cost_bound=.0072,exact_face=False):
        if exact_face and Q(str(cost_bound))!=S_OPT:
            raise ValueError('Exact face restriction applies only to S<=9/1250')
        self.cost_bound=float(cost_bound);self.exact_face=exact_face
        self.targets=BASE.target_library((.1,.1))
        self.model=BASE.model(4,(.1,.1),self.targets,'native_repeats',None)
        m=self.model;self.levels=m.levels
        self.histories=self.levels[-1]
        self.prefix_laws=np.stack([m.p[h] for h in self.histories],axis=1)
        self.target_kernels={t['name']:t['kernel'] for t in self.targets}
        self.original_cost=np.asarray(m.lp.cost).copy()
        m.lp.row({i:float(c) for i,c in enumerate(self.original_cost) if c},self.cost_bound)
        self.bellman=exact_bellman()
        self.fixed_action_variables=0
        if exact_face:
            for h,allowed in self.bellman['allowed'].items():
                for a in range(3):
                    if a not in allowed:
                        m.lp.bounds[m.x[h,a]]=(0.,0.);self.fixed_action_variables+=1
            for name in ('L','R','tagged','LR'):
                m.lp.bounds[m.deficit_indices[name]]=(0.,0.)
        self.ae=m.lp.matrix(m.lp.eq);self.au=m.lp.matrix(m.lp.ub)
        self.be=np.asarray([b for _,b in m.lp.eq]);self.bu=np.asarray([b for _,b in m.lp.ub])
        self.bounds=np.asarray(m.lp.bounds);self.w_indices=np.asarray([m.w[h] for h in self.histories])
        self.calls=0;self.total_seconds=0.

    def optimize(self,coefficients,certificate_path=None):
        coefficients=np.asarray(coefficients,dtype=float)
        if coefficients.shape!=(len(self.histories),):
            raise ValueError(f'Expected {len(self.histories)} terminal coefficients')
        c=np.zeros(len(self.model.lp.cost));c[self.w_indices]=-coefficients
        start=time.monotonic()
        sol=linprog(c,A_eq=self.ae,b_eq=self.be,A_ub=self.au,b_ub=self.bu,
                    bounds=self.model.lp.bounds,method=METHOD,options=OPTIONS)
        seconds=time.monotonic()-start;self.calls+=1;self.total_seconds+=seconds
        if not sol.success:
            raise RuntimeError(sol.message)
        lo,hi=self.bounds.T
        dual=float(self.be@sol.eqlin.marginals+self.bu@sol.ineqlin.marginals+
                   lo@sol.lower.marginals+hi@sol.upper.marginals)
        residuals={'equality':float(np.max(abs(self.ae@sol.x-self.be),initial=0)),
                   'inequality':float(np.max(np.maximum(self.au@sol.x-self.bu,0),initial=0)),
                   'bounds':float(np.max(np.maximum(np.maximum(lo-sol.x,sol.x-hi),0),initial=0)),
                   'stationarity':float(np.max(abs(c-self.ae.T@sol.eqlin.marginals-
                                        self.au.T@sol.ineqlin.marginals-sol.lower.marginals-sol.upper.marginals),initial=0)),
                   'duality_gap':abs(float(sol.fun)-dual)}
        assert max(residuals.values())<=TOL,residuals
        E,actions,weights=BASE.replay(self.model,sol)
        terminal=np.asarray([weights[h] for h in self.histories])
        value=float(coefficients@terminal)
        assert abs(value+sol.fun)<=TOL
        if certificate_path is not None:
            old=self.model.lp.cost;self.model.lp.cost=c.tolist()
            arrays=BASE.certificate_arrays(self.model.lp,sol,self.ae,self.au,self.be,self.bu)
            self.model.lp.cost=old
            arrays.update(BASE.bindings(self.model))
            arrays['original_native_cost']=self.original_cost
            arrays['terminal_coefficients']=coefficients
            np.savez_compressed(certificate_path,**arrays)
        return {'value':value,'dual_upper_bound':-dual,'source_kernel':E,'action_rows':actions,
                'realization_weights':np.asarray([weights[h] for layer in self.levels for h in layer]),
                'terminal_weights':terminal,'solution':sol,'solver_seconds':seconds,'residuals':residuals,
                'native_epigraph_cost':float(self.original_cost@sol.x)}

    maximize=optimize


def schedule_source(oracle,word='RRRL'):
    actions=np.asarray([np.eye(3)[int(word[len(h)]=='R')] for layer in oracle.levels[:-1] for h in layer])
    weights=BASE.realization(oracle.levels,actions)
    E=BASE.experiment(oracle.levels,oracle.model.p,weights)
    return E,actions,np.asarray([weights[h] for layer in oracle.levels for h in layer])


def fixed_dual(E,T):
    value,witness=BASE.fixed_deficiency(E,T)
    return value,witness


def clean_dual(alpha,b):
    alpha=np.maximum(alpha,0);alpha=alpha/alpha.sum()
    return alpha,np.minimum(np.maximum(b,0),alpha[:,None])


def old_dual_pool(oracle,max_selected):
    pool=[];seen=set();provenance=[];aggregate=hashlib.sha256();total=0
    reference,_,_=schedule_source(oracle)
    T=oracle.target_kernels['adaptive_L']
    for folder in ('results','results_h4'):
        index=PARENT/folder/'results.json';data=json.loads(index.read_text())
        provenance.append({'path':str(index.relative_to(HERE.parent)),'sha256':digest(index)})
        for row in data['optima']+data['rows']:
            path=PARENT/folder/row['deficiency_witness_path'];total+=1
            file_hash=digest(path);aggregate.update((str(path.relative_to(PARENT))+file_hash).encode())
            with np.load(path) as values:
                alpha,b=clean_dual(values['adaptive_L__dual_alpha'],values['adaptive_L__dual_b'])
            key=tuple(np.round(b,11).ravel())
            if key in seen:
                continue
            seen.add(key)
            gap=float(np.sum(T*b)-np.max(reference.T@b,axis=1).sum())
            pool.append({'id':row['id'],'path':str(path.relative_to(PARENT)),'sha256':file_hash,
                         'alpha':alpha,'b':b,'reference_lower_value':gap})
    selected=[]
    if pool:
        first=max(range(len(pool)),key=lambda i:pool[i]['reference_lower_value'])
        selected.append(pool.pop(first))
    while pool and len(selected)<max_selected:
        index=max(range(len(pool)),key=lambda i:min(float(np.linalg.norm(pool[i]['b']-x['b'])) for x in selected))
        selected.append(pool.pop(index))
    return selected,{'parent_collectors_scanned':total,'distinct_duals':len(seen),
                     'selected':len(selected),'parent_indices':provenance,'all_witness_files_sha256':aggregate.hexdigest()}


def verify_collector(oracle,E):
    errors={};witnesses={}
    for target in oracle.targets:
        if target['name'] not in ('L','R','tagged','LR','LLL','RRR','adaptive_L'):
            continue
        error,wit=BASE.fixed_deficiency(E,target['kernel']);errors[target['name']]=error
        witnesses.update({target['name']+'__'+k:v for k,v in wit.items()})
    cost=sum(t['weight']*errors[t['name']] for t in oracle.targets[:6])
    assert cost<=oracle.cost_bound+TOL,(cost,oracle.cost_bound)
    return cost,errors,witnesses


def run(args):
    start=time.monotonic();out=HERE/('smoke' if args.mode=='smoke' else 'numeric_search')
    out.mkdir(exist_ok=True)
    protocol=HERE/'PROTOCOL.md'
    if args.mode=='production' and not protocol.exists():
        raise RuntimeError('Production requires frozen protocol')
    oracle=PolicyOracle(args.cost_bound,args.exact_face)
    bellman=export_bellman(oracle.bellman,HERE/'bellman_search.json')
    report={'status':'running','mode':args.mode,'source_sha256':digest(__file__),
            'parent_compute_sha256':digest(PARENT/'compute.py'),
            'protocol_sha256':digest(protocol) if protocol.exists() else None,
            'cost_bound':args.cost_bound,'exact_face_reduction':args.exact_face,
            'fixed_action_variables':oracle.fixed_action_variables,
            'bellman_root_value':bellman['root_value'],'starts':[],'improvements':[],
            'claim':'Bounded alternating search produces lower witnesses only; no global upper claim',
            'failures':[]}
    T=oracle.target_kernels['adaptive_L']
    E,actions,weights=schedule_source(oracle)
    cost,errors,witnesses=verify_collector(oracle,E)
    best=errors['adaptive_L']
    np.savez_compressed(out/'best_policy.npz',source_kernel=E,action_rows=actions,
                        realization_weights=weights,**witnesses)
    report['best']={'adaptive_deficiency':best,'native_cost':cost,'target_deficiencies':errors,
                    'origin':'RRRL','policy_path':'best_policy.npz'}
    old,provenance=old_dual_pool(oracle,min(20,args.starts))
    report['seed_pool']=provenance
    seeds=[{'id':'parent_'+str(k),'origin':x['id'],'b':x['b']} for k,x in enumerate(old)]
    rng=np.random.default_rng(args.seed)
    while len(seeds)<args.starts:
        alpha=rng.dirichlet(np.ones(4));b=rng.uniform(size=(4,8))*alpha[:,None]
        seeds.append({'id':'random_'+str(len(seeds)),'origin':'random dual purpose','b':b})
    report['settings']={'starts':args.starts,'iterations':args.iterations,'seed':args.seed,
                        'solver':METHOD,'solver_options':OPTIONS,'tolerance':TOL}
    def checkpoint():
        report['runtime_seconds']=time.monotonic()-start;report['oracle_calls']=oracle.calls
        report['oracle_solver_seconds']=oracle.total_seconds
        write_json(out/'results.json',report)
    checkpoint()
    try:
        for seed in seeds:
            b=seed['b'];trace=[];previous=None
            for iteration in range(args.iterations):
                coefficients=np.max(oracle.prefix_laws.T@b,axis=1)
                result=oracle.optimize(-coefficients)
                value,wit=fixed_dual(result['source_kernel'],T)
                lower=float(np.sum(T*b)+result['value'])
                assert lower<=value+TOL
                if previous is not None:
                    assert value+TOL>=previous,(seed['id'],previous,value)
                trace.append({'iteration':iteration,'adaptive_deficiency':value,
                              'fixed_dual_lower_value':lower,'solver_seconds':result['solver_seconds'],
                              'residuals':result['residuals'],'native_epigraph_cost':result['native_epigraph_cost']})
                if value>best+1e-9:
                    cost,errors,witnesses=verify_collector(oracle,result['source_kernel'])
                    best=value
                    policy_name=f"improvement_{len(report['improvements']):02d}.npz"
                    np.savez_compressed(out/policy_name,source_kernel=result['source_kernel'],
                                        action_rows=result['action_rows'],realization_weights=result['realization_weights'],**witnesses)
                    info={'adaptive_deficiency':value,'native_cost':cost,'target_deficiencies':errors,
                          'origin':seed['origin'],'iteration':iteration,'policy_path':policy_name}
                    report['improvements'].append(info);report['best']=info
                if previous is not None and value<=previous+1e-9:
                    break
                previous=value;b=wit['dual_b']
            report['starts'].append({'id':seed['id'],'origin':seed['origin'],'trace':trace})
            checkpoint();print(seed['id'],'best',best,'steps',len(trace),flush=True)
        # Save a reproducible separation certificate for the final target dual.
        best_path=out/report['best']['policy_path']
        with np.load(best_path) as data:
            E=data['source_kernel']
        _,wit=fixed_dual(E,T)
        coefficients=-np.max(oracle.prefix_laws.T@wit['dual_b'],axis=1)
        final=oracle.optimize(coefficients,out/'final_separation_certificate.npz')
        report['final_fixed_dual_policy_value']=float(np.sum(T*wit['dual_b'])+final['value'])
        report['status']='passed_development_smoke' if args.mode=='smoke' else 'completed_bounded_lower_search'
        checkpoint();print(json.dumps({'status':report['status'],'best':report['best'],
                          'oracle_calls':oracle.calls,'seconds':report['runtime_seconds']},indent=2),flush=True)
    except Exception:
        report['status']='failed';report['failures'].append(traceback.format_exc());checkpoint();raise


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mode',choices=('smoke','production'),default='smoke')
    parser.add_argument('--cost-bound',type=float,default=.0072)
    parser.add_argument('--exact-face',action='store_true')
    parser.add_argument('--starts',type=int,default=3)
    parser.add_argument('--iterations',type=int,default=8)
    parser.add_argument('--seed',type=int,default=9132026)
    run(parser.parse_args())
