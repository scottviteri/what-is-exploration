#!/usr/bin/env python3
"""Bounded dual-cut decomposition pilots for finite native objectives."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import sys
import time

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'deps'))
sys.dont_write_bytecode=True
import numpy as np
import scipy
from scipy import sparse
import highspy
import scaling_core as core
from certified_decoder import StableDecoder

OLD=HERE.parents[1]/'native_objective_benchmark_2026-09-15/results'
TOL=2e-7
GAP=2e-7
CASES=['sensors_0.1_0.3','irreversible_0.1_0.1','hmm_91501_0.2']
SEED=923230


def digest(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def atomic(path,data):
    temp=path.with_suffix('.tmp');temp.write_text(json.dumps(data,indent=2,allow_nan=False)+'\n');temp.replace(path)
def positive_max(v):return float(np.max(np.maximum(v,0),initial=0))


def validate_experiment(E,F):
    for name,array in [('source',E),('target',F)]:
        if array.ndim!=2 or not np.isfinite(array).all() or np.any(array<0) or np.max(abs(array.sum(1)-1))>1e-9:
            raise ValueError('Invalid original '+name)
    if E.shape[0]!=F.shape[0]:raise ValueError('Hypothesis class mismatch')


def realization(g,rows):
    weights={():1.};action=np.zeros(g.flow.shape[1])
    for i,h in enumerate(g.decisions):
        for a in range(2):
            action[2*i+a]=weights[h]*rows[i,a]
            for o in range(2):weights[h+((a,o),)]=action[2*i+a]
    return action


def make_cut(g,F,witness):
    a=np.asarray(witness['alpha']);b=np.asarray(witness['b'])
    residual=max(abs(float(a.sum())-1),positive_max(-a),positive_max(-b),positive_max(b-a[:,None]))
    if not np.isfinite(a).all() or not np.isfinite(b).all() or not np.isfinite(residual) or residual>TOL:raise RuntimeError('Invalid cut dual witness')
    leaf_slope=np.max(g.raw.T@b,axis=1)
    # ALL syntactic histories are included, including zero-probability incumbent columns.
    slope=np.bincount(g.leaf_index,weights=leaf_slope,minlength=g.flow.shape[1])
    intercept=float(np.sum(F*b))
    return intercept,slope,residual


def oracle(g,E,rows,targets,deadline):
    started=time.perf_counter();action=realization(g,rows)
    decoders={};upper=[];lower=[];cuts=[];saved=[];fallbacks=0;solver_seconds=0.;build_seconds=0.
    for j,target in enumerate(targets):
        if time.perf_counter()>=deadline:raise TimeoutError('Objective audit time cap')
        F=target['kernel'];validate_experiment(E,F);Y=F.shape[1]
        if Y not in decoders:
            ts=time.perf_counter();decoders[Y]=StableDecoder(E,Y,time_limit=max(.01,min(5.,deadline-time.perf_counter())))
            build_seconds+=time.perf_counter()-ts
        report,w=decoders[Y].solve(F)
        G=w['decoder'];a=w['alpha'];b=w['b'];source=E[:,w['source_indices']]
        residual=max(float(np.max(abs(G.sum(1)-1))),positive_max(-G),abs(float(a.sum())-1),positive_max(-a),positive_max(-b),positive_max(b-a[:,None]))
        hi=float(np.max(abs(source@G-F).sum(1)/2))
        lo=float(np.sum(F*b)-np.max(source.T@b,axis=1).sum())
        if max(residual,abs(hi-report['upper']),abs(lo-report['lower']),hi-lo,lo-hi)>TOL:
            raise RuntimeError('Original-probability witness check failed')
        c,s,dual_residual=make_cut(g,F,w)
        if abs(c-s@action-lo)>TOL:raise RuntimeError('Cut does not match original-source dual value')
        # A second, different policy checks the complete-history coefficient mapping.
        uniform_action=np.array([2.**(-len(h)-1) for h in g.decisions for _ in range(2)])
        uniform_E=g.raw/(2**(len(g.layers)-1))
        alternate=float(np.sum(F*b)-np.max(uniform_E.T@b,axis=1).sum())
        if abs(c-s@uniform_action-alternate)>TOL:raise RuntimeError('Cut fails uniform-policy replay')
        upper.append(hi);lower.append(lo);cuts.append(dict(target=j,intercept=c,slope=s,alpha=a,b=b))
        saved.append(w);fallbacks+=int(report.get('fallback_used',False));solver_seconds+=report['solve_seconds']
    return dict(upper=np.asarray(upper),lower=np.asarray(lower),cuts=cuts,witnesses=saved,
                seconds=time.perf_counter()-started,solver_seconds=solver_seconds,
                decoder_build_seconds=build_seconds,fallbacks=fallbacks)


def aggregate(values,targets,kind):
    return float(np.max(values)) if kind=='native_minimax' else float(np.array([t['weight'] for t in targets])@values)


def master(g,targets,kind,cuts,time_limit):
    started=time.perf_counter();P=g.flow.shape[1];K=len(targets)
    D=1 if kind=='native_minimax' else K;V=P+D
    cost=np.r_[np.zeros(P),np.ones(1) if kind=='native_minimax' else np.array([t['weight'] for t in targets])]
    Ae=sparse.hstack([g.flow,sparse.csr_matrix((g.flow.shape[0],D))],format='csr')
    rr=[];cc=[];vv=[];bu=[]
    for r,cut in enumerate(cuts):
        for i,v in enumerate(cut['slope']):
            if v:rr.append(r);cc.append(i);vv.append(-float(v))
        rr.append(r);cc.append(P+(0 if D==1 else cut['target']));vv.append(-1.)
        bu.append(-cut['intercept'])
    Au=sparse.coo_matrix((vv,(rr,cc)),shape=(len(cuts),V)).tocsr()
    build_seconds=time.perf_counter()-started
    sol,report=core.solve_arrays(cost,Ae,g.flow_rhs,Au,bu,[(0,1)]*V,'highs',time_limit)
    E,rows,leaf=core.replay(g,sol.x[:P])
    report.update(build_seconds=build_seconds,total_seconds=time.perf_counter()-started)
    arrays=dict(cost=cost,solution=sol.x,b_eq=g.flow_rhs,b_ub=np.asarray(bu),
                eq_dual=sol.eqlin.marginals,ub_dual=sol.ineqlin.marginals,
                lower_dual=sol.lower.marginals,upper_dual=sol.upper.marginals)
    for name,matrix in [('A_eq',Ae),('A_ub',Au)]:
        arrays.update({name+'_data':matrix.data,name+'_indices':matrix.indices,
                       name+'_indptr':matrix.indptr,name+'_shape':matrix.shape})
    return E,rows,leaf,sol.x[P:],report,arrays


def decomposed_plan(g,targets,kind,time_limit=40.,max_iterations=200,gap=GAP):
    if kind not in ('native_weighted','native_minimax'):raise ValueError('Unknown objective')
    if not targets:raise ValueError('An explicit nonempty finite target library is required')
    weights=np.asarray([t['weight'] for t in targets])
    if not np.isfinite(weights).all() or np.any(weights<0):raise ValueError('Target weights must be finite and nonnegative')
    started=time.perf_counter();deadline=started+time_limit
    P=g.flow.shape[1];cuts=[];seen=set();iterations=[];lower=0.;best=None;best_upper=float('inf');last_arrays={}
    status='incomplete_iteration_cap';error=None;total_oracle=0.;total_master=0.;total_cut=0.;decoder_calls=0
    for k in range(max_iterations):
        if time.perf_counter()>=deadline:status='incomplete_time_cap';break
        try:
            E,rows,leaf,d,m,arrays=master(g,targets,kind,cuts,max(.01,min(10.,deadline-time.perf_counter())))
            if not last_arrays or m['dual']>=lower:last_arrays=arrays
            total_master+=m['total_seconds'];lower=max(lower,m['dual'])
            evaluated=oracle(g,E,rows,targets,deadline);decoder_calls+=len(targets);total_oracle+=evaluated['seconds']
            upper=aggregate(evaluated['upper'],targets,kind)
            if upper<best_upper:
                best_upper=upper;best=dict(E=E,rows=rows,leaf=leaf,evaluated=evaluated)
            rec=dict(iteration=k,cut_count=len(cuts),master=m,feasible_upper=upper,best_upper=best_upper,
                     lower=lower,gap=best_upper-lower,oracle_seconds=evaluated['seconds'],
                     oracle_solver_seconds=evaluated['solver_seconds'],decoder_build_seconds=evaluated['decoder_build_seconds'],
                     decoder_fallbacks=evaluated['fallbacks'])
            iterations.append(rec)
            if best_upper-lower < -TOL:raise RuntimeError('Master lower bound exceeds feasible policy upper bound')
            if best_upper-lower<=gap:status='converged';break
            ts=time.perf_counter();added=0
            action=realization(g,rows)
            for cut in evaluated['cuts']:
                deficit=d[0 if kind=='native_minimax' else cut['target']]
                violation=cut['intercept']-cut['slope']@action-deficit
                if violation<=1e-11:continue
                key=(cut['target'],cut['intercept'],cut['slope'].tobytes())
                if key in seen:continue
                seen.add(key);cuts.append(cut);added+=1
            total_cut+=time.perf_counter()-ts;rec['cuts_added']=added
            if added==0:status='incomplete_nonclosing_numerical_gap';break
        except Exception as exc:
            status='incomplete_time_cap' if isinstance(exc,TimeoutError) else 'failed'
            error=repr(exc);break
    report=dict(status=status,error=error,seconds=time.perf_counter()-started,
                lower=lower,upper=None if best is None else best_upper,
                gap=None if best is None else best_upper-lower,
                iterations=iterations,cut_count=len(cuts),master_variables=P+(1 if kind=='native_minimax' else len(targets)),
                total_master_seconds=total_master,total_oracle_seconds=total_oracle,total_cut_insertion_seconds=total_cut,
                decoder_calls=decoder_calls,time_limit=time_limit)
    return best,report,cuts,last_arrays


def save_decomposition(folder,best,report,cuts,arrays,g,targets):
    packed=dict(raw=g.raw,leaf_index=g.leaf_index,
                target_kernels=np.array([t['kernel'] for t in targets]),
                target_weights=[t['weight'] for t in targets],
                cut_targets=[c['target'] for c in cuts],cut_intercepts=[c['intercept'] for c in cuts],
                cut_slopes=np.array([c['slope'] for c in cuts]),
                cut_alpha=np.array([c['alpha'] for c in cuts]),cut_b=np.array([c['b'] for c in cuts]))
    if best is not None:
        packed.update(E=best['E'],rows=best['rows'],leaf=best['leaf'],
                      target_upper=best['evaluated']['upper'],target_lower=best['evaluated']['lower'])
        for j,w in enumerate(best['evaluated']['witnesses']):
            for name,value in w.items():packed[f'witness_{j}_{name}']=value
    np.savez_compressed(folder/'decomposition.npz',**packed)
    if arrays:np.savez_compressed(folder/'master_certificate.npz',**arrays)
    atomic(folder/'decomposition.json',report)


def target_set(model,n,K):
    full=core.Targets(model['T'],model['Z'],n)
    if K==full.count:ids=list(range(full.count))
    else:
        initial=full.fixed_indices()
        remaining=[j for j in range(full.count) if j not in initial]
        rest=np.random.default_rng(SEED).permutation(remaining).tolist()
        ids=(initial+rest)[:K]
    targets=[full.get(j)|{'weight':1/K} for j in ids]
    return targets,ids


def pilot(output,extra=False):
    os.sched_setaffinity(0,{min(os.sched_getaffinity(0))})
    resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
    core.OPTIONS=core.OPTIONS|{'threads':1}
    output.mkdir(parents=True,exist_ok=True)
    cells=[dict(case=case,t=3,n=n,K=K,kind=kind)
           for n,K in [(2,8),(3,16)] for case in CASES for kind in ['native_weighted','native_minimax']]
    cells += [dict(case='hmm_91501_0.2',t=3,n=3,K=128,kind=kind)
              for kind in ['native_weighted','native_minimax']]
    if extra:
        cells=[dict(case='hmm_91501_0.2',t=4,n=3,K=128,kind='native_weighted'),
               dict(case='hmm_91502_1.0',t=4,n=3,K=128,kind='native_weighted',decomposition_only=True,target_seed=923101)]
    bindings={p.name:digest(p) for p in (HERE/'deps').glob('*.py')}
    atomic(output/'design.json',dict(cells=cells,seed=SEED,per_method_limit=40.,total_limit=540.,gap=GAP,
            rss_limit_gib=2,cpu_affinity=sorted(os.sched_getaffinity(0)),
            dependencies=bindings,source_sha256=digest(__file__),python=sys.version,
            numpy=np.__version__,scipy=scipy.__version__,highs=highspy.Highs().version()))
    started=time.perf_counter();results=[]
    for specification in cells:
        key=f"{specification['case']}__t{specification['t']}n{specification['n']}K{specification['K']}__{specification['kind']}"
        folder=output/key;folder.mkdir(exist_ok=True)
        record=dict(specification)
        if time.perf_counter()-started>500:
            record['status']='skipped_total_budget';results.append(record);continue
        model_path=OLD/specification['case']/'model.npz';model=np.load(model_path)
        geometry_start=time.perf_counter();g=core.geometry(model['T'],model['Z'],specification['t'])
        targets,ids=target_set(model,specification['n'],specification['K'])
        record.update(target_indices=ids,geometry_and_targets_seconds=time.perf_counter()-geometry_start,
                      input_sha256=digest(model_path))
        cap=min(40.,530-(time.perf_counter()-started))
        best,decomposition,cuts,arrays=decomposed_plan(g,targets,specification['kind'],cap)
        export_start=time.perf_counter()
        save_decomposition(folder,best,decomposition,cuts,arrays,g,targets)
        decomposition['certificate_export_seconds']=time.perf_counter()-export_start
        record['decomposition']=decomposition
        if specification.get('decomposition_only'):
            record['status']='decomposition_only_'+decomposition['status']
            results.append(record);atomic(folder/'comparison.json',record)
            atomic(output/'results.json',dict(cells=results,seconds=time.perf_counter()-started,peak_rss_mib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024))
            print(key,record['status'],'D',round(decomposition['seconds'],3),'gap',decomposition['gap'],flush=True)
            continue
        try:
            cap=max(.01,min(40.,530-(time.perf_counter()-started)))
            ts=time.perf_counter()
            export_times=[];original_export=np.savez_compressed
            def timed_export(*args,**kwargs):
                export_start=time.perf_counter()
                try:return original_export(*args,**kwargs)
                finally:export_times.append(time.perf_counter()-export_start)
            np.savez_compressed=timed_export
            try:
                E,rows,leaf,monolithic=core.native_plan(g,targets,specification['kind'],time_limit=cap,
                                                      certificate_path=folder/'monolithic_certificate.npz')
            finally:np.savez_compressed=original_export
            evaluated=oracle(g,E,rows,targets,min(started+535.,time.perf_counter()+20.))
            actual_upper=aggregate(evaluated['upper'],targets,specification['kind'])
            actual_lower=aggregate(evaluated['lower'],targets,specification['kind'])
            if actual_upper-monolithic['dual']>TOL or actual_lower>monolithic['primal']+TOL:
                raise RuntimeError('Monolithic replay objective does not match certificate')
            wall_seconds=time.perf_counter()-ts
            monolithic.update(total_wall_including_export_seconds=wall_seconds,
                              certificate_export_seconds=sum(export_times),
                              total_including_replay_audit_seconds=wall_seconds-sum(export_times),
                              selected_target_upper=actual_upper,selected_target_lower=actual_lower,
                              decoder_audit_seconds=evaluated['seconds'],status='passed')
            record['monolithic']=monolithic
            np.savez_compressed(folder/'monolithic_policy.npz',E=E,rows=rows,leaf=leaf,
                                target_upper=evaluated['upper'],target_lower=evaluated['lower'])
            if decomposition['status']=='converged':
                if decomposition['lower']>actual_upper+TOL or monolithic['dual']>decomposition['upper']+TOL:
                    raise RuntimeError('Decomposition and monolithic bounds do not overlap')
                record['status']='compared_passed'
                record['absolute_upper_difference']=abs(decomposition['upper']-actual_upper)
                record['end_to_end_speed_ratio_mono_over_decomposed']=monolithic['total_including_replay_audit_seconds']/decomposition['seconds']
            else:record['status']='decomposition_incomplete_or_failed'
        except Exception as exc:
            record['status']='monolithic_comparison_failed'
            record['monolithic_error']=repr(exc)
            record['monolithic_failed_wall_seconds']=time.perf_counter()-ts
        record['peak_rss_mib']=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024
        results.append(record);atomic(folder/'comparison.json',record)
        atomic(output/'results.json',dict(cells=results,seconds=time.perf_counter()-started,
                                          peak_rss_mib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024))
        print(key,record['status'],'D',round(decomposition['seconds'],3),
              'M',round(record.get('monolithic',{}).get('total_including_replay_audit_seconds',0),3),
              'iterations',len(decomposition['iterations']),'gap',decomposition['gap'],flush=True)
    atomic(output/'results.json',dict(cells=results,seconds=time.perf_counter()-started,
                                      peak_rss_mib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024))
    print('completed',len(results),'cells',round(time.perf_counter()-started,3),'seconds',flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pilot',action='store_true')
    parser.add_argument('--extra-t4',action='store_true')
    parser.add_argument('--output',type=Path,default=HERE/'results_fair_timing')
    args=parser.parse_args()
    if args.pilot or args.extra_t4:pilot(args.output,extra=args.extra_t4)
    else:parser.print_help()
