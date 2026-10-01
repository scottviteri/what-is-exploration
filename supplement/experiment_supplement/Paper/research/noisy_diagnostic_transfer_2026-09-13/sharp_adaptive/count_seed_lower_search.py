#!/usr/bin/env python3
"""Bounded lower-witness search seeded by actual-native common-count cuts.

Every optimized policy obeys the native-optimal LP constraints numerically.
Alternating a fixed deficiency dual with policy best response supplies lower
witnesses only. No global maximum or upper certificate is inferred.
"""
from pathlib import Path
import argparse,importlib.util,json,sys,time,traceback
import numpy as np
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('linear_native_count_lower',HERE/'linear_native_oracle.py')
LN=importlib.util.module_from_spec(spec);sys.modules[spec.name]=LN;spec.loader.exec_module(LN)

def positive_source(oracle,z):
    return oracle.rays*np.maximum(np.asarray(z),0)

def main(args):
    start=time.monotonic();oracle=LN.TerminalPolicyOracle();T=oracle.target_kernels['adaptive_L']
    input_path=HERE/'native_count_progress.json';input_hash=LN.CO.SEARCH.digest(input_path)
    data=json.loads(input_path.read_text());pool=[];seen=set();initial_failures=[]
    for index,row in enumerate(data['witnesses']):
        z=np.asarray(row['state_weights']);key=tuple(np.round(z,10))
        if key in seen:continue
        seen.add(key)
        try:
            value,witness=LN.CO.BASE.fixed_deficiency(positive_source(oracle,z),T)
            alpha,b=LN.CO.SEARCH.clean_dual(witness['dual_alpha'],witness['dual_b'])
            pool.append({'input_index':index,'iteration':row['iteration'],'world':row['theta'],
                         'mask':row['mask'],'state_weights':z.tolist(),'initial_deficiency':value,
                         'alpha':alpha.tolist(),'b':b.tolist()})
        except Exception:
            initial_failures.append({'input_index':index,'traceback':traceback.format_exc()})
    candidates=np.asarray([r['state_weights'] for r in pool])
    selected=[]
    if pool:
        next_index=max(range(len(pool)),key=lambda i:pool[i]['initial_deficiency'])
        distances=np.full(len(pool),np.inf)
        for _ in range(min(args.max_sources,len(pool))):
            selected.append(next_index)
            distances=np.minimum(distances,np.linalg.norm(candidates-candidates[next_index],axis=1))
            distances[selected]=-np.inf
            next_index=int(np.argmax(distances))
    selection={'input_path':input_path.name,'input_sha256':input_hash,
               'raw_witnesses':len(data['witnesses']),'distinct_sources':len(seen),
               'successfully_evaluated_sources':len(pool),
               'selection':'Start with largest initial adaptive deficiency, then farthest Euclidean state-weight diversity; rounded1e-10 dedup.',
               'max_sources':args.max_sources,'selected_pool_indices':selected,
               'initial_failures':initial_failures,'pool':pool}
    LN.CO.SEARCH.write_json(HERE/'count_seed_selection.json',selection)
    best=.072;best_candidate=None;best_result=None;best_dual=None;traces=[];failures=[]
    for position,index in enumerate(selected):
        seed=pool[index];b=np.asarray(seed['b']);previous=seed['initial_deficiency'];trace=[]
        try:
            for iteration in range(args.iterations):
                coefficients=np.max(oracle.rays.T@b,axis=1)
                result=oracle.optimize(-coefficients)
                E=positive_source(oracle,result['state_weights'])
                value,witness=LN.CO.BASE.fixed_deficiency(E,T)
                alpha,new_b=LN.CO.SEARCH.clean_dual(witness['dual_alpha'],witness['dual_b'])
                old_dual_lower=float(np.sum(T*b)-coefficients@result['state_weights'])
                assert value>=previous-1e-7,(value,previous)
                trace.append({'iteration':iteration,'adaptive_deficiency':value,
                              'previous_deficiency':previous,'old_dual_lower':old_dual_lower,
                              'native_epigraph_cost':result['native_epigraph_cost'],
                              'solver_seconds':result['solver_seconds'],'residuals':result['residuals']})
                if value>best+1e-8:
                    best=value;best_candidate={'selected_position':position,'pool_index':index,'iteration':iteration}
                    best_result=result;best_dual=(alpha,new_b,witness)
                improvement=value-previous;previous=value;b=new_b
                if improvement<=1e-9:break
            traces.append({'selected_position':position,'pool_index':index,'trace':trace})
        except Exception:
            failures.append({'selected_position':position,'pool_index':index,'trace':trace,
                             'traceback':traceback.format_exc()})
        if (position+1)%25==0:
            print(json.dumps({'starts_done':position+1,'best_lower_candidate':best,
                              'oracle_calls':oracle.calls,'seconds':time.monotonic()-start}),flush=True)
    best_path=None
    if best_result is not None:
        # Re-solve the winning valid dual purpose with guarded behavioral replay.
        alpha,b,_=best_dual;coefficients=np.max(oracle.rays.T@b,axis=1)
        result=oracle.optimize(-coefficients,HERE/'count_seed_best_lp.npz',replay=True)
        E=result['full_source_kernel'];deficiencies={}
        for target in LN.CO.BASE.target_library((.1,.1)):
            if target['name'] in ('L','R','tagged','LR','LLL','RRR','adaptive_L'):
                deficiencies[target['name']]=LN.CO.BASE.fixed_deficiency(E,target['kernel'])[0]
        native=.2*(deficiencies['L']+deficiencies['R'])+.1*sum(deficiencies[n] for n in ('tagged','LR','LLL','RRR'))
        assert native<=.0072+1e-7
        best_candidate.update(recomputed_native_cost=native,recomputed_target_deficiencies=deficiencies)
        best_path='count_seed_best_policy.npz'
        np.savez_compressed(HERE/best_path,source_kernel=E,compressed_source_kernel=result['compressed_source_kernel'],
                            action_rows=result['action_rows'],realization_weights=result['realization_weights'],
                            state_weights=result['state_weights'],dual_alpha=alpha,dual_b=b)
    report={'status':'completed_bounded_lower_search','scope':
            'Numerical policy lower witnesses only. A failure to exceed .072 does not prove global optimality.',
            'source_sha256':LN.CO.SEARCH.digest(__file__),
            'linear_oracle_sha256':LN.CO.SEARCH.digest(HERE/'linear_native_oracle.py'),
            'selection_path':'count_seed_selection.json','selection_sha256':LN.CO.SEARCH.digest(HERE/'count_seed_selection.json'),
            'baseline_exact_RRRL_lower':.072,'best_lower_candidate':best,'best_candidate':best_candidate,
            'best_policy_path':best_path,'starts':len(selected),'max_iterations':args.iterations,
            'oracle_calls':oracle.calls,'initial_max_deficiency':max(r['initial_deficiency'] for r in pool),
            'initial_failures':initial_failures,'failures':failures,'traces':traces,
            'run_seconds':time.monotonic()-start}
    LN.CO.SEARCH.write_json(HERE/'count_seed_lower_results.json',report)
    print(json.dumps({k:report[k] for k in ('best_lower_candidate','initial_max_deficiency','starts','oracle_calls','run_seconds','best_candidate')},indent=2))

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--max-sources',type=int,default=300)
    parser.add_argument('--iterations',type=int,default=8);main(parser.parse_args())
