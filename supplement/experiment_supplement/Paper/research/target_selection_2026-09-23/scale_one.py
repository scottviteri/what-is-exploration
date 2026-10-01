"""One frozen target-selection curve or intrinsic baseline; no sampled training."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import resource
import sys
import time
import traceback
sys.dont_write_bytecode = True
import numpy as np
import scaling_core as c
from objective_dp import plan_terminal_rewards
from extra_objectives import fixed_history_scores, occupancy_plan
from certified_decoder import StableDecoder as NativeDecoder
HERE=Path(__file__).resolve().parent


def write(path,data):
    tmp=path.with_suffix('.tmp')
    tmp.write_text(json.dumps(data,indent=2,allow_nan=False)+'\n');tmp.replace(path)


def atomic_npz(path,**arrays):
    tmp=path.with_suffix('.tmp')
    with tmp.open('wb') as f:np.savez_compressed(f,**arrays)
    tmp.replace(path)


def order_targets(targets,strategy,seed):
    rng=np.random.default_rng(seed)
    if strategy=='random':return rng.permutation(targets.count).tolist()
    fixed=targets.fixed_indices();excluded=set(fixed)
    others=[j for j in range(targets.count) if j not in excluded]
    return fixed+rng.permutation(others).tolist()


def dp_plan(g,scores):
    dp=plan_terminal_rewards(g.layers,g.p,scores,tie_tolerance=0.)
    E,rows,leaf=dp['E'],dp['rows'],dp['weights'][-len(g.layers[-1]):]
    plan={k:v for k,v in dp.items() if k in ['objective','optimal_objective','checks','seconds','numerical_tied_histories']}
    plan.update(method='exact_tree_dp',reward=float(dp['objective']),tie_break='uniform over exactly tied float64 action values')
    if any(not np.isfinite(v) or abs(v)>c.TOL for v in dp['checks'].values()):raise RuntimeError('DP certificate failed')
    return E,rows,leaf,plan


def action_weights(g,rows):
    prefix={():1.};out=np.zeros(g.flow.shape[1])
    for h,row in zip(g.decisions,rows):
        for a in range(2):
            w=prefix[h]*row[a];out[2*g.decision_index[h]+a]=w
            for o in range(2):prefix[h+((a,o),)]=w
    return out


def master(g,library,args,path,constraint=None,feasible_reward_policy=None):
    variables=g.flow.shape[1]+sum(1+g.raw.shape[1]*x['kernel'].shape[1]+g.raw.shape[0]*x['kernel'].shape[1] for x in library)+1
    if variables>args.max_variables:raise RuntimeError(f'Predeclared LP size limit: {variables}>{args.max_variables}')
    method=args.method
    if method=='hybrid':method='cuopt-pdlp' if variables>=100000 else 'highs-ipm'
    out=c.native_plan(g,library,args.objective if constraint is None else 'native_minimax',
                      method,args.solve_limit,certificate_path=path/'master_certificate.npz',
                      reward_constraint=constraint,compact_certificate=True)
    E,rows,leaf,plan=out
    repair_fraction=0.
    if constraint is not None:
        value=float(leaf@constraint[0]);optimal_rows,optimal_reward=feasible_reward_policy
        margin=min((optimal_reward-constraint[1])/4,1e-11*max(1.,abs(optimal_reward)))
        goal=constraint[1]+margin
        if value<goal:
            repair_fraction=min(1.,max(0.,(goal-value)/(optimal_reward-value)))
            repair_fraction=min(1.,float(np.ceil(repair_fraction*1e8)/1e8))
            mixture=(1-repair_fraction)*action_weights(g,rows)+repair_fraction*action_weights(g,optimal_rows)
            E,rows,leaf=c.replay(g,mixture)
        achieved=float(leaf@constraint[0])
        if achieved<constraint[1]:raise RuntimeError('Reward-face repair did not produce a feasible incumbent')
        plan['reward_face_repair']=dict(fraction=repair_fraction,before=value,after=achieved,threshold=float(constraint[1]))
    replay_start=time.perf_counter();cache={};values=[]
    for target in library:
        F=target['kernel'];Y=F.shape[1]
        if Y not in cache:cache[Y]=NativeDecoder(E,Y,'native-simplex',min(120.,args.solve_limit))
        value,_=cache[Y].solve(F);values.append(value['upper'])
    actual=max(values) if args.objective=='native_minimax' or constraint is not None else sum(x['weight']*v for x,v in zip(library,values))
    if abs(actual-plan['primal'])>repair_fraction+c.TOL:raise RuntimeError(f'Master decoder replay mismatch: {actual}, {plan["primal"]}')
    plan.update(independent_library_upper=actual,independent_replay_seconds=time.perf_counter()-replay_start,
                compact_certificate='LP matrices deterministically reconstructed from frozen sources/model/targets; vectors and matrix hashes saved')
    if constraint is not None:
        value=float(leaf@constraint[0]);plan['achieved_constrained_reward']=value
        plan['reward_constraint_threshold']=float(constraint[1])
        if value<constraint[1]:raise RuntimeError('Recovered policy violates reward constraint')
    return E,rows,leaf,plan


def save_audit(E,targets,path,report,args,prefix='audit'):
    def progress(done,seconds):
        report['progress']={'path':str(path.relative_to(args.output)),'target_horizon':targets.n,'targets_done':done,'seconds':seconds}
        write(args.output/'result.json',report)
    start=time.perf_counter()
    audit=c.audit(E,targets,method='native-simplex',time_limit=min(120.,args.solve_limit),
                  progress=progress,checkpoint_path=path/(prefix+'_partial.npz'),witness_path=path/(prefix+'_witness.npz'))
    ids=audit.pop('target_indices');lower=np.asarray(audit.pop('lower_values'));upper=np.asarray(audit.pop('upper_values'))
    atomic_npz(path/(prefix+'_profile.npz'),indices=ids,lower=lower,upper=upper)
    audit.update(total_seconds=time.perf_counter()-start,mean_lower=float(lower.mean()),mean_upper=float(upper.mean()))
    if not audit['exhaustive']:raise RuntimeError('Complete study refuses partial audits as completed results')
    return audit,lower,upper


def run(args,report):
    begin=time.perf_counter()
    model=c.random_model(args.seed,worlds=args.worlds,concentration=args.concentration) if args.case=='fresh' else c.model(args.case)
    atomic_npz(args.output/'model.npz',T=model['T'],Z=model['Z'])
    g=c.geometry(model['T'],model['Z'],args.t);targets=c.Targets(model['T'],model['Z'],args.n)
    report.update(model_name=model['name'],worlds=len(model['T']),source_histories=g.raw.shape[1],
                  target_count=targets.count,geometry_seconds=g.seconds,checkpoints=[])
    baseline=args.strategy=='baseline';constraint=None;face=None;scores=None;feasible_reward_policy=None
    if baseline or args.face_objective!='none':scores=fixed_history_scores(g)
    if args.face_objective!='none':
        score=scores[args.face_objective];_,best_rows,_,best=dp_plan(g,score);_,_,_,negative=dp_plan(g,-score)
        feasible_reward_policy=(best_rows,best['reward'])
        high=best['reward'];low=-negative['reward'];gap=args.regret*(high-low)
        coefficients=g.raw.mean(axis=0)*score
        threshold=high-gap-1e-10
        constraint=(coefficients,threshold)
        face=dict(objective=args.face_objective,optimum=high,minimum=low,normalized_regret=args.regret,
                  permitted_objective_gap=gap,numerical_reward_slack=1e-10,threshold=threshold)
        report['reward_face']=face
    offline=0.;reference_lower=None
    if baseline:budgets=[0];ordered=[]
    else:
        budgets=[k for k in [8,16,32,64,128] if 2**args.n<=k<=min(args.max_targets,targets.count)]
        if not budgets:raise ValueError('No target budget')
        ordered=order_targets(targets,args.strategy,args.target_seed)
    charged=time.perf_counter()-begin
    report['setup_seconds']=charged
    active=[];previous_upper=None;final_policy=None
    for k in budgets:
        path=args.output/f'checkpoint_{k:03d}';path.mkdir(exist_ok=False)
        step_start=time.perf_counter()
        if baseline:
            if args.objective in scores:E,rows,leaf,plan=dp_plan(g,scores[args.objective])
            elif args.objective=='observation_occupancy_entropy':E,rows,leaf,plan=occupancy_plan(g)
            elif args.objective=='uniform':
                rows=np.full((len(g.decisions),2),.5);leaf=np.full(g.raw.shape[1],2.**(-args.t));E=g.raw*leaf;plan=dict(method='literal_uniform')
            elif args.objective in ['native_weighted','native_minimax']:
                library=c.target_library(model['T'],model['Z']);E,rows,leaf,plan=master(g,library,args,path)
            else:raise ValueError(args.objective)
        else:
            if args.strategy=='adaptive' and previous_upper is not None:
                candidates=sorted((j for j in range(targets.count) if j not in set(active)),key=lambda j:(-previous_upper[j],j))
                active+=candidates[:k-len(active)]
            else:active=ordered[:k]
            library=[dict(targets.get(j),weight=1/len(active)) for j in sorted(active)]
            E,rows,leaf,plan=master(g,library,args,path,constraint,feasible_reward_policy)
        construction_seconds=time.perf_counter()-step_start
        charged+=construction_seconds
        atomic_npz(path/'policy.npz',E=E,rows=rows,leaf=leaf)
        row=dict(status='auditing',k=k,selected_targets=sorted(active),planning=plan,
                 optimization_seconds=construction_seconds,training_seconds=charged,reward_face=face)
        if face:
            value=float(leaf@constraint[0]);row['actual_reward_gap']=face['optimum']-value
            row['actual_normalized_regret']=(face['optimum']-value)/(face['optimum']-face['minimum']) if face['optimum']>face['minimum'] else 0.
        write(path/'checkpoint.json',row)
        report['phase']='current_depth_audit';write(args.output/'result.json',report)
        audited,lower,upper=save_audit(E,targets,path,report,args)
        if args.strategy=='adaptive':charged+=audited['total_seconds']
        else:offline+=audited['total_seconds']
        if not baseline and args.objective=='native_minimax':
            reference_lower=plan['dual'] if reference_lower is None else max(reference_lower,plan['dual'])
            gap=audited['upper']-reference_lower
            if gap < -2*c.TOL:raise RuntimeError('Negative full minimax optimization bracket')
            row.update(full_minimax_lower=reference_lower,full_minimax_gap=max(0.,gap),
                       full_minimax_certified=gap<=c.TOL)
        elif not baseline and args.objective=='native_weighted':
            fraction=len(active)/targets.count
            reference_lower=max(0.,fraction*plan['dual'])
            if audited['mean_upper']<reference_lower-2*c.TOL:raise RuntimeError('Negative full weighted-reference bracket')
            row.update(full_uniform_mean_lower=reference_lower,
                       full_uniform_mean_gap=max(0.,audited['mean_upper']-reference_lower),
                       full_uniform_mean_certified=audited['mean_upper']-reference_lower<=c.TOL)
        row.update(status='complete',audit=audited,training_seconds=charged,
                   offline_audit_seconds=offline,end_to_end_seconds=time.perf_counter()-begin)
        write(path/'checkpoint.json',row);report['checkpoints'].append(row)
        report['latest_checkpoint']=str(path.relative_to(args.output));write(args.output/'result.json',report)
        previous_upper=upper;final_policy=(E,path)
        if args.strategy=='adaptive' and row.get('full_minimax_certified'):
            report['early_stop']='full_target_minimax_gap_certified';break
    if args.eval_n and args.eval_n!=args.n:
        report['phase']='held_out_horizon';write(args.output/'result.json',report)
        held=c.Targets(model['T'],model['Z'],args.eval_n)
        value,_,_=save_audit(final_policy[0],held,final_policy[1],report,args,prefix='held_out')
        report['held_out_horizon']=dict(n=args.eval_n,selection_used=False,audit=value,policy_checkpoint=report['latest_checkpoint'])
    report.update(status='complete',phase='complete',training_seconds=charged,
                  offline_current_depth_audit_seconds=offline,
                  scope='Supplied-class finite planning, selected numerical optima, no training on sampled episodes or complete-return J_w.')


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--case',default='sensors_0.1_0.3');p.add_argument('--t',type=int,default=3);p.add_argument('--n',type=int,default=3)
    p.add_argument('--eval-n',type=int,default=0);p.add_argument('--worlds',type=int,default=4)
    p.add_argument('--seed',type=int,default=2026092800);p.add_argument('--concentration',type=float,default=1.)
    p.add_argument('--objective',default='native_minimax')
    p.add_argument('--strategy',choices=['random','structured','adaptive','baseline'],default='adaptive')
    p.add_argument('--target-seed',type=int,default=923101);p.add_argument('--max-targets',type=int,default=128)
    p.add_argument('--face-objective',default='none');p.add_argument('--regret',type=float,default=0.)
    p.add_argument('--method',choices=['highs-ipm','cuopt-pdlp','hybrid'],default='highs-ipm')
    p.add_argument('--max-variables',type=int,default=1200000)
    p.add_argument('--solve-limit',type=float,default=300.);p.add_argument('--output',type=Path,required=True)
    args=p.parse_args();args.output=args.output.resolve();args.output.mkdir(parents=True,exist_ok=True)
    if args.strategy=='adaptive' and args.objective!='native_minimax':raise ValueError('Adaptive additions are a minimax method, not a weighted estimator')
    if args.face_objective!='none' and (args.strategy!='adaptive' or args.objective!='native_minimax'):raise ValueError('Reward-face comparisons require adaptive minimax')
    report=dict(status='running',started_utc=datetime.now(timezone.utc).isoformat(),
                arguments={k:str(v) if isinstance(v,Path) else v for k,v in vars(args).items()},
                manifest_sha256=os.environ.get('SCALING_MANIFEST_SHA256'),job_sha256=os.environ.get('SCALING_JOB_SHA256'),
                source_sha256={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in HERE.glob('*.py')},
                python=sys.version,numpy=np.__version__,pid=os.getpid())
    write(args.output/'result.json',report);start=time.perf_counter()
    try:run(args,report)
    except Exception as exc:
        report.update(status='failed',error=repr(exc),traceback=traceback.format_exc());raise
    finally:
        report.update(seconds=time.perf_counter()-start,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                      finished_utc=datetime.now(timezone.utc).isoformat())
        write(args.output/'result.json',report)
    print(json.dumps({'status':report['status'],'checkpoints':len(report['checkpoints']),'seconds':report['seconds']}),flush=True)

if __name__=='__main__':main()
