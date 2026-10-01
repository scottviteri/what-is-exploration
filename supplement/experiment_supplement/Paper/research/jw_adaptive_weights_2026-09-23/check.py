#!/usr/bin/env python3
"""Tiny stdlib-only regression checks; no solver, training, or model generation."""
import os
for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):
    os.environ[key] = '1'
import resource
import signal
import sys
sys.dont_write_bytecode = True
resource.setrlimit(resource.RLIMIT_AS,(256*1024**2,256*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(9,10))
signal.alarm(10)
import ast
from dataclasses import replace
from fractions import Fraction as F
import json
from pathlib import Path
import time
import unittest

from adaptive_weights import *
from frozen_adapter import prepare_master, verify_lock, load_backend, solve_reweighted
from weight_updates import distribution, tractability_weights, hard_target_update, average_realizations
from dry_run import make_plan
from target_oracle import fixed_dual_target, source_penalty
HERE=Path(__file__).resolve().parent


def fixture():
    raw=((F(1),F(0),F(1,2),F(1,2)),(F(0),F(1),F(1,2),F(1,2)))
    leaf=(0,0,1,1)
    kernel=((F(1),F(0)),(F(0),F(1)))
    context=Context(digest('model'),exact_geometry_hash(raw,leaf,2),digest(['0','1']),1,2)
    target=TargetBinding('read-hidden-bit',exact_kernel_hash(kernel))
    other=TargetBinding('constant',exact_kernel_hash(((1,0),(1,0))))
    cut=exact_dual_cut(context,target,raw,leaf,kernel,(F(1,2),F(1,2)),
                       ((F(1,2),F(0)),(F(0),F(1,2))))
    return context,target,other,cut,raw,leaf,kernel


class Checks(unittest.TestCase):
    def test_rational_policy_table_normalization(self):
        targets=[RationalTarget(2,2,1,2,k) for k in range(3)]
        self.assertEqual([t.table() for t in targets],
                         [((F(0),F(1)),),((F(1,2),F(1,2)),),((F(1),F(0)),)])
        self.assertEqual(sum(t.mass for t in targets),F(1,16))
        self.assertEqual(RationalTarget(2,2,0,7,0).table(),())
        self.assertEqual(sum(RationalTarget(2,2,0,d,0).mass for d in range(1,5)),F(15,32))

    def test_metadata_guard_before_huge_exponentiation(self):
        with self.assertRaises(ValueError): RationalTarget(2,2,20,2,0)
        with self.assertRaises(ValueError): RationalTarget(2,2,2,100000000,0)

    def test_randomized_native_record_retains_actions(self):
        raw=((1,0,0,1),(0,1,1,0))
        target=RationalTarget(2,2,1,2,1)
        kernel=exact_native_kernel(target,raw)
        self.assertEqual(kernel,((F(1,2),F(0),F(0),F(1,2)),
                                 (F(0),F(1,2),F(1,2),F(0))))
        # Forgetting the action would make these distinct laws identical.
        self.assertEqual(tuple(row[0]+row[2] for row in kernel),(F(1,2),F(1,2)))
        self.assertNotEqual(kernel[0],kernel[1])
        with self.assertRaises(ValueError): exact_native_kernel(target,((1,1,1,1),))

    def test_full_history_cut_not_incumbent_support(self):
        context,target,other,cut,raw,leaf,kernel=fixture()
        for p in (F(0),F(1,4),F(1,2),F(1)):
            self.assertEqual(cut.at((p,1-p)),(1-p)/2)
        self.assertEqual(cut.slope,(F(1),F(1,2)))
        self.assertEqual(cut.at((1,0)),0)
        # Dropping the zero incumbent TEST columns would incorrectly give 1 here.
        bad=replace(cut,slope=(F(0),F(1,2)))
        self.assertEqual(bad.at((1,0)),1)

    def test_cut_kernel_and_geometry_binding(self):
        c,t,other,cut,raw,leaf,kernel=fixture()
        with self.assertRaises(ValueError):
            exact_dual_cut(c,other,raw,leaf,kernel,(F(1,2),F(1,2)),
                           ((F(1,2),F(0)),(F(0),F(1,2))))
        with self.assertRaises(ValueError):
            exact_dual_cut(c,t,raw,(1,1,0,0),kernel,(F(1,2),F(1,2)),
                           ((F(1,2),F(0)),(F(0),F(1,2))))

    def test_cut_reuse_reindexes_and_invalidates_changed_kernel(self):
        c,t,o,cut,*_=fixture(); cache=CutCache(c); cache.add(t,cut)
        old=Objective.finite(c,[t,o],[F(1,2)]*2)
        new=Objective.finite(c,[o,t],[F(1,4),F(3,4)])
        self.assertEqual(cache.for_objective(old)[0][0],0)
        self.assertEqual(cache.for_objective(new)[0][0],1)
        changed=replace(t,kernel_sha256=digest('changed'))
        self.assertEqual(cache.for_objective(Objective.finite(c,[changed],[1])),[])
        with self.assertRaises(ValueError): cache.add(changed,cut)
        with self.assertRaises(ValueError):
            cache.for_objective(replace(old,context_id=digest('other-context')))

    def test_cache_round_trip_and_schema(self):
        c,t,o,cut,*_=fixture(); cache=CutCache(c); cache.add(t,cut)
        obj=Objective.finite(c,[t],[1])
        restored=CutCache.restore(json.loads(json.dumps(cache.manifest())))
        self.assertEqual(restored.for_objective(obj),cache.for_objective(obj))
        stale=cache.manifest(); stale['schema']='unknown'
        with self.assertRaises(ValueError): CutCache.restore(stale)
        stale=cache.manifest(); stale['aggregate_bounds']={'lower':'.5'}
        with self.assertRaises(ValueError): CutCache.restore(stale)

    def test_new_weights_require_new_bound(self):
        c,t,o,cut,*_=fixture()
        old=Objective.finite(c,[t,o],[F(1,2)]*2)
        new=Objective.finite(c,[t,o],[F(3,4),F(1,4)])
        policy=PolicyIntervals(c.identity,digest('policy'),((t.identity,F(1,2),F(1,2)),
                              (o.identity,F(0),F(0))),'exact fixture')
        bound=MasterBound(c.identity,old.identity,F(0),'exact fixture')
        with self.assertRaises(ValueError): finite_certificate(new,policy,bound)
        self.assertEqual(policy.aggregate(new),(F(3,8),F(3,8)))
        new_bound=replace(bound,objective_id=new.identity)
        certificate=finite_certificate(new,policy,new_bound)
        self.assertEqual(certificate['full_finite_regret_upper'],'3/8')
        self.assertIsNone(certificate['eventual_regret_upper'])
        self.assertEqual(certificate['eventual_score_lower'],'5/8')

    def test_background_tail_not_renormalized(self):
        c,*_=fixture(); es=[RationalTarget(2,2,1,1,k) for k in (0,1)]
        ts=[TargetBinding(e.key,digest(e.key)) for e in es]
        obj=Objective.rich(c,ts,es,{es[0].key:1},F(1,10))
        self.assertEqual(obj.weights,(F(29,32),F(1,160)))
        self.assertEqual(obj.omitted_mass,F(7,80))
        self.assertEqual(sum(obj.weights),F(73,80))
        # L_selected=.1825; tail=.0875, so total upper=.27 exactly.
        policy=PolicyIntervals(c.identity,digest('policy'),tuple(
            (t.identity,F(1,5),F(1,5)) for t in ts),'exact synthetic')
        cert=finite_certificate(obj,policy,MasterBound(c.identity,obj.identity,F(0),'fixture'))
        self.assertEqual(cert['full_finite_policy_loss_interval'],['73/400','27/100'])
        with self.assertRaises(ValueError): Objective.rich(c,ts,es,{'outside':1},F(1,10))
        with self.assertRaises(ValueError): Objective.rich(c,ts,es,{es[0].key:1},0)

    def test_invalid_weights_and_constraints(self):
        c,t,o,*_=fixture()
        with self.assertRaises(ValueError): Objective.finite(c,[t,o],[F(3,2),F(-1,2)])
        with self.assertRaises(ValueError): Objective.finite(c,[t],[F(1,2)])
        with self.assertRaises(ValueError): replace(c,policy_constraints='brier-near-optimal-face')
        with self.assertRaises(TypeError): rational(float('nan'))

    def test_unnormalized_coefficient_transport(self):
        self.assertEqual(coefficient_change_bounds([F(1,2),F(1,2)],[F(3,4),F(1,4)]),
                         (F(-1,4),F(1,4)))
        self.assertEqual(coefficient_change_bounds([F(1,4)],[F(1,2)]),(F(0),F(1,4)))

    def test_cooperative_and_dual_tie_counterexample(self):
        for x in (F(0),F(1,4),F(1,2),F(1)):
            du,dv=(1-x)/2,x/2
            self.assertEqual((du+dv)/2,F(1,4))
            if x==F(1,2): self.assertEqual(max(du,dv),F(1,4))
            if x in (0,1): self.assertEqual(max(du,dv),F(1,2))

    def test_adaptive_rules_and_realization_average(self):
        self.assertEqual(tractability_weights([1,1],[1,3],1),(F(2,3),F(1,3)))
        weights,record=hard_target_update([1,1],[(0,0),(1,1)],1)
        self.assertEqual(sum(weights),1); self.assertGreater(weights[1],weights[0])
        self.assertEqual(record['score_error_upper'],'0')
        self.assertFalse(record['last_iterate_minimax_guarantee'])
        self.assertEqual(average_realizations([(1,0),(0,1)]),(F(1,2),F(1,2)))

    def test_fixed_dual_dp_and_native_nonconcavity(self):
        raw=((1,0,1,0),(0,1,0,1)); alpha=(F(1,2),F(1,2))
        left=((F(1,2),0,0,0),(0,F(1,2),0,0))
        right=((0,0,F(1,2),0),(0,0,0,F(1,2)))
        middle=tuple(tuple((F(a)+F(b))/2 for a,b in zip(x,y)) for x,y in zip(left,right))
        results=[]
        for dual in (left,right,middle):
            result=fixed_dual_target(raw,alpha,dual,actions=2,observations=2,depth=1)
            results.append(result['linear_value']-source_penalty(((1,),(1,)),dual))
            self.assertIsNone(result['global_hardest_target_upper'])
            self.assertTrue(all(sum(row)==1 for row in result['target_kernel']))
        self.assertEqual(results,[F(1,2),F(1,2),F(1,4)])
        self.assertLess(results[2],(results[0]+results[1])/2)

    def test_dry_master_has_no_stale_bounds(self):
        c,t,o,cut,*_=fixture();cache=CutCache(c);cache.add(t,cut)
        plan=prepare_master(cache,Objective.finite(c,[t],[1]))
        self.assertEqual(plan['reused_cut_count'],1)
        self.assertIsNone(plan['inherited_aggregate_lower'])
        self.assertFalse(plan['execution_enabled'])
        with self.assertRaises(RuntimeError): load_backend()
        with self.assertRaises(RuntimeError): solve_reweighted(None,None,None,None,None,
                                                   model_sha256=digest('model'),world_labels=[])

    def test_lock_dry_run_and_no_solver_imports(self):
        verify_lock(); plan=make_plan()
        self.assertEqual(len(plan['future_model_specifications']),12)
        self.assertFalse(plan['execution_enabled'])
        self.assertEqual(len({v['objective']['objective_id'] for v in
                              plan['illustrative_objectives'].values()}),3)
        for name in ('numpy','scipy','highspy','torch','cupy'):
            self.assertNotIn(name,sys.modules)
        for path in HERE.glob('*.py'):
            ast.parse(path.read_text(),filename=str(path))


def main():
    wall=time.perf_counter(); cpu=time.process_time()
    suite=unittest.defaultTestLoader.loadTestsFromTestCase(Checks)
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    process_status = {line.split(':',1)[0]: line.split(':',1)[1].strip()
                      for line in Path('/proc/self/status').read_text().splitlines() if ':' in line}
    report={'status':'passed' if result.wasSuccessful() else 'failed',
        'tests':result.testsRun,'failures':len(result.failures),'errors':len(result.errors),
        'wall_seconds':time.perf_counter()-wall,'cpu_seconds':time.process_time()-cpu,
        'peak_rss_kib':int(process_status['VmHWM'].split()[0]),
        'lifetime_ru_maxrss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        'memory_measurement':'peak_rss_kib is current exec image /proc/self/status VmHWM; lifetime rusage may include launcher history',
        'resource_caps':{'wall_seconds':10,'cpu_soft_seconds':9,'address_space_mib':256,'threads':1},
        'solver_calls':0,'numeric_backends_imported':False,'training_runs':0,
        'scope':'exact fixtures, schema/cut/objective invariants, syntax, dependency hashes, dry-run',
        'not_checked':['new bridge numerical equivalence','performance','full campaign','Lean','PDFs'],
        'source_hashes':{p.name:__import__('hashlib').sha256(p.read_bytes()).hexdigest()
                         for p in sorted(HERE.glob('*.py'))}}
    (HERE/'CHECKS.json').write_text(json.dumps(report,indent=2)+'\n')
    if not result.wasSuccessful(): sys.exit(1)


if __name__=='__main__': main()
