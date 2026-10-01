"""Analytic/synthetic tests only. No study outcomes and no solver imports."""
import os
for key in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS', 'NUMEXPR_NUM_THREADS'):
    os.environ[key]='1'
import sys
sys.dont_write_bytecode=True
import unittest
from unittest.mock import patch
from pathlib import Path
import tempfile
import itertools
import math
import check
import numpy as np
from check import physical_replay, replay_witness, check_request, check_pair
from worker import replay as worker_replay
from common import METHODS, BASELINES, design, pair_classification, now, write, HERE, sha

class AnalyticTests(unittest.TestCase):
    def test_identity_and_erasure(self):
        I=np.eye(2);alpha=np.full(2,.5);b=.5*I
        self.assertEqual(replay_witness(I,I,I,alpha,b,0.,0.)['upper'],0.)
        E=np.array([[.4,0.,.6],[0.,.4,.6]]);G=np.array([[1.,0.],[0.,1.],[.5,.5]])
        self.assertAlmostEqual(replay_witness(E,I,G,alpha,b,.3,.3)['lower'],.3)
        self.assertAlmostEqual(replay_witness(np.repeat(E/2,2,axis=1),I,np.repeat(G,2,axis=0),alpha,b,.3,.3)['upper'],.3)

    def test_uninformative_four_worlds(self):
        r=replay_witness(np.ones((4,1)),np.eye(4),np.full((1,4),.25),np.full(4,.25),np.eye(4)/4,.75,.75)
        self.assertEqual(r['lower'],.75)

    def test_incomparable_bits(self):
        E=np.array([[1.,0.],[1.,0.],[0.,1.],[0.,1.]])
        F=np.array([[1.,0.],[0.,1.],[1.,0.],[0.,1.]])
        alpha=np.full(4,.25);G=np.full((2,2),.5)
        f=replay_witness(E,F,G,alpha,F/4,.5,.5);r=replay_witness(F,E,G,alpha,E/4,.5,.5)
        self.assertEqual(pair_classification(dict(status='validated',**f),dict(status='validated',**r)),'numerical_incomparability')

    def test_reject_corrupt_witnesses(self):
        I=np.eye(2);alpha=np.full(2,.5);b=I/2
        for G,a,d,lo,hi in [(I*.9,alpha,b,0.,0.),(I,alpha*2,b,0.,0.),(I,alpha,b+1,0.,0.),
                           (I,alpha,b,float('nan'),0.),(I,alpha,b,.1,0.),(I,alpha,b,0.,.1),(I*np.nan,alpha,b,0.,0.)]:
            with self.assertRaises(ValueError):replay_witness(I,I,G,a,d,lo,hi)

    def test_physical_replay_and_corruption(self):
        T=np.ones((2,2,1,1));Z=np.zeros((2,2,1,2));Z[0,:,:,0]=1.;Z[1,:,:,1]=1.
        rows=np.full((21,2),.5);E=np.zeros((2,64))
        for column in range(64):
            obs=[(column//4**depth)%2 for depth in (2,1,0)]
            for q in (0,1):
                if obs==[q,q,q]:E[q,column]=1/8
        model={'T':T,'Z':Z};policy={'rows':rows,'E':E,'leaf':np.full(64,1/8)}
        self.assertEqual(physical_replay(model,policy)[1],0.)
        self.assertTrue(np.array_equal(worker_replay(model,policy),E))
        bad=E.copy();bad[0,0]+=1e-6;bad[0,2]-=1e-6
        for fn in (physical_replay,worker_replay):
            with self.assertRaises(ValueError):fn(model,dict(policy,E=bad))

    def test_adaptive_action_dependent_replay(self):
        rng=np.random.default_rng(7)
        T=rng.dirichlet([1.,1.],size=(2,2,2));Z=rng.dirichlet([1.,1.],size=(2,2,2))
        alphabet=list(itertools.product(range(2),repeat=2))
        levels=[list(itertools.product(alphabet,repeat=d)) for d in range(4)]
        def choice(h):
            p=.3 if not h else .15+.1*len(h)+.25*h[-1][1]
            return [p,1-p]
        rows=np.array([choice(h) for layer in levels[:-1] for h in layer]);E=np.zeros((2,64));leaf=[]
        for col,h in enumerate(levels[-1]):
            w=math.prod(choice(h[:i])[a] for i,(a,o) in enumerate(h));leaf.append(w)
            for q in range(2):
                state=np.array([1.,0.])
                for a,o in h:state=(state@T[q,a])*Z[q,a,:,o]
                E[q,col]=state.sum()*w
        model=dict(T=T,Z=Z);policy=dict(E=E,rows=rows,leaf=np.array(leaf))
        self.assertLess(physical_replay(model,policy)[1],1e-12)
        self.assertTrue(np.allclose(worker_replay(model,policy),E,rtol=0,atol=1e-12))
        altered=rows.copy();altered[[1,2]]=altered[[2,1]]
        for fn in (physical_replay,worker_replay):
            with self.assertRaises(ValueError):fn(model,dict(policy,rows=altered))

    def test_directional_binding_and_scalar_join(self):
        with tempfile.TemporaryDirectory(dir=HERE) as tmp:
            root=Path(tmp);model=root/'model.npz';a=root/'native.npz';b=root/'baseline.npz';state=root/'ANALYSIS_EXECUTION.json'
            for path in (model,a,b,state):path.write_text(path.name)
            frozen={str(p):sha(p) for p in (model,a,b)}
            job=design(['synthetic'])[0]
            native=dict(model='synthetic',method='fixed',budget_seconds=40,policy_path=str(a),planning_check_status='passed',available_seconds=1.,comparison_eligible=True,audit_lower=.1,audit_upper=.11)
            baseline=dict(native,method='information',policy_path=str(b),audit_lower=.3,audit_upper=.31)
            ctx=dict(jobs={'000':job},models={'synthetic':dict(path=str(model),sha256=sha(model))},index={('synthetic','fixed',40):native,('synthetic','information',40):baseline},primary={'metadata':{'input_sha256':frozen}},bindings={})
            request=dict(job,model_path=str(model),source_policy=str(a),target_policy=str(b),primary_execution=str(state),input_sha256={**frozen,str(state):sha(state)})
            with patch.object(check,'STUDY',root):
                check_request(request,'000',ctx)
                with self.assertRaises(ValueError):check_request(dict(request,source_policy=str(b),target_policy=str(a)),'000',ctx)
                missing=dict(request['input_sha256']);missing.pop(str(a))
                with self.assertRaises(ValueError):check_request(dict(request,input_sha256=missing),'000',ctx)
            f=dict(job,status='validated',lower=.1,upper=.1);r=dict(f,job_id='001',direction='baseline_to_native',lower=.2,upper=.2)
            pair=dict(model='synthetic',method='fixed',baseline='information',budget_seconds=40,forward_job='000',reverse_job='001',classification='numerical_incomparability',forward_lower=.1,forward_upper=.1,reverse_lower=.2,reverse_upper=.2,native_audit_classification='native_win',native_audit_difference_lower=.1-.31,native_audit_difference_upper=.11-.3)
            check_pair(pair,f,r,ctx)
            with self.assertRaises(ValueError):check_pair(dict(pair,forward_upper=.5),f,r,ctx)
            with self.assertRaises(ValueError):check_pair(dict(pair,native_audit_classification='native_loss'),f,r,ctx)

    def test_fixed_grid_and_non_dominance_labels(self):
        jobs=design([f'm{i}' for i in range(12)])
        self.assertEqual(len(jobs),288);self.assertEqual(len({j['job_id'] for j in jobs}),288)
        self.assertEqual({j['method'] for j in jobs},set(METHODS));self.assertEqual({j['baseline'] for j in jobs},set(BASELINES))
        good=lambda lo,hi:dict(status='validated',lower=lo,upper=hi)
        self.assertEqual(pair_classification(good(0,1e-8),good(.1,.1)),'native_approximate_simulation_reverse_separated')
        self.assertEqual(pair_classification(good(.1,.1),good(0,1e-8)),'baseline_approximate_simulation_reverse_separated')
        self.assertEqual(pair_classification(good(0,1e-8),good(0,1e-8)),'mutual_approximate_simulation')
        self.assertEqual(pair_classification(good(0,.1),good(0,.2)),'unresolved')
        self.assertEqual(pair_classification(dict(status='lp_timeout'),good(0,0)),'unavailable')

if __name__=='__main__':
    tested=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(AnalyticTests))
    prohibited=sorted(name for name in sys.modules if name in ('highspy','certified_decoder','fast_decoder','scaling_core','scipy.optimize'))
    assert not prohibited,prohibited
    write(HERE/'SYNTHETIC_TESTS.json',dict(created_utc=now(),status='passed' if tested.wasSuccessful() else 'failed',tests=tested.testsRun,failures=len(tested.failures),errors=len(tested.errors),prohibited_solver_modules=prohibited,scope='Analytic and synthetic inputs only; no confirmation outcomes or solver execution'))
    raise SystemExit(0 if tested.wasSuccessful() else 1)
