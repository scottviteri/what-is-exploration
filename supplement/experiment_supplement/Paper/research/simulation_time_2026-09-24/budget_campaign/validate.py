"""Bounded integration and negative tests before the scientific queue starts."""
from io_utils import *
import time
sys.path.insert(0,str(HERE/'deps'))
import scaling_core as core
import objective_dp as dp
import decomposition as decomp
from recovery_decoder import RecoveryDecoder
from worker import scores

def run():
    verify_sources();start=time.monotonic();tests=[]
    E=np.array([[1.,0.],[1.,0.]]);F=np.eye(2)
    r,w=RecoveryDecoder(E,2,time_limit=20).solve(F);l,u=check_witness(E,F,w);assert abs(l-.5)<1e-10 and abs(u-.5)<1e-10;tests.append('uninformative_to_perfect_half')
    r,w=RecoveryDecoder(F,2,time_limit=20).solve(E);l,u=check_witness(F,E,w);assert u<1e-10;tests.append('perfect_to_uninformative_zero')
    corrupt={k:v.copy() for k,v in w.items()};corrupt['decoder'][0,0]=2.
    try:check_witness(F,E,corrupt)
    except AssertionError:tests.append('corrupt_decoder_rejected')
    else:raise AssertionError('Corrupt decoder accepted')
    r,w=RecoveryDecoder(np.array([[.25,.75]]),2,time_limit=20).solve(np.array([[.6,.4]]));assert r['upper']<1e-10;tests.append('singleton_vacuity')
    refs=json.loads((HERE/'REFERENCES.json').read_text());model=np.load(HERE/refs['records'][0]['model']);T,Z=model['T'],model['Z'];g=core.geometry(T,Z,3)
    for method in ['information','brier','pseudo_count']:
        sc=scores(g,method);ans=dp.plan_terminal_rewards(g.layers,g.p,sc);e,rows,leaf,lp=core.reward_plan(g,g.raw.mean(0)*sc)
        assert abs(ans['objective']+lp['primal'])<TOL;replay(T,Z,3,ans['rows'],ans['E'],ans['weights'][-64:]);tests.append(method+'_dp_lp_agreement')
    pool=core.Targets(T,Z,2);targets=[pool.get(j) for j in range(8)]
    for kind in ['native_weighted','native_minimax']:
        best,rep,cuts,arr=decomp.decomposed_plan(g,targets,kind,time_limit=30,gap=TOL);assert rep['status']=='converged',rep
        E,rows,leaf,lp=core.native_plan(g,targets,kind,method='highs-ipm',time_limit=30)
        assert rep['lower']<=lp['primal']+TOL and lp['dual']<=rep['upper']+TOL
        replay(T,Z,3,best['rows'],best['E'],best['leaf']);tests.append(kind+'_decomposition_monolithic_agreement')
        raw=raw_law(T,Z,levels(3)[-1]);assert np.max(abs(raw-g.raw))<1e-12
        for cut in cuts:
            expected=np.bincount(g.leaf_index,weights=np.max(raw.T@cut['b'],axis=1),minlength=g.flow.shape[1]);assert np.max(abs(expected-cut['slope']))<1e-12
        tests.append(kind+'_all_history_cut_replay')
    result=dict(status='passed',tests=tests,seconds=time.monotonic()-start,checked_utc=now(),sources_sha256=sha(HERE/'SOURCES.json'),scope='Bounded numerical integration/negative checks; not campaign outcomes.')
    write(HERE/'VALIDATION.json',result);print(json.dumps(result),flush=True)
if __name__=='__main__':run()
