"""One supplied-class collector, independently optimized for its stated budget."""
from io_utils import *
import argparse,resource,time,traceback,shutil
sys.path.insert(0,str(HERE/'deps'))
import scaling_core as core
import objective_dp as dp
import decomposition as decomp
from recovery_decoder import RecoveryDecoder


def scores(g,method):
    if method in ('information','brier'):return dp.terminal_scores(g.layers,g.p)[method]
    assert method=='pseudo_count'
    out=[]
    for h in g.layers[-1]:
        counts=[0,0];value=0.
        for a,o in h:value+=1/np.sqrt(1+counts[o]);counts[o]+=1
        out.append(value)
    return np.array(out)


def audits(E,refs,out,report):
    records=[];cache={}
    for ref in refs:
        targetpath=HERE/ref['path'];assert sha(targetpath)==ref['sha256']
        with np.load(targetpath) as z:F=z['E'].copy()
        Y=F.shape[1]
        if Y not in cache:cache[Y]=RecoveryDecoder(E,Y,'native-ipm',60.)
        ts=time.monotonic();r,w=cache[Y].solve(F);lo,hi=check_witness(E,F,w)
        assert abs(lo-r['lower'])<1e-10 and abs(hi-r['upper'])<1e-10
        path=out/('reference_'+ref['method']+'.npz');save(path,E=E,F=F,**w,lower=lo,upper=hi)
        records.append(dict(reference=ref['method'],reference_cell=ref['cell'],lower=lo,upper=hi,bracket=hi-lo,classification={str(e):classify(lo,hi,e) for e in [.05,.02,.01]},witness=path.name,witness_sha256=sha(path),seconds=time.monotonic()-ts,coarsening_bound=r.get('coarsening_bound',0.)))
        report['audits']=records;report['phase']='reference_audit';write(out/'result.json',report)
    return records


def run(spec,out):
    source_hash=verify_sources();out.mkdir(parents=True,exist_ok=False)
    allrefs=json.loads((HERE/'REFERENCES.json').read_text());manifest=json.loads((HERE/'MANIFEST.json').read_text())
    assert sha(HERE/'REFERENCES.json')==manifest['references_sha256']
    refs=[r for r in allrefs['records'] if r['case_id']==spec['case_id']];assert len(refs)==6
    modelpath=HERE/refs[0]['model'];assert sha(modelpath)==refs[0]['model_sha256']
    model=np.load(modelpath);T,Z=model['T'],model['Z'];start=time.monotonic()
    report=dict(status='running',phase='planning',spec=spec,started_utc=now(),sources_sha256=source_hash,manifest_sha256=sha(HERE/'MANIFEST.json'),model_sha256=sha(modelpath),pid=os.getpid(),cpu_affinity=sorted(os.sched_getaffinity(0)),audits=[])
    write(out/'result.json',report)
    try:
        t=spec['t'];method=spec['method'];g=core.geometry(T,Z,t)
        certified=True
        if spec['mode']=='replay':
            ref=next(r for r in refs if r['method']==method)
            with np.load(HERE/ref['path']) as z:E=z['E'].copy();rows=z['rows'].copy();leaf=z['leaf'].copy()
            report['planning']=dict(method='frozen_original_reference',cell=ref['cell'],seconds=0,scope='Original selected numerical optimum/control, re-audited as evidence; no new optimizer certificate claimed.')
        elif method in ('information','brier','pseudo_count'):
            ans=dp.plan_terminal_rewards(g.layers,g.p,scores(g,method),tie_tolerance=0.,tie_break='uniform')
            E,rows,leaf=ans['E'],ans['rows'],ans['weights'][-len(g.layers[-1]):]
            save(out/'dp_certificate.npz',**{k:ans[k] for k in ['values','action_values','coefficients','tie_mask','weights','rows']})
            report['planning']={k:ans[k] for k in ['objective','optimal_objective','seconds','checks','numerical_tied_histories','tie_tolerance','tie_break']}
            report['planning']['method']='full_history_dynamic_programming'
        elif method=='uniform':
            rows=np.full((len(g.decisions),2),.5);leaf=np.full(g.raw.shape[1],2.**(-t));E=g.raw*leaf
            report['planning']=dict(method='literal_uniform',seconds=0,scope='Control, not an optimized objective.')
        else:
            kind={'weighted128':'native_weighted','minimax':'native_minimax'}[method]
            targets=core.Targets(T,Z,3);library=[targets.get(j) for j in range(128)]
            best,r,cuts,arrays=decomp.decomposed_plan(g,library,kind,time_limit=spec['planning_seconds'],max_iterations=400,gap=TOL)
            decomp.save_decomposition(out,best,r,cuts,arrays,g,library)
            report['planning']=r|{'method':'full_library_dual_cut_LP','kind':kind,'targets':128,'target_horizon':3}
            if best is None:raise RuntimeError('No accepted feasible native incumbent: '+str(r.get('error')))
            E,rows,leaf=best['E'],best['rows'],best['leaf'];certified=r['status']=='converged'
        replay(T,Z,t,rows,E,leaf)
        save(out/'policy.npz',E=E,rows=rows,leaf=leaf)
        report['policy_sha256']=sha(out/'policy.npz');report['rewards']=rewards(E,g.layers[-1]);report['planning_certified']=certified
        report['planning_elapsed_seconds']=time.monotonic()-start;write(out/'result.json',report)
        audits(E,refs,out,report)
        report['status']='complete' if certified else 'incomplete_optimization'
        report['phase']='awaiting_independent_check'
    except Exception as exc:
        report.update(status='failed',phase='failed',error=repr(exc),traceback=traceback.format_exc())
    report.update(seconds=time.monotonic()-start,peak_rss_mib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024,finished_utc=now())
    assert source_hash==verify_sources();write(out/'result.json',report)
    print(spec['id'],report['status'],round(report['seconds'],3),flush=True)
    return report

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--job',required=True);p.add_argument('--output',type=Path);a=p.parse_args()
    m=json.loads((HERE/'MANIFEST.json').read_text());os.sched_setaffinity(0,{m['cpu']});resource.setrlimit(resource.RLIMIT_AS,(m['address_space_gib']*1024**3,)*2)
    spec=next(j for j in m['jobs'] if j['id']==a.job);r=run(spec,a.output or HERE/'results'/a.job)
    if r['status']=='failed':raise SystemExit(1)
