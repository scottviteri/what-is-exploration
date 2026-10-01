"""Persistent native HiGHS decoder with repaired two-sided numerical witnesses.

Run this file with --benchmark for the frozen full-depth-three sweep. This is a
fixed-source audit backend, not joint policy optimization or an eventual score.
"""
from __future__ import annotations
import os
for _key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'):
    os.environ.setdefault(_key,'1')
import argparse
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import sys
sys.dont_write_bytecode=True
import time
from types import SimpleNamespace
import numpy as np
import highspy
from scipy import sparse
import scaling_core as core

HERE=Path(__file__).resolve().parent
OUT=HERE/'native_sweep_results'
TOL=2e-7
CASES=['sensors_0.1_0.3','irreversible_0.1_0.1','hmm_91502_1.0']


class NativeDecoder(core.Decoder):
    """Same interface as Decoder, with persistent matrix and objective updates.

    `method` accepts highs/highs-ds/simplex/native-simplex (simplex), or
    highs-ipm/ipm/native-ipm. Solver work is one-threaded. Fallback attempts share
    the per-call time budget, and failures remain visible in the returned report.
    """
    def __init__(self,E,outputs,method='highs',time_limit=120):
        started=time.perf_counter()
        E=np.asarray(E,dtype=float)
        if E.ndim!=2 or min(E.shape)<1 or not np.all(np.isfinite(E)) or np.any(E<0):
            raise ValueError('Source must be a nonnegative finite experiment matrix')
        if np.max(abs(E.sum(1)-1))>TOL or int(outputs)!=outputs or outputs<1:
            raise ValueError('Invalid source normalization or target cardinality')
        if not np.isfinite(time_limit) or not 0<time_limit<=120:
            raise ValueError('Per-call solver time limit must be in (0,120] seconds')
        aliases={'highs':'simplex','highs-ds':'simplex','simplex':'simplex','native-simplex':'simplex',
                 'highs-ipm':'ipm','ipm':'ipm','native-ipm':'ipm'}
        if method not in aliases:raise ValueError(f'Unsupported native method {method}')
        self.solver=aliases[method]
        super().__init__(E,int(outputs),method,time_limit)
        self.matrix_build_seconds=self.build_seconds
        self.A=sparse.vstack([self.Ae,self.Au],format='csr')
        self.row_lower=np.r_[self.be,np.full(len(self.bu),-np.inf)]
        self.row_upper=np.r_[self.be,self.bu]
        self.lo=np.array([0.]*(self.Q+self.Q*self.Y)+[-np.inf]*self.X)
        self.hi=np.full(len(self.c),np.inf)
        self.cost_indices=np.arange(self.Q,self.Q+self.Q*self.Y,dtype=np.int32)
        self.import_reports=[]
        self.h=self._new_solver(self.solver,self.c)
        self.build_seconds=time.perf_counter()-started
        self.calls=0

    def _new_solver(self,solver,cost):
        h=highspy.Highs()
        options=dict(output_flag=False,threads=1,solver=solver,time_limit=float(self.time_limit),
                     primal_feasibility_tolerance=1e-9,dual_feasibility_tolerance=1e-9,
                     ipm_optimality_tolerance=1e-10,small_matrix_value=1e-12)
        for key,value in options.items():
            if h.setOptionValue(key,value)!=highspy.HighsStatus.kOk:
                raise RuntimeError(f'HiGHS rejected {key}={value}')
        lp=highspy.HighsLp();lp.num_col_=len(cost);lp.num_row_=self.A.shape[0]
        lp.col_cost_=cost;lp.col_lower_=self.lo;lp.col_upper_=self.hi
        lp.row_lower_=self.row_lower;lp.row_upper_=self.row_upper
        lp.a_matrix_.format_=highspy.MatrixFormat.kRowwise
        lp.a_matrix_.start_=self.A.indptr;lp.a_matrix_.index_=self.A.indices;lp.a_matrix_.value_=self.A.data
        imported=h.passModel(lp)
        self.import_reports.append(dict(status=str(imported),input_nonzeros=int(self.A.nnz),
                                        stored_nonzeros=int(h.getNumNz()),small_matrix_value=1e-12))
        if imported not in [highspy.HighsStatus.kOk,highspy.HighsStatus.kWarning]:
            raise RuntimeError('HiGHS rejected decoder model: '+str(imported))
        return h

    def _extract(self,h,cost,F):
        hs=h.getSolution();info=h.getInfo()
        x=np.asarray(hs.col_value);y=np.asarray(hs.row_dual);z=np.asarray(hs.col_dual)
        if not all(np.all(np.isfinite(v)) for v in (x,y,z)):
            raise RuntimeError('Nonfinite primal or dual solver output')
        free_residual=float(np.max(abs(z[self.Q+self.Q*self.Y:]),initial=0))
        lower=np.r_[z[:self.Q+self.Q*self.Y],np.zeros(self.X)]
        sol=SimpleNamespace(x=x,fun=float(cost@x),nit=int(info.simplex_iteration_count+info.ipm_iteration_count),
            eqlin=SimpleNamespace(marginals=y[:1]),ineqlin=SimpleNamespace(marginals=y[1:]),
            lower=SimpleNamespace(marginals=lower),upper=SimpleNamespace(marginals=np.zeros(len(x))))
        report=core.check_solution(cost,self.Ae,self.be,self.Au,self.bu,self.lo,self.hi,sol,TOL)
        report['residuals']['free_variable_reduced_cost']=free_residual
        if free_residual>TOL:raise RuntimeError(f'Nonzero free-variable reduced cost {free_residual}')
        G=-y[1+self.Q*self.Y:].reshape(self.X,self.Y)
        raw_row=float(np.max(abs(G.sum(1)-1),initial=0));raw_neg=core.violation(-G)
        if max(raw_row,raw_neg)>TOL:raise RuntimeError(f'Invalid raw decoder {raw_row}, {raw_neg}')
        raw_G=G.copy();G=np.maximum(G,0);den=G.sum(1,keepdims=True)
        if np.any(den<=0):raise RuntimeError('Empty repaired decoder row')
        G/=den
        a_raw=x[:self.Q];b_raw=x[self.Q:self.Q+self.Q*self.Y].reshape(self.Q,self.Y)
        alpha=np.maximum(a_raw,0)
        if alpha.sum()<=0:raise RuntimeError('Zero decision prior')
        alpha/=alpha.sum();b=np.minimum(np.maximum(b_raw,0),alpha[:,None])
        upper=float(np.max(abs(self.E@G-F).sum(1)/2))
        lower=float(np.sum(F*b)-np.max(self.E.T@b,axis=1).sum())
        errors=[abs(upper+sol.fun),abs(lower+sol.fun),upper-lower,lower-upper]
        if max(errors)>TOL:raise RuntimeError(f'Repaired witnesses disagree: {lower}, {upper}, {-sol.fun}')
        report.update(lower=lower,upper=upper,bracket=upper-lower,
                      raw_decoder_row_residual=raw_row,raw_decoder_negative=raw_neg,
                      decoder_repair_max=float(np.max(abs(G-raw_G),initial=0)),
                      alpha_repair_max=float(np.max(abs(alpha-a_raw),initial=0)),
                      b_repair_max=float(np.max(abs(b-b_raw),initial=0)),
                      simplex_iterations=int(info.simplex_iteration_count),ipm_iterations=int(info.ipm_iteration_count))
        return report,dict(source_indices=self.keep.copy(),decoder=G,alpha=alpha,b=b)

    def solve(self,F):
        started=time.perf_counter();deadline=started+self.time_limit
        F=np.asarray(F,dtype=float)
        if F.shape!=(self.Q,self.Y) or not np.all(np.isfinite(F)) or np.any(F<0):
            raise ValueError('Target must be a nonnegative matrix of the declared shape')
        if np.max(abs(F.sum(1)-1))>TOL:raise ValueError('Target rows are not stochastic')
        cost=self.c.copy();cost[self.cost_indices]=-F.ravel()
        attempts=[];solve_seconds=0.;update_seconds=0.;verify_seconds=0.
        strategies=[('retained',self.solver),('cold',self.solver),('cold_alternate','ipm' if self.solver=='simplex' else 'simplex')]
        for mode,solver in strategies:
            remaining=deadline-time.perf_counter()
            if remaining<=0:break
            attempt=dict(mode=mode,solver=solver);ts=time.perf_counter()
            try:
                if mode=='retained':
                    h=self.h
                    status=h.changeColsCost(len(self.cost_indices),self.cost_indices,cost[self.cost_indices])
                    if status!=highspy.HighsStatus.kOk:raise RuntimeError('Objective update rejected')
                else:h=self._new_solver(solver,cost)
                update=time.perf_counter()-ts;update_seconds+=update;attempt['update_seconds']=update
                remaining=deadline-time.perf_counter()
                if remaining<=0:raise TimeoutError('Decoder call budget exhausted during setup')
                # HiGHS run time accumulates on a persistent model. Its limit is
                # absolute in that clock; our remaining budget is per solve(F).
                attempt['prior_solver_run_seconds']=h.getRunTime()
                h.setOptionValue('time_limit',h.getRunTime()+remaining)
                ts=time.perf_counter();h.run();elapsed=time.perf_counter()-ts
                solve_seconds+=elapsed;attempt['solve_seconds']=elapsed
                status=h.getModelStatus();attempt['status']=h.modelStatusToString(status)
                if status!=highspy.HighsModelStatus.kOptimal:raise RuntimeError(attempt['status'])
                ts=time.perf_counter();report,witness=self._extract(h,cost,F)
                checked=time.perf_counter()-ts;verify_seconds+=checked
                attempt.update(success=True,verify_seconds=checked);attempts.append(attempt)
                self.h=h;self.solver=solver;self.calls+=1
                report.update(method='native-'+solver,solve_seconds=solve_seconds,update_seconds=update_seconds,
                              verify_seconds=verify_seconds,total_seconds=time.perf_counter()-started,
                              attempts=attempts,fallback_used=len(attempts)>1,call_index=self.calls,
                              import_reports=self.import_reports.copy(),
                              backend_version=h.version())
                return report,witness
            except Exception as exc:
                attempt.update(success=False,error=repr(exc));attempts.append(attempt)
        raise RuntimeError(f'Native decoder failed within {self.time_limit}s budget: {attempts}')


def _digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def _write(p,value):
    tmp=p.with_suffix('.tmp');tmp.write_text(json.dumps(value,indent=2,allow_nan=False)+'\n');tmp.replace(p)
def _check_witness(E,F,r,w):
    G=w['decoder'];a=w['alpha'];b=w['b'];source=E[:,w['source_indices']]
    residual=max(float(np.max(abs(G.sum(1)-1))),float(max(0,-G.min())),abs(float(a.sum())-1),float(max(0,-a.min())),float(max(0,-b.min())),float(np.max(np.maximum(b-a[:,None],0))))
    upper=float(np.max(abs(source@G-F).sum(1)/2));lower=float(np.sum(F*b)-np.max(source.T@b,axis=1).sum())
    if max(residual,abs(upper-r['upper']),abs(lower-r['lower']),upper-lower)>TOL:raise RuntimeError('Independent witness replay failed')
    return residual

def sweep(case,backend,order):
    resource.setrlimit(resource.RLIMIT_AS,(8*1024**3,8*1024**3))
    # Runtime option only: do not mutate the shared core source file.
    core.OPTIONS=core.OPTIONS|{'threads':1}
    if hasattr(os,'sched_getaffinity'):
        os.sched_setaffinity(0,{min(os.sched_getaffinity(0))})
    source_path=core.OLD/'results'/case/'native_weighted_optimum_policy.npz'
    E=np.load(source_path)['E'];model=core.model(case);targets=core.Targets(model['T'],model['Z'],3)
    indices=np.arange(targets.count)
    if order=='seeded':indices=np.random.default_rng(92317).permutation(indices)
    ts=time.perf_counter();decoder=(NativeDecoder if backend=='native' else core.Decoder)(E,8);setup=time.perf_counter()-ts
    reports=[];saved={};started=time.perf_counter()
    for index in indices:
        F=targets.get(int(index))['kernel'];r,w=decoder.solve(F)
        residual=_check_witness(E,F,r,w);r.update(target=int(index),witness_feasibility=residual)
        reports.append(r)
        for key,value in w.items():saved[f'{int(index)}__{key}']=value
    total=time.perf_counter()-started
    stem=f'{case}__{backend}__{order}'
    np.savez_compressed(OUT/(stem+'_witnesses.npz'),**saved)
    data=dict(case=case,backend=backend,order=order,seed=92317,source_sha256=_digest(source_path),
              setup_seconds=setup,total_seconds=total,total_including_setup_seconds=total+setup,
              solver_seconds=sum(r['solve_seconds'] for r in reports),
              peak_rss_mib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024,
              target_count=targets.count,exhaustive=True,rows=reports)
    _write(OUT/(stem+'.json'),data)

def validation_checks():
    # Exact controls exercise null source columns, singleton classes, and fallback.
    records=[]
    for name,E,F,expected in [
        ('singleton',np.array([[.2,.8]]),np.array([[.3,.7]]),0.),
        ('no_information',np.array([[1.,0.],[1.,0.]]),np.eye(2),.5),
        ('full_revelation',np.eye(2),np.array([[.1,.9],[.8,.2]]),0.)]:
        d=NativeDecoder(E,F.shape[1]);r,w=d.solve(F);_check_witness(E,F,r,w)
        assert abs(r['upper']-expected)<=TOL
        records.append(dict(name=name,report=r))
    d=NativeDecoder(np.array([[.8,.2],[.2,.8]]),2)
    class RejectUpdate:
        def changeColsCost(self,*args):return highspy.HighsStatus.kError
    d.h=RejectUpdate();F=np.eye(2);r,w=d.solve(F);_check_witness(d.E,F,r,w)
    assert r['fallback_used'] and len(r['attempts'])==2 and r['attempts'][0]['success'] is False
    records.append(dict(name='injected_objective_update_failure',report=r))
    d=NativeDecoder(np.array([[.8,.2],[.2,.8]]),2);original=d._extract;calls=[0]
    def reject_first(*args):
        calls[0]+=1
        if calls[0]==1:raise RuntimeError('Injected raw KKT residual above tolerance')
        return original(*args)
    d._extract=reject_first;r,w=d.solve(F);_check_witness(d.E,F,r,w)
    assert r['fallback_used'] and len(r['attempts'])==2
    records.append(dict(name='injected_validation_failure',report=r))
    try:d.solve(np.array([[np.nan,0.],[0.,1.]]))
    except ValueError:records.append(dict(name='reject_nan_target',passed=True))
    else:raise AssertionError('NaN target accepted')
    E=np.load(core.OLD/'results/sensors_0.1_0.3/native_weighted_optimum_policy.npz')['E']
    model=core.model('sensors_0.1_0.3');targets=core.Targets(model['T'],model['Z'],3)
    d=NativeDecoder(E,8,time_limit=.1);failures=0;max_call=0.
    for index in range(targets.count):
        report,witness=d.solve(targets.get(index)['kernel'])
        failures+=int(report['fallback_used']);max_call=max(max_call,report['total_seconds'])
    assert d.h.getRunTime()>.1 and failures==0
    records.append(dict(name='persistent_cumulative_timer',calls=128,per_call_limit=.1,
                        cumulative_solver_seconds=d.h.getRunTime(),max_call_seconds=max_call,
                        fallback_calls=failures,passed=True))
    _write(OUT/'validation_checks.json',dict(passed=True,records=records))

def benchmark():
    OUT.mkdir(exist_ok=True);jobs=[]
    from scipy.optimize._highspy._core import _Highs
    _write(OUT/'manifest.json',dict(source_sha256=_digest(__file__),core_sha256=_digest(core.__file__),
        highspy=highspy.Highs().version(),scipy_highs=_Highs().version(),cases=CASES,
        target_horizon=3,collector='saved H3 native_weighted optimum',target_count=128,
        orders=['fixed','seeded'],seed=92317,threads=1,time_limit=120,address_space_gib=8))
    for case in CASES:
        for backend in ['scipy','native']:
            for order in ['fixed','seeded']:
                stem=f'{case}__{backend}__{order}';ts=time.perf_counter()
                with (OUT/(stem+'.log')).open('w') as log:
                    try:
                        run=subprocess.run([sys.executable,'-B',__file__,'--worker',case,backend,order],stdout=log,stderr=subprocess.STDOUT,timeout=300)
                        status=run.returncode
                    except subprocess.TimeoutExpired:status='worker_timeout'
                jobs.append(dict(case=case,backend=backend,order=order,status=status,seconds=time.perf_counter()-ts))
                _write(OUT/'jobs.json',jobs);print(stem,status,flush=True)
    summary=[]
    for case in CASES:
        ref=json.loads((OUT/f'{case}__scipy__fixed.json').read_text());values={r['target']:r['upper'] for r in ref['rows']}
        for backend in ['scipy','native']:
            for order in ['fixed','seeded']:
                d=json.loads((OUT/f'{case}__{backend}__{order}.json').read_text())
                diff=max(abs(r['upper']-values[r['target']]) for r in d['rows'])
                if diff>TOL:raise RuntimeError(f'Full value profile disagreement: {case} {backend} {order} {diff}')
                summary.append({k:v for k,v in d.items() if k!='rows'}|dict(max_profile_difference=diff,
                    max_bracket=max(r['bracket'] for r in d['rows']),max_kkt_residual=max(max(r['residuals'].values()) for r in d['rows']),
                    fallback_calls=sum(r.get('fallback_used',False) for r in d['rows']),max_witness_feasibility=max(r['witness_feasibility'] for r in d['rows'])))
    _write(OUT/'summary.json',dict(all_profiles_agree=True,solves=12*128,rows=summary))
    validation_checks()

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--benchmark',action='store_true');parser.add_argument('--worker',nargs=3);args=parser.parse_args()
    if args.worker:sweep(*args.worker)
    elif args.benchmark:benchmark()
    else:parser.error('Use --benchmark or --worker CASE BACKEND ORDER')
