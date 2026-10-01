"""Pre-outcome GPU fixed-source audit feasibility; no policy optimization.

Original E, F are never rounded/coarsened for witness evaluation. Numerical
brackets are repaired stochastic decoder upper/feasible decision-dual lower
bounds, NOT formally outward-rounded interval certificates.
"""
import os
for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):
    os.environ[key]='1'
os.sched_setaffinity(0,{20,21,22,23})
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json,time,hashlib,importlib.metadata
import numpy as np
from scipy import sparse
from scipy.optimize import linprog
HERE=Path(__file__).resolve().parent
SOURCE=HERE.parents[1]/'target_selection_2026-09-23'
sys.path.insert(0,str(SOURCE))
import scaling_core as core
from certified_decoder import StableDecoder
from cuopt.linear_programming import DataModel,Solve
from cuopt.linear_programming.solver_settings import SolverSettings,SolverMethod
from cuopt.linear_programming.solver.solver_parameters import CUOPT_METHOD
TOL=2e-7

def write(name,value):
    (HERE/name).write_text(json.dumps(value,indent=2,allow_nan=False)+'\n')

def replay(E,F,G,alpha,b):
    residual=max(float(abs(G.sum(axis=1)-1).max()),float(max(0,-G.min())),float(abs(alpha.sum()-1)),float(max(0,-alpha.min())),float(max(0,-b.min())),float(np.maximum(b-alpha[:,None],0).max()))
    upper=float(np.max(np.abs(E@G-F).sum(axis=1)/2))
    lower=float(np.sum(F*b)-np.max(E.T@b,axis=1).sum())
    if not np.isfinite([upper,lower,residual]).all() or residual>1e-12 or lower>upper+1e-10:raise RuntimeError('Original probability witness infeasible')
    return dict(lower=lower,upper=upper,gap=upper-lower,feasibility=residual)

class GPUBatch:
    def __init__(self,E,Y,B,tag):
        self.E=E;self.Y=Y;self.B=B;self.tag=tag
        d=core.Decoder(E,Y);self.d=d
        # Alpha and b lie in [0,1]. Optimal s_x=max_y (E^T b)_xy
        # lies in [0,max_q E_qx], hence in [0,1]. The bounded LP is exact.
        A=sparse.vstack([d.Ae,d.Au],format='csr')
        M=sparse.block_diag([A]*B,format='csr')
        self.model=DataModel();self.model.set_csr_constraint_matrix(M.data,M.indices.astype(np.int32),M.indptr.astype(np.int32))
        self.model.set_constraint_bounds(np.tile(np.r_[d.be,d.bu],B))
        self.model.set_row_types(np.tile(np.array(['E']+['L']*len(d.bu)),B))
        self.model.set_variable_lower_bounds(np.zeros(B*len(d.c)))
        self.model.set_variable_upper_bounds(np.ones(B*len(d.c)))
        self.model.set_maximize(False)
        self.settings=SolverSettings();self.settings.set_parameter(CUOPT_METHOD,SolverMethod.PDLP)
        self.settings.set_parameter('num_cpu_threads',4)
        self.settings.set_parameter('log_to_console',False)
        self.settings.set_parameter('log_file',str(HERE/(tag+'.cuopt.log')))
        self.settings.set_optimality_tolerance(1e-10)
        self.settings.set_parameter('time_limit',20.)
    def solve(self,Fs,save=None):
        d=self.d;B=self.B;assert len(Fs)==B
        c=np.tile(d.c,(B,1));c[:,d.Q:d.Q+d.Q*d.Y]=-Fs.reshape(B,-1)
        self.model.set_objective_coefficients(c.ravel())
        start=time.perf_counter();fit=Solve(self.model,self.settings);seconds=time.perf_counter()-start
        term=str(fit.get_termination_reason())
        xs=np.asarray(fit.get_primal_solution(),dtype=float).reshape(B,-1)
        ds=np.asarray(fit.get_dual_solution(),dtype=float).reshape(B,-1)
        if not np.isfinite(xs).all() or not np.isfinite(ds).all():raise RuntimeError('nonfinite GPU')
        reports=[];saved={}
        for k,F in enumerate(Fs):
            raw=-ds[k,1+d.Q*d.Y:].reshape(d.X,d.Y)
            G=np.maximum(raw,0);den=G.sum(axis=1,keepdims=True)
            G=np.divide(G,den,out=np.full_like(G,1/d.Y),where=den>0)
            alpha=np.maximum(xs[k,:d.Q],0)
            alpha=alpha/alpha.sum() if alpha.sum()>0 else np.ones(d.Q)/d.Q
            b=np.clip(xs[k,d.Q:d.Q+d.Q*d.Y].reshape(d.Q,d.Y),0,alpha[:,None])
            # Lift arbitrary rows at exactly null source columns.
            GG=np.full((self.E.shape[1],d.Y),1/d.Y);GG[d.keep]=G
            report=replay(self.E,F,GG,alpha,b)
            report.update(raw_decoder_row_error=float(abs(raw.sum(1)-1).max()),raw_decoder_negative=float(max(0,-raw.min())),accepted=report['gap']<=TOL)
            reports.append(report)
            saved.update({f'{k}_G':GG,f'{k}_alpha':alpha,f'{k}_b':b})
        if save:np.savez_compressed(HERE/save,E=self.E,F=Fs,raw_primal=xs,raw_dual=ds,**saved)
        return dict(seconds=seconds,termination=term,rows=reports,all_accepted=all(r['accepted'] for r in reports))

def cpu_primal(E,F):
    # Independently assemble the direct decoder primal (not core's dual LP).
    Q,X=E.shape;Y=F.shape[1];V=X*Y+Q*Y+1;rr=[];cc=[];vv=[];rhs=[]
    for sign in (1.,-1.):
        for q in range(Q):
            for y in range(Y):
                row=len(rhs);rhs.append(sign*F[q,y])
                for x in range(X):rr.append(row);cc.append(x*Y+y);vv.append(sign*E[q,x])
                rr.append(row);cc.append(X*Y+q*Y+y);vv.append(-1.)
    for q in range(Q):
        row=len(rhs);rhs.append(0.)
        for y in range(Y):rr.append(row);cc.append(X*Y+q*Y+y);vv.append(.5)
        rr.append(row);cc.append(V-1);vv.append(-1.)
    Au=sparse.coo_matrix((vv,(rr,cc)),shape=(len(rhs),V)).tocsr()
    Ae=sparse.hstack([sparse.kron(sparse.eye(X),np.ones((1,Y))),sparse.csr_matrix((X,Q*Y+1))],format='csr')
    c=np.zeros(V);c[-1]=1
    fit=linprog(c,A_ub=Au,b_ub=rhs,A_eq=Ae,b_eq=np.ones(X),bounds=(0,1),method='highs',options={'threads':1,'primal_feasibility_tolerance':1e-9,'dual_feasibility_tolerance':1e-9})
    if not fit.success:raise RuntimeError(fit.message)
    G=np.maximum(fit.x[:X*Y].reshape(X,Y),0);G/=G.sum(1,keepdims=True)
    return float(np.max(abs(E@G-F).sum(1)/2))

def main():
    started=time.perf_counter()
    protocol=dict(purpose='pre-outcome feasibility only; uniform-action collectors',seeds=[926101,926102],worlds=[4,8],collector_horizons=[3,4],target_depth=4,target_count=32768,concentration=1.,hidden_states=3,compute_budget_seconds=600,cpu_affinity=[20,21,22,23],maximum_gpu_threads=4,tolerance=TOL,source_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [SOURCE/'scaling_core.py',SOURCE/'certified_decoder.py',SOURCE/'fast_decoder.py',SOURCE/'gpu_solver.py',Path(__file__)]},versions={x:importlib.metadata.version(x) for x in ['numpy','scipy','highspy','cuopt-cu12']})
    write('PROTOCOL.json',protocol)
    cases=[('null_columns',np.array([[1.,0.,0.],[1.,0.,0.]]),np.eye(2),.5),('perfect_zero_loss',np.eye(2),np.array([[.1,.9],[.8,.2]]),0.),('tiny_columns',np.array([[1-1e-12,1e-12,0],[1-2e-12,2e-12,0]]),np.eye(2),.5-5e-13),('near_zero_loss',np.array([[1.-1e-12,1e-12],[1e-12,1.-1e-12]]),np.eye(2),1e-12)]
    controls=[]
    for name,E,F,expected in cases:
        result=GPUBatch(E,F.shape[1],1,'control_'+name).solve(F[None],name+'_witness.npz')
        r,w=StableDecoder(E,F.shape[1]).solve(F)
        primal=cpu_primal(E,F)
        result.update(name=name,expected=expected,cpu=r,independent_cpu_primal_upper=primal)
        result['crosscheck']=result['all_accepted'] and abs(result['rows'][0]['upper']-expected)<=TOL and abs(primal-r['upper'])<=TOL
        controls.append(result);write('controls.json',controls)
        print('CONTROL',name,result['termination'],result['seconds'],result['rows'][0],flush=True)
    if not all(c['crosscheck'] for c in controls):
        write('RESULTS.json',dict(status='gpu_validation_failed',controls_passed=False,seconds=time.perf_counter()-started));return
    timing=[];selected=np.array([0,1,2,3,7,31,127,511,1023,4095,8191,16383,24575,30001,32766,32767])
    for seed in protocol['seeds']:
      for Q in protocol['worlds']:
       m=core.random_model(seed,worlds=Q);targets=core.Targets(m['T'],m['Z'],4)
       for t in protocol['collector_horizons']:
        if time.perf_counter()-started>450:break
        tag=f'seed{seed}_q{Q}_t{t}';g=core.geometry(m['T'],m['Z'],t);E=g.raw/(2**t)
        np.savez_compressed(HERE/(tag+'_model.npz'),T=m['T'],Z=m['Z'],E=E)
        Fs=np.stack([targets.get(int(i))['kernel'] for i in selected])
        dec=GPUBatch(E,16,len(selected),tag);gpu=dec.solve(Fs,tag+'_witness.npz')
        cpu=StableDecoder(E,16);cpurows=[];tick=time.perf_counter()
        for i,F in enumerate(Fs):
            r,w=cpu.solve(F);rc=replay(E[:,w['source_indices']],F,w['decoder'],w['alpha'],w['b']);rc['target']=int(selected[i]);cpurows.append(rc)
        cpu_seconds=time.perf_counter()-tick
        cpu_direct=[dict(target=int(selected[i]),upper=cpu_primal(E,Fs[i])) for i in [0,7,15]]
        crosscheck=all(max(a['lower'],b['lower'])<=min(a['upper'],b['upper'])+1e-10 for a,b in zip(gpu['rows'],cpurows))
        row=dict(tag=tag,seed=seed,worlds=Q,t=t,target_ids=selected.tolist(),gpu=gpu,cpu_rows=cpurows,cpu_seconds=cpu_seconds,independent_cpu_primal=cpu_direct,crosscheck=crosscheck,full_audit_seconds_linear_gpu_estimate=gpu['seconds']*32768/len(selected),full_audit_seconds_linear_cpu_estimate=cpu_seconds*32768/len(selected))
        timing.append(row);write('timing.json',timing)
        print('TIMING',tag,'gpu',gpu['seconds'],'accepted',gpu['all_accepted'],'cpu',cpu_seconds,'bracket',max(r['gap'] for r in gpu['rows']),flush=True)
    # Launch one complete audit only if measured GPU throughput conservatively
    # fits the remaining original budget. This is a feasibility gate, not ranking.
    eligible=[r for r in timing if r['gpu']['all_accepted'] and r['crosscheck'] and r['full_audit_seconds_linear_gpu_estimate']*1.5+time.perf_counter()-started<550]
    full=None
    if eligible:
        r=eligible[0];m=core.random_model(r['seed'],worlds=r['worlds']);g=core.geometry(m['T'],m['Z'],r['t']);E=g.raw/2**r['t'];targets=core.Targets(m['T'],m['Z'],4);B=128;dec=GPUBatch(E,16,B,r['tag']+'_full');rows=[];tick=time.perf_counter();failures=[]
        for first in range(0,32768,B):
            if time.perf_counter()-started>580:break
            Fs=np.stack([targets.get(i)['kernel'] for i in range(first,first+B)])
            result=dec.solve(Fs)
            for j,rr in enumerate(result['rows']):rr['target']=first+j;rows.append(rr)
            if not result['all_accepted']:failures.append(first);break
            if first%2048==0:print('FULL',first,len(rows),time.perf_counter()-tick,flush=True)
        full=dict(tag=r['tag'],count=len(rows),complete=len(rows)==32768,seconds=time.perf_counter()-tick,failures=failures,rows=rows)
        write('full_audit.json',full)
    write('RESULTS.json',dict(status='completed_pilot',controls_passed=True,cases=len(timing),gpu_validated_cases=sum(r['gpu']['all_accepted'] and r['crosscheck'] for r in timing),full_audit=None if full is None else {k:v for k,v in full.items() if k!='rows'},total_seconds=time.perf_counter()-started))
if __name__=='__main__':main()
