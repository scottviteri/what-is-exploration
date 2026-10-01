"""Finite supplied-model planning; independent t/n; compact realization LP.

Policies retain full histories. Floating-point certificates, not exact arithmetic.
This module never writes to earlier experiment directories.
"""
from __future__ import annotations
from dataclasses import dataclass
import hashlib
import importlib.util
import itertools
from pathlib import Path
import time
import warnings

import numpy as np
from scipy import sparse
from scipy.optimize import linprog

HERE = Path(__file__).resolve().parent
OLD = HERE.parent / 'native_objective_benchmark_2026-09-15'
OPTIONS = dict(primal_feasibility_tolerance=1e-9,
               dual_feasibility_tolerance=1e-9, ipm_optimality_tolerance=1e-10,
               time_limit=120.,threads=1)
TOL = 2e-7


def old_models():
    spec = importlib.util.spec_from_file_location('scaling_archived_models', OLD/'compute.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.environments()


def model(name):
    for case in old_models():
        if case['name'] == name:
            return case
    raise KeyError(name)


def random_model(seed, worlds=8, states=3, concentration=1.):
    rng = np.random.default_rng(seed)
    return dict(name=f'fresh_hmm_{seed}_q{worlds}_s{states}_c{concentration}', family='fresh_hmm',
                T=rng.dirichlet(np.full(states, concentration), size=(worlds, 2, states)),
                Z=rng.dirichlet(np.full(2, concentration), size=(worlds, 2, states)))


def levels(horizon):
    layers = [[()]]
    for _ in range(horizon):
        layers.append([h+((a,o),) for h in layers[-1] for a in range(2) for o in range(2)])
    return layers


def masses(T, Z, layers):
    first = np.zeros((len(T), T.shape[-1])); first[:,0] = 1
    states = {(): first}
    result = {(): np.ones(len(T))}
    for layer in layers[:-1]:
        next_states = {}
        for h in layer:
            for a in range(2):
                predicted = np.einsum('qs,qsu->qu', states[h], T[:,a])
                for o in range(2):
                    child = h+((a,o),)
                    value = predicted * Z[:,a,:,o]
                    next_states[child] = value
                    result[child] = value.sum(axis=1)
        states = next_states
    return result


@dataclass
class Geometry:
    layers: list
    p: dict
    raw: np.ndarray
    decisions: list
    decision_index: dict
    leaf_index: np.ndarray
    flow: sparse.csr_matrix
    flow_rhs: np.ndarray
    seconds: float


def geometry(T, Z, horizon):
    if horizon < 1:
        raise ValueError('Collector horizon must be positive in this implementation')
    started = time.perf_counter()
    layers = levels(horizon); p = masses(T,Z,layers)
    decisions = [h for layer in layers[:-1] for h in layer]
    index = {h:i for i,h in enumerate(decisions)}
    rr=[];cc=[];vv=[]
    for row,h in enumerate(decisions):
        for a in range(2):
            rr.append(row);cc.append(2*index[h]+a);vv.append(1.)
        if h:
            rr.append(row);cc.append(2*index[h[:-1]]+h[-1][0]);vv.append(-1.)
    P=2*len(decisions)
    flow=sparse.coo_matrix((vv,(rr,cc)),shape=(len(decisions),P)).tocsr()
    rhs=np.zeros(len(decisions));rhs[0]=1
    leaf_index=np.array([2*index[h[:-1]]+h[-1][0] for h in layers[-1]])
    raw=np.array([p[h] for h in layers[-1]]).T
    return Geometry(layers,p,raw,decisions,index,leaf_index,flow,rhs,time.perf_counter()-started)


def reward_coefficients(g, prior=None):
    Q,S=g.raw.shape
    prior=np.ones(Q)/Q if prior is None else np.asarray(prior,dtype=float)
    if prior.shape!=(Q,) or np.min(prior)<0 or abs(prior.sum()-1)>1e-12:
        raise ValueError('Invalid supplied prior')
    m=prior@g.raw
    posterior=np.divide(prior[:,None]*g.raw,m,out=np.zeros_like(g.raw),where=m>0)
    def entropy(x,axis=0):
        return -(x*np.log2(np.where(x>0,x,1))).sum(axis=axis)
    return dict(information=m*(entropy(prior)-entropy(posterior)),
                brier=m*((posterior**2).sum(axis=0)-(prior**2).sum()),
                surprisal=-m*np.log2(np.where(m>0,m,1)),
                first_visit=m*np.array([len({o for _,o in h}) for h in g.layers[-1]]))


def target_library(T,Z):
    targets=[]
    for length in [1,2,3]:
        layers=levels(length);p=masses(T,Z,layers)
        for word in itertools.product(range(2),repeat=length):
            keep=[h for h in layers[-1] if tuple(a for a,_ in h)==word]
            targets.append(dict(name=''.join('LR'[a] for a in word),
                                weight=.1 if length==1 else .05,
                                kernel=np.array([p[h] for h in keep]).T))
    for length in [1,3]:
        layers=levels(length);p=masses(T,Z,layers)
        keep=[h for h in layers[-1] if len({a for a,_ in h})==1]
        targets.append(dict(name=f'tagged_{length}',weight=.05,
                            kernel=.5*np.array([p[h] for h in keep]).T))
    return targets


class Targets:
    """Generate each tree on demand, avoiding the collector-horizon target bug."""
    def __init__(self,T,Z,horizon):
        if horizon<1 or horizon>4:
            raise ValueError('Exhaustive target implementation explicitly limited to n=1..4')
        self.n=horizon;self.layers=levels(horizon);self.p=masses(T,Z,self.layers)
        self.nodes=2**horizon-1;self.count=2**self.nodes

    def choices(self,index):
        return [(index>>(self.nodes-1-k))&1 for k in range(self.nodes)]

    def get(self,index):
        if not 0<=index<self.count: raise IndexError(index)
        choices=self.choices(index);signals=[]
        for obs in itertools.product(range(2),repeat=self.n):
            h=();node=0
            for o in obs:
                a=choices[node];h+=((a,o),);node=2*node+1+o
            signals.append(h)
        F=np.array([self.p[h] for h in signals]).T
        return dict(name=f'tree_{index}',kernel=F,weight=1/self.count)

    def fixed_indices(self):
        result=[]
        for actions in itertools.product(range(2),repeat=self.n):
            choices=[a for depth,a in enumerate(actions) for _ in range(2**depth)]
            index=0
            for a in choices:index=2*index+a
            result.append(index)
        return result


def violation(value):
    return float(np.max(np.maximum(value,0),initial=0))


def check_solution(c,Ae,be,Au,bu,lo,hi,sol,tolerance=TOL):
    x=sol.x
    if not all(np.all(np.isfinite(v)) for v in [c,x,be,bu,sol.eqlin.marginals,sol.ineqlin.marginals,sol.lower.marginals,sol.upper.marginals]):raise RuntimeError('Nonfinite LP certificate')
    residuals=dict(equality=float(np.max(np.abs(Ae@x-be),initial=0)),
                   inequality=violation(Au@x-bu),lower=violation(lo-x),upper=violation(x-hi),
                   inequality_dual_sign=violation(sol.ineqlin.marginals),
                   lower_dual_sign=violation(-sol.lower.marginals),
                   upper_dual_sign=violation(sol.upper.marginals))
    stationarity=c-Ae.T@sol.eqlin.marginals-Au.T@sol.ineqlin.marginals-sol.lower.marginals-sol.upper.marginals
    residuals['stationarity']=float(np.max(np.abs(stationarity),initial=0))
    lower_terms=lo[np.isfinite(lo)]@sol.lower.marginals[np.isfinite(lo)]
    upper_terms=hi[np.isfinite(hi)]@sol.upper.marginals[np.isfinite(hi)]
    dual=float(be@sol.eqlin.marginals+bu@sol.ineqlin.marginals+lower_terms+upper_terms)
    raw_dual=dual
    residuals['gap']=abs(float(c@x)-dual)
    if np.all(np.isfinite(lo)) and np.all(np.isfinite(hi)):
        # Bound-box Lagrangian repair charges accumulated stationarity error.
        inequality_dual=np.minimum(sol.ineqlin.marginals,0.)
        remaining=c-Ae.T@sol.eqlin.marginals-Au.T@inequality_dual
        dual=float(be@sol.eqlin.marginals+bu@inequality_dual+
                   np.minimum(lo*remaining,hi*remaining).sum())
        residuals['repaired_gap']=abs(float(c@x)-dual)
    if any(not np.isfinite(v) for v in residuals.values()) or max(residuals.values())>tolerance:
        raise RuntimeError(f'LP numerical certificate failed: {residuals}')
    return dict(primal=float(c@x),dual=dual,raw_dual=raw_dual,residuals=residuals,
                iterations=int(sol.nit),variables=len(c),equalities=len(be),inequalities=len(bu))


def solve_arrays(c,Ae,be,Au,bu,bounds,method='highs',time_limit=120):
    if method=='cuopt-pdlp':
        from gpu_solver import solve_arrays as gpu_solve
        return gpu_solve(c,Ae,be,Au,bu,bounds,time_limit=time_limit)
    options=OPTIONS|{'time_limit':float(time_limit)}
    started=time.perf_counter()
    with warnings.catch_warnings(record=True) as solver_warnings:
        warnings.simplefilter('always')
        sol=linprog(c,A_eq=Ae,b_eq=be,A_ub=Au if len(bu) else None,
                    b_ub=bu if len(bu) else None,bounds=bounds,method=method,options=options)
    seconds=time.perf_counter()-started
    if not sol.success:raise RuntimeError(f'{method}: {sol.message}')
    lo=np.array([-np.inf if a is None else a for a,b in bounds])
    hi=np.array([np.inf if b is None else b for a,b in bounds])
    checked=check_solution(np.asarray(c),Ae,np.asarray(be),Au,np.asarray(bu),lo,hi,sol)
    checked.update(solve_seconds=seconds,method=method,warnings=list({str(w.message) for w in solver_warnings}))
    return sol,checked


def replay(g,action_weights):
    """Replay recovered conditional rows, rather than trusting LP leaf weights."""
    weights={():1.};rows=[]
    for h in g.decisions:
        q=np.maximum(action_weights[2*g.decision_index[h]:2*g.decision_index[h]+2],0)
        row=q/q.sum() if q.sum()>0 else np.full(2,.5)
        rows.append(row)
        for a in range(2):
            for o in range(2):weights[h+((a,o),)]=weights[h]*row[a]
    leaf=np.array([weights[h] for h in g.layers[-1]])
    E=g.raw*leaf
    if np.max(np.abs(E.sum(axis=1)-1))>TOL:raise RuntimeError('Policy law is not stochastic')
    return E,np.array(rows),leaf


def reward_plan(g,coefficients,method='highs',time_limit=120):
    started=time.perf_counter();P=g.flow.shape[1]
    c=-np.bincount(g.leaf_index,weights=coefficients,minlength=P)
    built=time.perf_counter()-started
    sol,report=solve_arrays(c,g.flow,g.flow_rhs,sparse.csr_matrix((0,P)),[],[(0,1)]*P,method,time_limit)
    E,rows,leaf=replay(g,sol.x)
    achieved=float(leaf@coefficients)
    if abs(achieved+sol.fun)>TOL:raise RuntimeError('Reward replay failed')
    report.update(build_seconds=built,reward=achieved)
    return E,rows,leaf,report


class Builder:
    def __init__(self):
        self.cost=[];self.eq=[];self.ub=[];self.be=[];self.bu=[]
    def variables(self,n,cost=0):
        start=len(self.cost);self.cost.extend([cost]*n);return start
    def rows(self,parts,rhs,equality=False):
        destination=self.eq if equality else self.ub
        right=self.be if equality else self.bu
        base=len(right);right.extend(np.asarray(rhs).ravel().tolist())
        for offset,block in parts:
            mat=sparse.coo_matrix(block)
            destination.append((mat.row+base,mat.col+offset,mat.data))
    def matrix(self,equality):
        entries=self.eq if equality else self.ub
        count=len(self.be if equality else self.bu)
        if not entries:return sparse.csr_matrix((count,len(self.cost)))
        rr,cc,vv=(np.concatenate([entry[i] for entry in entries]) for i in range(3))
        return sparse.coo_matrix((vv,(rr,cc)),shape=(count,len(self.cost))).tocsr()


def native_plan(g,targets,kind='native_weighted',method='highs',time_limit=120,certificate_path=None,
                reward_constraint=None,compact_certificate=False):
    started=time.perf_counter();Q,S=g.raw.shape;P=g.flow.shape[1]
    lp=Builder();lp.variables(P);lp.rows([(0,g.flow)],g.flow_rhs,True)
    if reward_constraint is not None:
        coefficients,threshold=reward_constraint
        action_reward=np.bincount(g.leaf_index,weights=coefficients,minlength=P)
        lp.rows([(0,sparse.csr_matrix(-action_reward.reshape(1,-1)))],[-float(threshold)])
    minimax=kind=='native_minimax'
    mm=lp.variables(1,1.) if minimax else None
    assign=sparse.coo_matrix((np.ones(S),(np.arange(S),g.leaf_index)),shape=(S,P)).tocsr()
    for target in targets:
        F=target['kernel'];Y=F.shape[1]
        if F.shape[0]!=Q:raise ValueError('Target hypothesis class differs')
        d=lp.variables(1,0 if minimax else target['weight'])
        z=lp.variables(S*Y);e=lp.variables(Q*Y)
        if minimax:lp.rows([(d,sparse.csr_matrix([[1.]])),(mm,sparse.csr_matrix([[-1.]]))],[0])
        normal=sparse.kron(sparse.eye(S),np.ones((1,Y)),format='csr')
        lp.rows([(z,normal),(0,-assign)],np.zeros(S),True)
        decoded=sparse.kron(sparse.csr_matrix(g.raw),sparse.eye(Y),format='csr')
        eye=sparse.eye(Q*Y,format='csr')
        lp.rows([(z,decoded),(e,-eye)],F.ravel())
        lp.rows([(z,-decoded),(e,-eye)],-F.ravel())
        total=.5*sparse.kron(sparse.eye(Q),np.ones((1,Y)),format='csr')
        lp.rows([(e,total),(d,-np.ones((Q,1)))],np.zeros(Q))
    Ae,Au=lp.matrix(True),lp.matrix(False)
    built=time.perf_counter()-started
    sol,report=solve_arrays(lp.cost,Ae,lp.be,Au,lp.bu,[(0,1)]*len(lp.cost),method,time_limit)
    if certificate_path is not None:
        arrays=dict(cost=np.asarray(lp.cost),bounds=np.asarray([(0.,1.)]*len(lp.cost)),
                    solution=sol.x,objective=np.asarray(sol.fun),b_eq=np.asarray(lp.be),b_ub=np.asarray(lp.bu),
                    eq_dual=sol.eqlin.marginals,ub_dual=sol.ineqlin.marginals,
                    lower_dual=sol.lower.marginals,upper_dual=sol.upper.marginals)
        for key,matrix in [('A_eq',Ae),('A_ub',Au)]:
            arrays[key+'_shape']=np.asarray(matrix.shape)
            if compact_certificate:
                arrays[key+'_sha256']=np.asarray(hashlib.sha256(
                    matrix.data.tobytes()+matrix.indices.tobytes()+matrix.indptr.tobytes()).hexdigest())
            else:
                arrays.update({key+'_data':matrix.data,key+'_indices':matrix.indices,key+'_indptr':matrix.indptr})
        np.savez_compressed(certificate_path,**arrays)
        report['certificate_path']=str(certificate_path)
    E,rows,leaf=replay(g,sol.x[:P])
    if np.max(np.abs(leaf-sol.x[g.leaf_index]))>TOL:raise RuntimeError('Realization replay failed')
    report.update(build_seconds=built,nnz=Ae.nnz+Au.nnz,
                  matrix_bytes=sum(m.data.nbytes+m.indices.nbytes+m.indptr.nbytes for m in [Ae,Au]))
    return E,rows,leaf,report


class Decoder:
    """One dual LP returns its lower witness AND a primal stochastic decoder.

    The s variables are free, so their stationarity enforces decoder row sums1.
    Matrix depends only on E/output size; new target kernels change the cost.
    """
    def __init__(self,E,outputs,method='highs',time_limit=120):
        started=time.perf_counter();self.keep=np.flatnonzero(np.max(E,axis=0)>0)
        self.E=np.asarray(E[:,self.keep]);Q,X=self.E.shape;Y=outputs
        self.Q,self.X,self.Y=Q,X,Y;self.method=method;self.time_limit=time_limit
        V=Q+Q*Y+X;self.c=np.zeros(V);self.c[Q+Q*Y:]=1
        a=sparse.kron(sparse.eye(Q),-np.ones((Y,1)),format='csr')
        upper=sparse.hstack([a,sparse.eye(Q*Y),sparse.csr_matrix((Q*Y,X))],format='csr')
        coefficient=sparse.kron(sparse.csr_matrix(self.E.T),sparse.eye(Y),format='csr')
        s=-sparse.kron(sparse.eye(X),np.ones((Y,1)),format='csr')
        lower=sparse.hstack([sparse.csr_matrix((X*Y,Q)),coefficient,s],format='csr')
        self.Au=sparse.vstack([upper,lower],format='csr');self.bu=np.zeros(Q*Y+X*Y)
        self.Ae=sparse.csr_matrix(([1.]*Q,([0]*Q,list(range(Q)))),shape=(1,V));self.be=np.ones(1)
        self.bounds=[(0,None)]*(Q+Q*Y)+[(None,None)]*X
        self.build_seconds=time.perf_counter()-started

    def solve(self,F):
        if F.shape!=(self.Q,self.Y):raise ValueError('Wrong target shape')
        cost=self.c.copy();cost[self.Q:self.Q+self.Q*self.Y]=-F.ravel()
        sol,report=solve_arrays(cost,self.Ae,self.be,self.Au,self.bu,self.bounds,self.method,self.time_limit)
        G=-sol.ineqlin.marginals[self.Q*self.Y:].reshape(self.X,self.Y)
        raw_sum=float(np.max(np.abs(G.sum(axis=1)-1),initial=0));raw_neg=violation(-G)
        if max(raw_sum,raw_neg)>TOL:raise RuntimeError(f'Non-stochastic extracted decoder: {raw_sum}, {raw_neg}')
        # Normalize only after testing the raw KKT-derived decoder; report changes.
        G=np.maximum(G,0);G/=G.sum(axis=1,keepdims=True)
        upper=float(np.max(np.abs(self.E@G-F).sum(axis=1)/2))
        alpha=sol.x[:self.Q];b=sol.x[self.Q:self.Q+self.Q*self.Y].reshape(self.Q,self.Y)
        # Produce an explicitly feasible dual witness even with tiny solver residuals.
        alpha=np.maximum(alpha,0);alpha/=alpha.sum()
        b=np.minimum(np.maximum(b,0),alpha[:,None])
        lower=float(np.sum(F*b)-np.max(self.E.T@b,axis=1).sum())
        if abs(upper+sol.fun)>TOL or upper-lower>TOL or lower>upper+TOL:
            raise RuntimeError(f'Decoder bounds disagree: {lower}, {upper}, {-sol.fun}')
        report.update(lower=lower,upper=upper,raw_decoder_row_residual=raw_sum,
                      raw_decoder_negative=raw_neg,bracket=upper-lower)
        return report,dict(source_indices=self.keep,decoder=G,alpha=alpha,b=b)


def audit(E,targets,indices=None,method='highs',time_limit=120,progress=None,
          checkpoint_path=None,witness_path=None):
    indices=range(targets.count) if indices is None else list(indices)
    first=targets.get(0)['kernel']
    def make_decoder(outputs):
        if method.startswith('native'):
            from certified_decoder import StableDecoder
            return StableDecoder(E,outputs,method,min(120.,time_limit))
        return Decoder(E,outputs,method,min(120.,time_limit))
    decoder=make_decoder(first.shape[1])
    started=time.perf_counter();upper=[];lower=[];ids=[];solve_seconds=0.;max_residual=0.;fallbacks=[]
    source_hash=hashlib.sha256(np.ascontiguousarray(E).tobytes()).hexdigest()
    # Full revelation need not be native; it is used only as a valid audit upper bound.
    revelation_decoder=make_decoder(E.shape[0])
    revelation,revelation_witness=revelation_decoder.solve(np.eye(E.shape[0]))
    solve_seconds+=revelation['solve_seconds'];max_residual=max(revelation['residuals'].values())
    if revelation.get('fallback_used'):fallbacks.append(dict(target='full_revelation_control',attempts=revelation['attempts']))
    hardest_witness=None;hardest_upper=-1.;hardest_index=None
    def checkpoint():
        if checkpoint_path is not None:
            path=Path(checkpoint_path);temp=path.with_suffix('.tmp')
            with temp.open('wb') as handle:
                np.savez_compressed(handle,indices=ids,lower=lower,upper=upper,
                                    source_sha256=np.asarray(source_hash),target_horizon=np.asarray(targets.n),
                                    target_count=np.asarray(targets.count),
                                    full_revelation_upper=np.asarray(revelation['upper']))
            temp.replace(path)
        if witness_path is not None and hardest_witness is not None:
            path=Path(witness_path);temp=path.with_suffix('.tmp')
            arrays={**hardest_witness,'target_index':np.asarray(hardest_index),
                    'source_sha256':np.asarray(source_hash),'target_kernel':targets.get(hardest_index)['kernel']}
            arrays.update({'revelation_'+k:v for k,v in revelation_witness.items()})
            with temp.open('wb') as handle:np.savez_compressed(handle,**arrays)
            temp.replace(path)
    for j in indices:
        result,witness=decoder.solve(targets.get(j)['kernel'])
        ids.append(j);upper.append(result['upper']);lower.append(result['lower'])
        if result.get('fallback_used'):fallbacks.append(dict(target=j,attempts=result['attempts']))
        solve_seconds+=result['solve_seconds'];max_residual=max(max_residual,max(result['residuals'].values()))
        if result['upper']>hardest_upper:
            hardest_upper=result['upper'];hardest_index=j;hardest_witness=witness
        if len(ids)%128==0:
            checkpoint()
            if progress:progress(len(ids),time.perf_counter()-started)
    if not ids:raise ValueError('At least one target is required')
    checkpoint()
    if max(lower)>revelation['upper']+2*TOL:raise RuntimeError('Native audit exceeds full-revelation upper bound')
    complete=len(ids)==targets.count and len(set(ids))==targets.count
    return dict(lower=max(lower),upper=max(upper),global_upper=max(upper) if complete else revelation['upper'],
                full_revelation_upper=revelation['upper'],full_revelation_report=revelation,
                bound_scope='full_target_class' if complete else 'evaluated_targets_only',
                backend=method,fallbacks=fallbacks,hardest_target=hardest_index,
                source_coarsening=dict(merged_columns=getattr(decoder,'merged_columns',0),worldwise_mass_bound=getattr(decoder,'coarsening_bound',0.),original_source_bounds=True),
                lp_residual_scope='KKT of the numerical coarsened LP; decoder and dual bounds checked on original source',
                model_imports=getattr(decoder,'import_reports',[]),
                target_indices=ids,lower_values=lower,upper_values=upper,
                exhaustive=complete,target_count=targets.count,evaluated=len(ids),
                seconds=time.perf_counter()-started,solve_seconds=solve_seconds,
                decoder_build_seconds=decoder.build_seconds+revelation_decoder.build_seconds,max_lp_residual=max_residual)


def minimax_plan(g,targets,method='highs',time_limit=120,gap=2e-7,max_iterations=32,decoder_method='highs-ds'):
    active=targets.fixed_indices();iterations=[]
    for k in range(max_iterations):
        E,rows,leaf,plan=native_plan(g,[targets.get(j) for j in active],'native_minimax',method,time_limit)
        evaluated=audit(E,targets,method=decoder_method,time_limit=min(120.,time_limit))
        separation_gap=evaluated['upper']-plan['dual']
        iterations.append(dict(active=active.copy(),plan=plan,audit_seconds=evaluated['seconds'],
                               lower=plan['dual'],upper=evaluated['upper'],gap=separation_gap))
        if separation_gap<=gap:
            return E,rows,leaf,dict(iterations=iterations,audit=evaluated,optimization_gap=separation_gap)
        order=np.argsort(-np.array(evaluated['upper_values']))
        add=[int(j) for j in order if j not in active and evaluated['upper_values'][j]>plan['dual']+gap][:4]
        if not add:raise RuntimeError('Nonclosing minimax numerical gap')
        active.extend(add)
    raise RuntimeError('Minimax iteration cap, no optimum claimed')
