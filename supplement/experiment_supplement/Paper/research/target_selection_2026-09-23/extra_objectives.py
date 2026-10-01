"""Literal finite-record scores; no policy population fitting or hidden features."""
import time
import numpy as np
import scaling_core as core
from objective_dp import terminal_scores,plan_terminal_rewards

ADDED=('prediction_error','pseudo_count','empirical_label_entropy','posterior_disagreement','tabular_rnd','specified_icm')


def entropy(p):
    p=np.asarray(p,dtype=float);positive=p>0
    return float(-np.sum(p[positive]*np.log2(p[positive])))


def fixed_history_scores(g,prior=None):
    Q=g.raw.shape[0];mu=np.full(Q,1/Q) if prior is None else np.asarray(prior,dtype=float)
    result=terminal_scores(g.layers,g.p,mu)
    labels=sorted({o for h in g.layers[1] for _,o in h});index={o:i for i,o in enumerate(labels)}
    if labels!=list(range(len(labels))):raise ValueError('These declared learner targets use consecutive integer labels')
    L=len(labels);state={(): (np.zeros(L,dtype=int),np.arange(L+1,dtype=float),np.zeros(len(ADDED)))}
    predictive={}
    for layer in g.layers[:-1]:
        for h in layer:
            mass=g.p[h];m=float(mu@mass)
            posterior=mu*mass/m if m>0 else np.zeros(Q)
            for action in [0,1]:
                responses=np.stack([np.divide(g.p[h+((action,o),)],mass,out=np.zeros(Q),where=mass>0) for o in labels],axis=1)
                q=posterior@responses
                variance=float(np.sum(posterior@(responses**2)-q**2))
                if variance < -1e-12:raise RuntimeError('Negative posterior variance')
                predictive[h,action]=(q,max(0.,variance))
                for o in labels:
                    counts,coordinates,total=state[h]
                    counts=counts.copy();coordinates=coordinates.copy();total=total.copy();j=index[o]
                    loss=float(q@q+1-2*q[j])
                    total[0]+=loss
                    total[1]+=1/np.sqrt(1+counts[j])
                    total[3]+=max(0.,variance)
                    total[4]+=(o+1)**2 if counts[j]==0 else 0
                    d=coordinates[0]-coordinates[j+1]
                    total[5]+=d*d
                    coordinates[0]-=d/4;coordinates[j+1]+=d/4
                    counts[j]+=1
                    total[2]=entropy(counts/counts.sum())
                    child=h+((action,o),);state[child]=(counts,coordinates,total)
    for i,name in enumerate(ADDED):
        values=np.array([state[h][2][i] for h in g.layers[-1]])
        values[mu@g.raw==0]=0
        if not np.all(np.isfinite(values)):raise RuntimeError('Nonfinite reward coefficients')
        result[name]=values
    return result


def occupancy_plan(g,prior=None):
    """Max H(prior-mean observed-label occupancy) on a binary label interface."""
    start=time.perf_counter();Q=g.raw.shape[0];mu=np.full(Q,1/Q) if prior is None else np.asarray(prior)
    if {o for h in g.layers[1] for _,o in h}!={0,1}:raise ValueError('Binary occupancy interval required')
    horizon=len(g.layers)-1
    frequency=np.array([sum(o==0 for _,o in h)/horizon for h in g.layers[-1]])
    low=plan_terminal_rewards(g.layers,g.p,-frequency,mu,tie_tolerance=0.)
    high=plan_terminal_rewards(g.layers,g.p,frequency,mu,tie_tolerance=0.)
    lower=-low['optimal_objective'];upper=high['optimal_objective']
    target=float(np.clip(.5,lower,upper))
    mix=(target-lower)/(upper-lower) if upper>lower else 0.
    n=len(g.decisions)
    x=(1-mix)*low['weights'][:n,None]*low['rows']+mix*high['weights'][:n,None]*high['rows']
    E,rows,leaf=core.replay(g,x.ravel())
    attained=float((mu@E)@frequency)
    residual=float(np.max(abs(E-((1-mix)*low['E']+mix*high['E']))))
    checks=dict(frequency_error=abs(attained-target),mixture_replay=residual,
                endpoint_dp=max([abs(v) for a in [low,high] for v in a['checks'].values()]))
    if not all(np.isfinite(v) and v<=core.TOL for v in checks.values()):raise RuntimeError('Occupancy certificate failed')
    plan=dict(method='binary_occupancy_interval',frequency_interval=[lower,upper],target_frequency=target,
              endpoint_mix=mix,optimal_objective=entropy([target,1-target]),
              objective=entropy([attained,1-attained]),checks=checks,seconds=time.perf_counter()-start,
              selection='mixture of minimum/maximum occupancy policies; each endpoint uniformly breaks exact float ties')
    return E,rows,leaf,plan
