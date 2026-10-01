#!/usr/bin/env python3
"""Independent arithmetic replay of saved decomposition cuts and certificates.

No planner, decoder, or copied core imports; no optimization performed.
"""
import argparse
import hashlib
import resource
import time
import itertools
import json
import os
from pathlib import Path
import numpy as np
from scipy import sparse

HERE=Path(__file__).resolve().parent
OLD=HERE.parents[1]/'native_objective_benchmark_2026-09-15/results'
TOL=2e-7

def norm(v):return float(np.max(np.abs(v),initial=0))
def pos(v):return float(np.max(np.maximum(v,0),initial=0))
def matrix(z,key):return sparse.csr_matrix((z[key+'_data'],z[key+'_indices'],z[key+'_indptr']),shape=z[key+'_shape'])
def histories(t):return [list(itertools.product(itertools.product(range(2),repeat=2),repeat=d)) for d in range(t+1)]
def law(T,Z,h):
    values=[]
    for q in range(len(T)):
        state=np.zeros(T.shape[-1]);state[0]=1.
        for a,o in h:state=(state@T[q,a])*Z[q,a,:,o]
        values.append(state.sum())
    return np.asarray(values)
def target(T,Z,n,index):
    bits=[(index>>k)&1 for k in range(2**n-2,-1,-1)]
    columns=[]
    for obs in itertools.product(range(2),repeat=n):
        h=[];node=0
        for o in obs:
            h.append((bits[node],o));node=node*2+1+o
        columns.append(law(T,Z,h))
    return np.stack(columns,axis=1)
def replay(rows,layers):
    decisions=sum(layers[:-1],[]);di={h:i for i,h in enumerate(decisions)}
    w={():1.};action=np.zeros(2*len(decisions))
    for h in decisions:
        for a in range(2):
            value=w[h]*rows[di[h],a];action[2*di[h]+a]=value
            for o in range(2):w[h+((a,o),)]=value
    return action,np.array([w[h] for h in layers[-1]])
def lp_certificate(path):
    z=np.load(path);c=z['cost'];x=z['solution'];Ae=matrix(z,'A_eq');Au=matrix(z,'A_ub')
    be=z['b_eq'];bu=z['b_ub'];ye=z['eq_dual'];yu=z['ub_dual'];yl=z['lower_dual'];yh=z['upper_dual']
    arrays=[c,x,Ae.data,Au.data,be,bu,ye,yu,yl,yh]
    if not all(np.isfinite(v).all() for v in arrays):raise ValueError('Nonfinite LP certificate')
    residual=max(norm(Ae@x-be),pos(Au@x-bu),pos(-x),pos(x-1),pos(yu),pos(-yl),pos(yh),norm(c-Ae.T@ye-Au.T@yu-yl-yh))
    repaired_yu=np.minimum(yu,0);remaining=c-Ae.T@ye-Au.T@repaired_yu
    lower=float(be@ye+bu@repaired_yu+np.minimum(remaining,0).sum());upper=float(c@x)
    residual=max(residual,abs(upper-lower))
    if residual>TOL:raise ValueError(f'LP failed {path}: {residual}')
    return dict(lower=lower,upper=upper,residual=residual,variables=len(c),rows=Ae.shape[0]+Au.shape[0]),z

def audit_cell(folder):
    r=json.loads((folder/'comparison.json').read_text());z=np.load(folder/'decomposition.npz')
    model=np.load(OLD/r['case']/'model.npz');T,Z=model['T'],model['Z'];layers=histories(r['t'])
    raw=np.stack([law(T,Z,h) for h in layers[-1]],axis=1)
    Fs=np.stack([target(T,Z,r['n'],j) for j in r['target_indices']])
    residual=max(norm(raw-z['raw']),norm(Fs-z['target_kernels']))
    decisions=sum(layers[:-1],[]);di={h:i for i,h in enumerate(decisions)}
    leaf_index=np.asarray([2*di[h[:-1]]+h[-1][0] for h in layers[-1]])
    if not np.array_equal(leaf_index,z['leaf_index']):raise ValueError('Leaf map differs')
    P=2*len(decisions)
    for j,(idx,c,s,a,b) in enumerate(zip(z['cut_targets'],z['cut_intercepts'],z['cut_slopes'],z['cut_alpha'],z['cut_b'])):
        if not all(np.isfinite(v).all() for v in [s,a,b]):raise ValueError('Nonfinite cut')
        residual=max(residual,abs(a.sum()-1),pos(-a),pos(-b),pos(b-a[:,None]))
        expected_s=np.zeros(P)
        for h in range(raw.shape[1]):expected_s[leaf_index[h]]+=max(raw[:,h]@b)
        residual=max(residual,abs(c-np.sum(Fs[idx]*b)),norm(s-expected_s))
        # Reuse the witness on a deterministic collector unrelated to the iterate.
        alternate=np.zeros((len(decisions),2));alternate[:,1]=1
        aw,wl=replay(alternate,layers)
        residual=max(residual,abs((c-s@aw)-(np.sum(Fs[idx]*b)-np.max((raw*wl).T@b,axis=1).sum())))
    source_a,source_w=replay(z['rows'],layers);E=raw*source_w
    residual=max(residual,norm(E-z['E']),norm(source_w-z['leaf']),norm(E.sum(1)-1),norm(z['rows'].sum(1)-1),pos(-z['rows']))
    uppers=[];lowers=[]
    for j,F in enumerate(Fs):
        keep=z[f'witness_{j}_source_indices'];G=z[f'witness_{j}_decoder'];a=z[f'witness_{j}_alpha'];b=z[f'witness_{j}_b']
        expected_keep=np.flatnonzero(np.max(E,axis=0)>0)
        if not np.array_equal(keep,expected_keep):raise ValueError('Source omission differs')
        residual=max(residual,norm(G.sum(1)-1),pos(-G),abs(a.sum()-1),pos(-a),pos(-b),pos(b-a[:,None]))
        upper=float(np.max(np.abs(E[:,keep]@G-F).sum(1)/2))
        lower=float(np.sum(F*b)-np.max(E[:,keep].T@b,axis=1).sum())
        residual=max(residual,abs(upper-z['target_upper'][j]),abs(lower-z['target_lower'][j]),abs(upper-lower))
        uppers.append(upper);lowers.append(lower)
    master,m=lp_certificate(folder/'master_certificate.npz')
    # Bind the saved master to the cut prefix, objective, and full source-flow law.
    D=1 if r['kind']=='native_minimax' else len(Fs);cost=np.r_[np.zeros(P),np.ones(1) if D==1 else z['target_weights']]
    residual=max(residual,norm(cost-m['cost']))
    Ae=matrix(m,'A_eq').toarray();expected_Ae=np.zeros_like(Ae);be=np.zeros(len(decisions));be[0]=1
    for i,h in enumerate(decisions):
        expected_Ae[i,2*i:2*i+2]=1
        if h:expected_Ae[i,2*di[h[:-1]]+h[-1][0]]=-1
    residual=max(residual,norm(Ae-expected_Ae),norm(be-m['b_eq']))
    Au=matrix(m,'A_ub').toarray();expected_Au=np.zeros_like(Au)
    for j in range(len(m['b_ub'])):
        expected_Au[j,:P]=-z['cut_slopes'][j]
        expected_Au[j,P+(0 if D==1 else z['cut_targets'][j])]=-1
    residual=max(residual,norm(Au-expected_Au),norm(m['b_ub']+z['cut_intercepts'][:len(m['b_ub'])]))
    upper=max(uppers) if r['kind']=='native_minimax' else float(z['target_weights']@uppers)
    gap=upper-master['lower']
    residual=max(residual,abs(upper-r['decomposition']['upper']),abs(master['lower']-r['decomposition']['lower']))
    if r['decomposition']['status']=='converged' and gap>TOL:raise ValueError('Unclosed certified gap')
    result=dict(case=r['case'],t=r['t'],n=r['n'],K=r['K'],kind=r['kind'],status='passed',residual=residual,
                upper=upper,lower=master['lower'],gap=gap,cuts=len(z['cut_targets']),master=master)
    if (folder/'monolithic_certificate.npz').exists():
        mono,_=lp_certificate(folder/'monolithic_certificate.npz');result['monolithic']=mono
        if mono['lower']>upper+TOL or master['lower']>mono['upper']+TOL:raise ValueError('Planner intervals disjoint')
    if residual>TOL:raise ValueError(f'Replay residual {residual}')
    return result

def main():
    started=time.perf_counter()
    resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
    available=sorted(os.sched_getaffinity(0));os.sched_setaffinity(0,{available[min(1,len(available)-1)]})
    parser=argparse.ArgumentParser();parser.add_argument('directory',type=Path);args=parser.parse_args()
    results=[]
    for path in sorted(args.directory.glob('*/comparison.json')):
        try:results.append(audit_cell(path.parent))
        except Exception as exc:results.append(dict(path=str(path),status='failed',error=repr(exc)))
    output=dict(status='passed' if results and all(r['status']=='passed' for r in results) else 'failed',cells=results,
                tolerance=TOL,scope='Independent saved arithmetic replay; floating-point certificates, no solver reruns')
    output.update(seconds=time.perf_counter()-started,peak_rss_mib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024,
                  source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),cpu_affinity=sorted(os.sched_getaffinity(0)),address_space_limit_gib=2)
    (args.directory/'audit.json').write_text(json.dumps(output,indent=2,allow_nan=False)+'\n')
    print(json.dumps(output,indent=2))
    if output['status']!='passed':raise SystemExit(1)
if __name__=='__main__':main()
