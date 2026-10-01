#!/usr/bin/env python3
"""Finite-policy constraint generation for the Bellman-optimal shared decoder."""
from pathlib import Path
from fractions import Fraction as Q
import json,hashlib,time,argparse
import numpy as np
from scipy.optimize import linprog
from bellman_bound import exact_model,target,exact_upper,Constraints,EDGES
HERE=Path(__file__).resolve().parent

def main(args):
    start=time.monotonic();levels,p,values,actions,reached=exact_model();T,labels=target(Q(1,10))
    leaf=reached[-1];li={h:i for i,h in enumerate(leaf)};nodes=[h for layer in reached[:-1] for h in layer]
    Y=len(labels);nv=len(leaf)*Y+1;delta=nv-1
    pp=np.array([p[h] for h in leaf],float).T;tt=np.array(T,float)
    eq=Constraints();ub=Constraints();seen=set();records=[]
    for i in range(len(leaf)):eq.add([(i*Y+z,1) for z in range(Y)],1)
    def add(theta,mask,indices):
        key=(theta,mask,tuple(indices))
        if key in seen:return False
        seen.add(key)
        ub.add([(k*Y+z,pp[theta,k]) for k in indices for z in range(Y) if mask>>z&1]+[(delta,-1)],sum(tt[theta,z] for z in range(Y) if mask>>z&1))
        return True
    # Fixed RRRL is in the permitted family and supplies the sharp lower witness.
    rr=[]
    def fixed(h):
        if len(h)==4:rr.append(li[h]);return
        a=(1,1,1,0)[len(h)]
        assert a in actions[h]
        for aa,o in EDGES:
            if aa==a:fixed(h+((aa,o),))
    fixed(())
    for theta in range(4):
        for mask in range(1<<Y):add(theta,mask,sorted(rr))
    def separate(dec):
        cuts=[];worst=-1.;details=[]
        for theta in range(4):
            for mask in range(1<<Y):
                v={h:pp[theta,k]*sum(dec[k,z] for z in range(Y) if mask>>z&1) for k,h in enumerate(leaf)};chosen={}
                for layer in reversed(reached[:-1]):
                    for h in layer:
                        pairs=[(sum(v[h+((aa,o),)] for aa,o in EDGES if aa==a),a) for a in actions[h]]
                        score,a=max(pairs);v[h]=score;chosen[h]=a
                value=v[()]-sum(tt[theta,z] for z in range(Y) if mask>>z&1);worst=max(worst,value)
                selected=[]
                def walk(h):
                    if h in li:selected.append(li[h]);return
                    for aa,o in EDGES:
                        if aa==chosen[h]:walk(h+((aa,o),))
                walk(())
                cuts.append((value,theta,mask,sorted(selected)))
        return worst,cuts
    c=np.zeros(nv);c[-1]=1
    for iteration in range(args.iterations):
        sol=linprog(c,A_ub=ub.matrix(nv),b_ub=ub.rhs,A_eq=eq.matrix(nv),b_eq=eq.rhs,bounds=(0,1),method='highs-ds',options={'dual_feasibility_tolerance':1e-9,'primal_feasibility_tolerance':1e-9})
        if not sol.success:raise RuntimeError(sol.message)
        dec=sol.x[:-1].reshape(-1,Y)
        upper,cuts=separate(dec);added=0
        for value,theta,mask,selected in cuts:
            if value>sol.fun+args.tolerance:addition=add(theta,mask,selected);added+=addition
        row=dict(iteration=iteration,master_value=float(sol.fun),separation_upper=float(upper),cuts=len(seen),added=added,elapsed_seconds=time.monotonic()-start);records.append(row);print(json.dumps(row),flush=True)
        if upper<=sol.fun+args.tolerance:break
        if added==0:raise RuntimeError('Unresolved violation but no new policy cuts')
    decoder=[]
    for row in dec:
        q=[Q(max(0.,x)).limit_denominator(args.denominator) for x in row];j=max(range(Y),key=lambda j:q[j]);q[j]=1-sum(v for k,v in enumerate(q) if k!=j)
        assert min(q)>=0 and sum(q)==1;decoder.append(q)
    bound,checks=exact_upper(decoder,reached,actions,p,T)
    out=dict(status='passed_exact_feasibility',scope='Rational shared-decoder upper over every exactly Bellman-optimal policy; master value is a numerical lower bound for the shared-decoder problem only.',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),dependency_sha256=hashlib.sha256((HERE/'bellman_bound.py').read_bytes()).hexdigest(),protocol_sha256=hashlib.sha256((HERE/'PROTOCOL.md').read_bytes()).hexdigest(),noise='1/10',horizon=4,root_value=str(values[()]),reachable_sizes=list(map(len,reached)),iterations=records,master_value=sol.fun,exact_upper=str(bound),exact_upper_float=float(bound),decoder=[[str(v) for v in row] for row in decoder],terminal_histories=[[[a,o] for a,o in h] for h in leaf],target_labels=labels,target_rows=[[str(v) for v in row] for row in T],event_checks=checks,elapsed_seconds=time.monotonic()-start)
    (HERE/args.output).write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('decoder','terminal_histories','target_rows','event_checks','iterations')}))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--iterations',type=int,default=100);ap.add_argument('--tolerance',type=float,default=1e-9);ap.add_argument('--denominator',type=int,default=10**8);ap.add_argument('--output',default='cutting_decoder.json')
    main(ap.parse_args())
