#!/usr/bin/env python3
"""Common count-state decoder, separated over the actual native optimum face.

The cutting-plane master is only a numerical lower bound for this *shared
decoder* problem. Separation supplies a numerical upper; a separate rational
dual audit is required before asserting a rigorous all-policy bound.
"""
from pathlib import Path
from fractions import Fraction as Q
import argparse
import hashlib
import json
import time
import numpy as np
from scipy.optimize import linprog
from compressed_oracle import CompressedPolicyOracle, SEARCH
from bellman_bound import Constraints

HERE=Path(__file__).resolve().parent

def main(args):
    start=time.monotonic(); oracle=CompressedPolicyOracle()
    S=len(oracle.states); T=oracle.target_kernels['adaptive_L']; Y=T.shape[1]
    nv=S*Y+1; d=nv-1; eq=Constraints(); ub=Constraints(); seen=set()
    for s in range(S):eq.add([(s*Y+y,1) for y in range(Y)],1)
    def add(theta,mask,E):
        key=(theta,mask,tuple(np.round(E[theta],13)))
        if key in seen:return False
        seen.add(key)
        ub.add([(s*Y+y,E[theta,s]) for s in range(S) for y in range(Y) if mask>>y&1]+[(d,-1)],sum(T[theta,y] for y in range(Y) if mask>>y&1))
        return True
    saved=np.load(HERE/'shared_decoder_diagnostic.npz')['source_kernels']
    for full in saved:
        E=np.stack([full[:,oracle.history_state==s].sum(axis=1) for s in range(S)],axis=1)
        for theta in range(4):
            for mask in range(1,(1<<Y)-1):add(theta,mask,E)
    c=np.zeros(nv);c[-1]=1; records=[]; witnesses=[]
    for iteration in range(args.iterations):
        sol=linprog(c,A_ub=ub.matrix(nv),b_ub=ub.rhs,A_eq=eq.matrix(nv),b_eq=eq.rhs,bounds=(0,1),method=SEARCH.METHOD,options=SEARCH.OPTIONS)
        if not sol.success:raise RuntimeError(sol.message)
        G=sol.x[:-1].reshape(S,Y); upper=0.; added=0; event_bounds=[]
        for theta in range(4):
            for mask in range(1,(1<<Y)-1):
                cols=[y for y in range(Y) if mask>>y&1]
                coeff=oracle.rays[theta]*G[:,cols].sum(axis=1)
                got=oracle.optimize(coeff)
                val=got['dual_upper_bound']-T[theta,cols].sum()
                event_bounds.append([theta,mask,val]);upper=max(upper,val)
                if val>sol.fun+args.tolerance:
                    added+=add(theta,mask,got['source_kernel'])
                    witnesses.append({'iteration':iteration,'theta':theta,'mask':mask,'state_weights':got['state_weights'].tolist(),'separation_value':val})
        row=dict(iteration=iteration,master_value=float(sol.fun),separation_upper=float(upper),added=added,cuts=len(seen),oracle_calls=oracle.calls,elapsed_seconds=time.monotonic()-start)
        records.append(row);print(json.dumps(row),flush=True)
        np.savez_compressed(HERE/'native_count_checkpoint.npz',decoder=G,event_bounds=np.asarray(event_bounds),target=T,states=np.asarray(oracle.states),rays=oracle.rays)
        SEARCH.write_json(HERE/'native_count_progress.json',{'scope':'Numerical common decoder on actual native optimum face; not yet an exact certificate.','iterations':records,'witnesses':witnesses})
        if upper<=sol.fun+args.tolerance:break
        if added==0:raise RuntimeError('Unresolved violation without a new cut')
    rational=[]
    for row in G:
        vals=[Q(max(0.,v)).limit_denominator(args.denominator) for v in row]
        j=max(range(Y),key=lambda y:vals[y]); vals[j]=1-sum(v for y,v in enumerate(vals) if y!=j)
        assert min(vals)>=0 and sum(vals)==1
        rational.append(vals)
    out=dict(status='completed_float64_common_decoder',scope='Common signed-count decoder over every exact native-repeat objective optimizer; no minimax exchange and no claim of sharpness without exact audit.',source_sha256=SEARCH.digest(__file__),oracle_sha256=SEARCH.digest(HERE/'compressed_oracle.py'),protocol_sha256=SEARCH.digest(HERE/'PROTOCOL.md'),noise='1/10',horizon=4,native_cost_bound='9/1250',states=oracle.states,decoder=[[str(v) for v in row] for row in rational],float_decoder=G.tolist(),target_rows=[[str(v) for v in row] for row in oracle.targets['adaptive_L']['exact']],iterations=records,numerical_upper=upper,numerical_master_value=float(sol.fun),elapsed_seconds=time.monotonic()-start)
    SEARCH.write_json(HERE/'native_count_decoder.json',out)
    print(json.dumps({k:v for k,v in out.items() if k not in ('states','decoder','float_decoder','target_rows','iterations')}),flush=True)

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--iterations',type=int,default=100);parser.add_argument('--tolerance',type=float,default=1e-9);parser.add_argument('--denominator',type=int,default=10**6)
    main(parser.parse_args())
