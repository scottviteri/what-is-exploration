#!/usr/bin/env python3
"""Numerical common full-history decoder over the exact native optimal set.

The native LP retains policy-specific diagnostic decoders. Only the requested
adaptive target uses a common decoder. Exact rational event certificates are
produced separately; cutting-plane values alone do not certify sharpness.
"""
from pathlib import Path
from fractions import Fraction as Q
import argparse,json,time
import numpy as np
from scipy.optimize import linprog
from linear_native_oracle import TerminalPolicyOracle
from compressed_oracle import SEARCH
from bellman_bound import Constraints

HERE=Path(__file__).resolve().parent

def main(args):
    start=time.monotonic();oracle=TerminalPolicyOracle()
    leaf=oracle.terminal_histories; all_index={h:i for i,h in enumerate(oracle.histories)}
    retained=np.asarray([all_index[h] for h in leaf]); P=oracle.terminal_prefix_laws
    groups=[[0],[1],[2,4],[3],[5]]
    original=oracle.targets['adaptive_L']['exact']
    # Equal-noise likelihood rays: count column4 is twice column2.
    assert all(row[4]==2*row[2] for row in original)
    exactT=[[sum(row[j] for j in group) for group in groups] for row in original]
    S=len(leaf);T=np.asarray(exactT,float);Y=T.shape[1]
    nv=S*Y+1;d=nv-1;eq=Constraints();ub=Constraints();seen=set()
    for s in range(S):eq.add([(s*Y+y,1) for y in range(Y)],1)
    def add(theta,mask,E):
        key=(theta,mask,tuple(np.round(E[theta],13)))
        if key in seen:return False
        seen.add(key)
        ub.add([(s*Y+y,E[theta,s]) for s in range(S) for y in range(Y) if mask>>y&1 and E[theta,s]]+[(d,-1)],sum(T[theta,y] for y in range(Y) if mask>>y&1))
        return True
    for full in np.load(HERE/'shared_decoder_diagnostic.npz')['source_kernels']:
        E=full[:,retained]
        for theta in range(4):
            for mask in range(1,(1<<Y)-1):add(theta,mask,E)
    c=np.zeros(nv);c[-1]=1;records=[]
    for iteration in range(args.iterations):
        sol=linprog(c,A_ub=ub.matrix(nv),b_ub=ub.rhs,A_eq=eq.matrix(nv),b_eq=eq.rhs,bounds=(0,1),method=SEARCH.METHOD,options=SEARCH.OPTIONS)
        if not sol.success:raise RuntimeError(sol.message)
        G=sol.x[:-1].reshape(S,Y);upper=0.;added=0;event_bounds=[]
        for theta in range(4):
            for mask in range(1,(1<<Y)-1):
                cols=[y for y in range(Y) if mask>>y&1]
                got=oracle.optimize_terminal(P[theta]*G[:,cols].sum(axis=1),replay=False)
                val=got['dual_upper_bound']-T[theta,cols].sum();upper=max(upper,val)
                event_bounds.append([theta,mask,val])
                if val>sol.fun+args.tolerance:added+=add(theta,mask,got['reachable_source_kernel'])
        row=dict(iteration=iteration,master_value=float(sol.fun),separation_upper=float(upper),added=added,cuts=len(seen),oracle_calls=oracle.calls,elapsed_seconds=time.monotonic()-start)
        records.append(row);print(json.dumps(row),flush=True)
        np.savez_compressed(HERE/'native_history_checkpoint.npz',decoder=G,event_bounds=np.asarray(event_bounds),target=T,retained_indices=retained,prefix_laws=P)
        SEARCH.write_json(HERE/'native_history_progress.json',{'scope':'Numerical common full-history decoder on actual native optimum face; exact certification separate.','iterations':records})
        if upper<=sol.fun+args.tolerance:break
        if added==0:raise RuntimeError('Unresolved violation without a new cut')
    rational=[]
    for row in G:
        vals=[Q(max(0.,v)).limit_denominator(args.denominator) for v in row]
        j=max(range(Y),key=lambda y:vals[y]);vals[j]=1-sum(v for y,v in enumerate(vals) if y!=j)
        assert min(vals)>=0 and sum(vals)==1;rational.append(vals)
    SEARCH.write_json(HERE/'native_history_decoder.json',dict(status='completed_float64_common_decoder',scope='Common full-history decoder over every exact native-repeat objective optimizer; no claim of sharpness without exact audit.',source_sha256=SEARCH.digest(__file__),oracle_sha256=SEARCH.digest(HERE/'linear_native_oracle.py'),protocol_sha256=SEARCH.digest(HERE/'PROTOCOL.md'),noise='1/10',horizon=4,native_cost_bound='9/1250',terminal_histories=leaf,decoder=[[str(v) for v in row] for row in rational],float_decoder=G.tolist(),target_rows=[[str(v) for v in row] for row in exactT],target_count_groups=groups,iterations=records,numerical_upper=upper,numerical_master_value=float(sol.fun),elapsed_seconds=time.monotonic()-start))

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--iterations',type=int,default=100);parser.add_argument('--tolerance',type=float,default=1e-9);parser.add_argument('--denominator',type=int,default=10**6)
    main(parser.parse_args())
