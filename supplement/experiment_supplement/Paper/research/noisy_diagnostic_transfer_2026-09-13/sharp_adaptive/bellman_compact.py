#!/usr/bin/env python3
"""Search a common decoder over an exactly characterized Bellman-optimal family.

Exact rational decoding and DP certify an upper; LP optimality is numerical.
The family contains all native-repeat exact optima by the separate lower-bound
proof. A gap for this stronger shared-decoder problem is not a worst-policy gap.
"""
from pathlib import Path
from fractions import Fraction as Q
from itertools import product
import argparse,hashlib,json,time
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

HERE=Path(__file__).resolve().parent
WORLDS=tuple(product((0,1),repeat=2))
EDGES=((0,0),(0,1),(1,0),(1,1),(2,0))

def exact_model(e=Q(1,10),H=4):
    levels=[[()]]
    for _ in range(H):levels.append([h+(edge,) for h in levels[-1] for edge in EDGES])
    p={():tuple(Q(1) for _ in WORLDS)}
    for layer in levels[:-1]:
        for h in layer:
            for a,o in EDGES:p[h+((a,o),)]=tuple(v*(Q(1) if a==2 else 1-e if o==theta[a] else e) for v,theta in zip(p[h],WORLDS))
    def purpose(v):
        return (max(v[0]+v[1],v[2]+v[3])+max(v[0]+v[2],v[1]+v[3]))/4
    values={h:purpose(p[h]) for h in levels[-1]};actions={}
    for layer in reversed(levels[:-1]):
        for h in layer:
            vs=[sum(values[h+((aa,o),)] for aa,o in EDGES if aa==a) for a in range(3)]
            values[h]=max(vs);actions[h]=tuple(a for a in range(3) if vs[a]==values[h])
    reachable=[[()]]
    for _ in range(H):reachable.append([h+((a,o),) for h in reachable[-1] for a,o in EDGES if a in actions[h]])
    return levels,p,values,actions,reachable

def target(e):
    labels=list(product((0,1),range(3)));rows=[]
    for u,v in WORLDS:
        row=[]
        for first,k in labels:
            x=u if first==0 else v
            prob=e if x==0 else 1-e
            row.append((1-e if first==u else e)*Q((1,2,1)[k])*prob**k*(1-prob)**(2-k))
        assert sum(row)==1;rows.append(row)
    return rows,labels

class Constraints:
    def __init__(self):self.row=[];self.col=[];self.val=[];self.rhs=[]
    def add(self,entries,rhs=0):
        n=len(self.rhs)
        for j,v in entries:
            if v:self.row.append(n);self.col.append(j);self.val.append(float(v))
        self.rhs.append(float(rhs))
    def matrix(self,n):return coo_matrix((self.val,(self.row,self.col)),shape=(len(self.rhs),n)).tocsr()

def exact_upper(dec,reachable,actions,p,T):
    Y=len(T[0]);leaf=reachable[-1];worst=Q(0);checks=[]
    for theta in range(4):
        for mask in range(1<<Y):
            vals={h:p[h][theta]*sum(dec[k][z] for z in range(Y) if mask>>z&1) for k,h in enumerate(leaf)}
            for layer in reversed(reachable[:-1]):
                for h in layer:vals[h]=max(sum(vals[h+((aa,o),)] for aa,o in EDGES if aa==a) for a in actions[h])
            q=sum(T[theta][z] for z in range(Y) if mask>>z&1)
            bound=vals[()]-q;worst=max(worst,bound)
            checks.append(dict(world=theta,event=mask,source_max=str(vals[()]),target=str(q),gap=str(bound)))
    return worst,checks

def main(args):
    start=time.monotonic();e=Q(args.noise)
    levels,p,values,actions,reached=exact_model(e);T,labels=target(e)
    nodes=[h for layer in reached[:-1] for h in layer];index={h:i for i,h in enumerate(nodes)};leaf=reached[-1]
    Y=len(labels);N=len(nodes);gsize=len(leaf)*Y;error=gsize;offset=error+1
    n=offset+4*(1<<Y)*N
    c=np.zeros(n);c[error]=1
    eq=Constraints();ub=Constraints()
    for k in range(len(leaf)):eq.add([(k*Y+z,1) for z in range(Y)],1)
    for theta in range(4):
        for mask in range(1<<Y):
            base=offset+(theta*(1<<Y)+mask)*N
            leaf_index={h:k for k,h in enumerate(leaf)}
            for layer in reversed(reached[:-1]):
                for h in layer:
                    for a in actions[h]:
                        terms=[]
                        for aa,o in EDGES:
                            if aa!=a:continue
                            child=h+((aa,o),)
                            if child in leaf_index:
                                terms.extend((leaf_index[child]*Y+z,p[child][theta]) for z in range(Y) if mask>>z&1)
                            else:terms.append((base+index[child],1))
                        ub.add(terms+[(base+index[h],-1)])
            ub.add([(base+index[()],1),(error,-1)],sum(T[theta][z] for z in range(Y) if mask>>z&1))
    print(json.dumps(dict(reachable=[len(x) for x in reached],root_value=str(values[()]),variables=n,inequalities=len(ub.rhs))),flush=True)
    sol=linprog(c,A_ub=ub.matrix(n),b_ub=ub.rhs,A_eq=eq.matrix(n),b_eq=eq.rhs,bounds=(0,1),method='highs-ipm',options={'dual_feasibility_tolerance':1e-9,'primal_feasibility_tolerance':1e-9,'ipm_optimality_tolerance':1e-10})
    if not sol.success:raise RuntimeError(sol.message)
    decoder=[]
    for k in range(len(leaf)):
        row=[Q(max(0.,x)).limit_denominator(args.denominator) for x in sol.x[k*Y:(k+1)*Y]]
        j=max(range(Y),key=lambda j:row[j]);row[j]=1-sum(x for z,x in enumerate(row) if z!=j)
        assert min(row)>=0 and sum(row)==1;decoder.append(row)
    upper,checks=exact_upper(decoder,reached,actions,p,T)
    out=dict(status='passed_exact_feasibility',scope='Shared full-history decoder for all exactly Bellman-optimal policies; numerical search optimum is not a policy-deficiency extremum.',noise=str(e),horizon=4,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),protocol_sha256=hashlib.sha256((HERE/'PROTOCOL.md').read_bytes()).hexdigest(),root_value=str(values[()]),reachable_sizes=[len(x) for x in reached],variables=n,inequalities=len(ub.rhs),search_value=sol.fun,exact_upper=str(upper),exact_upper_float=float(upper),decoder=[[str(v) for v in row] for row in decoder],terminal_histories=[[[a,o] for a,o in h] for h in leaf],target_labels=labels,target_rows=[[str(v) for v in row] for row in T],event_checks=checks,elapsed_seconds=time.monotonic()-start)
    path=HERE/args.output;path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('decoder','terminal_histories','target_rows','event_checks')}))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--noise',default='1/10');ap.add_argument('--denominator',type=int,default=10**8);ap.add_argument('--output',default='bellman_compact_decoder.json')
    main(ap.parse_args())
