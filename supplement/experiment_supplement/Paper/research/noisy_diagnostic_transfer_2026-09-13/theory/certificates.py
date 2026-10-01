#!/usr/bin/env python3
"""Exact-feasible affine noisy-diagnostic transfer certificates.

LP search uses float64. Output decoder, intercept, slope, and every vertex
verification use Fraction. Thus saved feasibility is exact; LP optimality is
not claimed without a separate dual certificate. Only two binary diagnostics
are implemented; the theorem in theory.tex is more general.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
from itertools import combinations, product
import json
from pathlib import Path
import numpy as np
from scipy.optimize import linprog

BITS=list(product((0,1), repeat=2))

def solve_square(a,b):
    n=len(b); aug=[[Q(x) for x in row]+[Q(v)] for row,v in zip(a,b)]
    for j in range(n):
        pivot=next((i for i in range(j,n) if aug[i][j]),None)
        if pivot is None: return None
        aug[j],aug[pivot]=aug[pivot],aug[j]
        z=aug[j][j]; aug[j]=[v/z for v in aug[j]]
        for i in range(n):
            if i!=j:
                z=aug[i][j]; aug[i]=[x-z*y for x,y in zip(aug[i],aug[j])]
    return tuple(row[-1] for row in aug)

def diagnostic_vertices(eps):
    """All vertices of the four marginal-sign cells in the four-simplex."""
    ml=(0,0,1,1); mr=(0,1,0,1); out=set()
    for signs in product((-1,1),repeat=2):
        rows=[]; rhs=[]
        for i in range(4):
            rows.append(tuple(-int(j==i) for j in range(4))); rhs.append(Q(0))
        for sign,m,e in zip(signs,(ml,mr),eps):
            rows.append(tuple(-sign*x for x in m)); rhs.append(-sign*e)
        for active in combinations(range(6),3):
            p=solve_square([(1,1,1,1)]+[rows[i] for i in active],[1]+[rhs[i] for i in active])
            if p is not None and all(sum(x*y for x,y in zip(row,p))<=b for row,b in zip(rows,rhs)):
                out.add(p)
    return sorted(out)

def target_rows(eps, word):
    ys=list(product((0,1),repeat=3 if word=='adaptive' else len(word))); rows=[]
    for theta in BITS:
        row=[]
        for y in ys:
            v=Q(1)
            actions=('LLL' if y[0]==0 else 'LRR') if word=='adaptive' else word
            for a,o in zip(actions,y):
                i=0 if a=='L' else 1
                v*=1-eps[i] if o==theta[i] else eps[i]
            row.append(v)
        rows.append(row)
    return rows

def translated(p,theta):
    return tuple(p[((u^theta[0])<<1)+(v^theta[1])] for u,v in BITS)

def marginal_cost(p,eps,w):
    return w[0]*abs(p[2]+p[3]-eps[0])+w[1]*abs(p[1]+p[3]-eps[1])

def tv(p,q): return sum(abs(a-b) for a,b in zip(p,q))/2

def certificate(eps,word,s,w=(Q(1,2),Q(1,2)),target_eps=None,diagnostic_source='singles'):
    eps=tuple(map(Q,eps)); s=Q(s); w=tuple(map(Q,w))
    target_eps=eps if target_eps is None else tuple(map(Q,target_eps))
    vertices=diagnostic_vertices(eps); targets=target_rows(target_eps,word); m=len(targets[0])
    pairs=[(translated(p,th),targets[i],marginal_cost(p,eps,w)) for i,th in enumerate(BITS) for p in vertices]
    di=4*m; bi=di; ki=di+1; zi=di+2; nv=zi+len(pairs)*m
    c=np.zeros(nv); c[bi]=1; c[ki]=float(s)
    ae=[]; be=[]
    for y in range(4):
        row=np.zeros(nv); row[y*m:(y+1)*m]=1; ae.append(row); be.append(1)
    au=[]; bu=[]
    for k,(p,t,cost) in enumerate(pairs):
        for z in range(m):
            row=np.zeros(nv)
            for y in range(4): row[y*m+z]=float(p[y])
            row[zi+k*m+z]=-1; au.append(row); bu.append(float(t[z]))
            row=np.zeros(nv)
            for y in range(4): row[y*m+z]=-float(p[y])
            row[zi+k*m+z]=-1; au.append(row); bu.append(-float(t[z]))
        row=np.zeros(nv); row[zi+k*m:zi+(k+1)*m]=1; row[bi]=-2; row[ki]=-2*float(cost)
        au.append(row); bu.append(0)
    sol=linprog(c,A_ub=np.asarray(au),b_ub=np.asarray(bu),A_eq=np.asarray(ae),b_eq=np.asarray(be),bounds=(0,None),method='highs')
    if not sol.success: raise RuntimeError(sol.message)
    dec=[]
    for y in range(4):
        vals=[Q(max(0,float(v))).limit_denominator(10**9) for v in sol.x[y*m:(y+1)*m]]
        j=max(range(m),key=lambda j:vals[j]); vals[j]=1-sum(v for i,v in enumerate(vals) if i!=j)
        assert all(v>=0 for v in vals) and sum(vals)==1
        dec.append(vals)
    slope=Q(max(0,float(sol.x[ki]))).limit_denominator(10**9)
    intercept=Q(0); worst=[]
    for p,t,cost in pairs:
        decoded=[sum(p[y]*dec[y][z] for y in range(4)) for z in range(m)]
        residual=tv(decoded,t)-slope*cost
        if residual>intercept: intercept=residual; worst=[(p,cost)]
        elif residual==intercept: worst.append((p,cost))
    assert all(tv([sum(p[y]*dec[y][z] for y in range(4)) for z in range(m)],t)<=intercept+slope*cost for p,t,cost in pairs)
    return dict(eps=list(map(str,target_eps)),diagnostic_eps=list(map(str,eps)),diagnostic_source=diagnostic_source,word=word,weights=list(map(str,w)),at_loss=str(s),intercept=str(intercept),slope=str(slope),bound=str(intercept+slope*s),bound_float=float(intercept+slope*s),lp_lower_candidate=float(sol.fun),search_to_exact_gap=float(intercept+slope*s)-float(sol.fun),decoder=[[str(v) for v in row] for row in dec],canonical_cell_vertices=len(vertices),exact_vertex_checks=len(pairs),all_exact_checks_pass=True)

def source_deficiency(e,t):
    """Independent plain finite stochastic decoder LP, numerical control only."""
    e=np.asarray(e,float); t=np.asarray(t,float); n,x=e.shape; y=t.shape[1]
    z0=x*y; eta=z0+n*y; nv=eta+1; c=np.zeros(nv); c[eta]=1
    ae=[]; be=[]
    for k in range(x):
        row=np.zeros(nv); row[k*y:(k+1)*y]=1; ae.append(row);be.append(1)
    au=[];bu=[]
    for q in range(n):
        for j in range(y):
            row=np.zeros(nv);row[np.arange(x)*y+j]=e[q];row[z0+q*y+j]=-1;au.append(row);bu.append(t[q,j])
            row=np.zeros(nv);row[np.arange(x)*y+j]=-e[q];row[z0+q*y+j]=-1;au.append(row);bu.append(-t[q,j])
        row=np.zeros(nv);row[z0+q*y:z0+(q+1)*y]=1;row[eta]=-2;au.append(row);bu.append(0)
    sol=linprog(c,A_ub=np.asarray(au),b_ub=np.asarray(bu),A_eq=np.asarray(ae),b_eq=np.asarray(be),bounds=(0,None),method='highs')
    assert sol.success
    return sol.fun

def analytic_controls():
    out=[]
    for e in (Q(1,10),Q(1,4),Q(3,10),Q(2,5)):
        c=1-2*e; src=[]
        for th in BITS:
            row=[Q(0)]*4;row[2*th[0]+th[1]]=1-e;row[2*(1-th[0])+1-th[1]]=e;src.append(row)
        target=target_rows((e,e),'LR'); formula=e*(1-e)*(1-2*e); got=source_deficiency(src,target)
        assert abs(got-float(formula))<1e-10
        cert=certificate((e,e),'LR',Q(0)); expected=e*c if e<=Q(1,3) else (c+c*c)/4
        assert abs(cert['bound_float']-float(expected))<1e-10
        a1=1-e; a3=1-3*e*e+2*e**3; b=2*e*(1-e)
        marginal=(1-b)*(a3+a1)/2+b*(a3+Q(1,2))/2
        joint=(1-b)*a3*a1+b*a3/2
        assert marginal==a1 and a1*a1-joint==(a3-a1)**2
        out.append(dict(eps=str(e),correlated_deficiency=str(formula),independent_lp=got,robust_zero_floor=str(expected),h4_marginal_accuracy=str(marginal),h4_joint_accuracy=str(joint),h4_joint_guessing_gap=str((a3-a1)**2),h4_joint_deficiency_exact=str(2*(a3-a1)**2)))
    return out

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=Path(__file__).with_name('certificates.json'));args=ap.parse_args()
    data=[]
    for eps in ((Q(1,10),Q(1,10)),(Q(1,4),Q(1,4)),(Q(1,10),Q(3,10))):
        for source in ('singles','majority3'):
            diagnostic_eps=eps if source=='singles' else tuple(3*e*e-2*e**3 for e in eps)
            for word in ('LR','LLR','LRR','LLL','RRR','adaptive'):
                for s in (Q(0),Q(1,1000),Q(1,100),Q(1,20),Q(1,10)):
                    data.append(certificate(diagnostic_eps,word,s,target_eps=eps,diagnostic_source=source))
    controls=analytic_controls()
    obj=dict(status='Exact feasible transfer certificates; float64 LP search, no LP-optimality certificate',certificates=data,controls=controls,exact_vertex_checks=sum(x['exact_vertex_checks'] for x in data),all_exact_checks_pass=True)
    args.output.write_text(json.dumps(obj,indent=2)+'\n')
    print(json.dumps(dict(certificates=len(data),exact_vertex_checks=obj['exact_vertex_checks'],controls=controls,output=str(args.output)),indent=2))
if __name__=='__main__':main()
