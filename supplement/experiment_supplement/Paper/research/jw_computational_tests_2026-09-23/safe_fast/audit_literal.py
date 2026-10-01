#!/usr/bin/env python3
"""Exact rational replay of literal full-record decoder LP witnesses."""
import concurrent.futures,gzip,json,os,time
from fractions import Fraction as Q
from pathlib import Path
BASE=Path(__file__).resolve().parent

def one(path):
    r=json.load(gzip.open(path,'rt'));w=r['literal_witness']
    try:
        E=[[Q(float(v)) for v in row] for row in w['E']];T=[[Q(float(v)) for v in row] for row in w['T']]
        W,X,Y=len(E),len(E[0]),len(T[0]);assert all(sum(row)==1 for row in E+T)
        G=[[max(Q(0),Q(float(v))) for v in row] for row in w['G']]
        G=[[v/sum(row) for v in row] for row in G]
        upper=max(sum(abs(sum(E[k][x]*G[x][y] for x in range(X))-T[k][y]) for y in range(Y))/2 for k in range(W))
        residual=[Q(0)]*(X*Y+W*Y)+[Q(1)];constant=Q(0)
        eq=[Q(float(v)) for v in w['dual_eq']];ub=[min(Q(0),Q(float(v))) for v in w['dual_ub']]
        for x,lam in enumerate(eq):
            constant+=lam
            for y in range(Y):residual[x*Y+y]-=lam
        row=0
        for k in range(W):
            for y in range(Y):
                for sign in (1,-1):
                    mu=ub[row];constant+=mu*sign*T[k][y]
                    for x in range(X):residual[x*Y+y]-=mu*sign*E[k][x]
                    residual[X*Y+k*Y+y]+=mu;row+=1
            mu=ub[row]
            for y in range(Y):residual[X*Y+k*Y+y]-=mu/2
            residual[-1]+=mu;row+=1
        lower=constant+sum(min(Q(0),v) for v in residual)
        assert lower<=upper
        cmp=Q(float(r['compressed']));tol=Q(1,10**8)
        assert lower-tol<=cmp<=upper+tol and upper-lower<=tol
        return {'index':r['index'],'status':'passed','lower':str(lower),'upper':str(upper),'gap':float(upper-lower)}
    except Exception as e:return {'index':r['index'],'status':'failed','error':repr(e)}
def init():
    import multiprocessing
    os.sched_setaffinity(0,{12+(multiprocessing.current_process()._identity[0]-1)%4})
def main():
    st=time.monotonic()
    with concurrent.futures.ProcessPoolExecutor(4,initializer=init) as p:rows=list(p.map(one,sorted((BASE/'crosscheck_witnesses').glob('*.json.gz')),chunksize=4))
    out={'status':'passed' if all(r['status']=='passed' for r in rows) else 'failed','cases':len(rows),'elapsed_seconds':time.monotonic()-st,'arithmetic':'exact rational decoder normalization, worldwise TV and full LP dual box correction','maximum_primal_dual_gap':max(r.get('gap',0) for r in rows),'rows':rows}
    (BASE/'LITERAL_AUDIT.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='rows'}))
if __name__=='__main__':main()
