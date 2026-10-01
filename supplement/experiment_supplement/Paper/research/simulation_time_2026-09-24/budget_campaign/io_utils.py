"""Shared file IO and literal independent replay; no optimizer imports."""
import os
for _k in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):
    os.environ[_k]='1'
import hashlib,itertools,json,sys
from pathlib import Path
from datetime import datetime,timezone
import numpy as np
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
METHODS=['information','brier','pseudo_count','uniform','weighted128','minimax']
TOL=2e-7

def now():return datetime.now(timezone.utc).isoformat()
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def write(path,data):
    path=Path(path);path.parent.mkdir(parents=True,exist_ok=True)
    tmp=path.with_suffix(path.suffix+'.tmp');tmp.write_text(json.dumps(data,indent=2,allow_nan=False)+'\n');tmp.replace(path)
def save(path,**arrays):
    path=Path(path);path.parent.mkdir(parents=True,exist_ok=True)
    tmp=path.with_suffix(path.suffix+'.tmp')
    with tmp.open('wb') as f:np.savez_compressed(f,**arrays)
    tmp.replace(path)
def verify_sources():
    data=json.loads((HERE/'SOURCES.json').read_text())
    for rel,h in data.items():assert sha(HERE/rel)==h,('source changed',rel)
    return sha(HERE/'SOURCES.json')
def levels(t):return [list(itertools.product(((0,0),(0,1),(1,0),(1,1)),repeat=d)) for d in range(t+1)]
def raw_law(T,Z,histories):
    answer=[]
    for h in histories:
        values=[]
        for q in range(len(T)):
            state=np.zeros(T.shape[-1]);state[0]=1.
            for a,o in h:state=(state@T[q,a])*Z[q,a,:,o]
            values.append(state.sum())
        answer.append(values)
    return np.asarray(answer).T

def replay(T,Z,t,rows,E=None,leaf=None):
    layers=levels(t);decisions=sum(layers[:-1],[]);index={h:i for i,h in enumerate(decisions)}
    rows=np.asarray(rows);assert rows.shape==(len(decisions),2)
    assert np.isfinite(rows).all() and rows.min()>=0 and np.max(abs(rows.sum(1)-1))<1e-10
    for arr in (T,Z):assert np.isfinite(arr).all() and arr.min()>=0 and np.max(abs(arr.sum(-1)-1))<1e-10
    weights=[]
    for h in layers[-1]:
        w=1.
        for k,(a,o) in enumerate(h):w*=rows[index[h[:k]],a]
        weights.append(w)
    weights=np.array(weights);raw=raw_law(T,Z,layers[-1]);actual=raw*weights
    residual=float(np.max(abs(actual.sum(1)-1)))
    if E is not None:residual=max(residual,float(np.max(abs(E-actual))))
    if leaf is not None:residual=max(residual,float(np.max(abs(leaf-weights))))
    assert residual<1e-10,('policy replay',residual)
    return actual,weights,raw,residual

def rewards(E,histories):
    Q=len(E);m=E.mean(0);post=np.divide(E,Q*m,out=np.zeros_like(E),where=m>0)
    logs=np.zeros_like(post);np.log2(post,out=logs,where=post>0)
    ig=float(np.log2(Q)+np.sum(m*(post*logs).sum(0)))
    br=float(np.sum(m*(post*post).sum(0))-1/Q)
    count=[]
    for h in histories:
        counts=[0,0];total=0.
        for a,o in h:total+=1/np.sqrt(1+counts[o]);counts[o]+=1
        count.append(total)
    return dict(information=ig,brier=br,pseudo_count=float(m@count))

def target(T,Z,n,j):
    choices=[(j>>k)&1 for k in range(2**n-2,-1,-1)];histories=[]
    for obs in itertools.product((0,1),repeat=n):
        h=[];node=0
        for o in obs:h.append((choices[node],o));node=2*node+1+o
        histories.append(tuple(h))
    return raw_law(T,Z,histories)

def check_witness(E,F,w):
    keep=w['source_indices'];G=w['decoder'];a=w['alpha'];b=w['b']
    assert np.array_equal(keep,np.flatnonzero(E.max(0)>0))
    for v in (G,a,b):assert np.isfinite(v).all()
    assert G.shape==(len(keep),F.shape[1]) and G.min()>=0 and np.max(abs(G.sum(1)-1))<1e-10
    assert a.min()>=0 and abs(a.sum()-1)<1e-10 and b.min()>=0 and np.max(b-a[:,None])<1e-10
    upper=float(np.max(abs(E[:,keep]@G-F).sum(1))/2)
    lower=float(np.sum(F*b)-np.max(E[:,keep].T@b,axis=1).sum())
    assert np.isfinite([lower,upper]).all() and -TOL<=upper-lower<=TOL
    return lower,upper

def classify(lower,upper,epsilon):
    if upper<=epsilon-1e-9:return 'reproduced'
    if lower>epsilon+1e-9:return 'not_reproduced'
    return 'unresolved_boundary'
