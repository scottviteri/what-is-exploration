"""Exhaustive additional audits. Preserve original inputs and every new witness."""
import os
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'): os.environ[k]='1'
import argparse,hashlib,json,sys,time,traceback,shutil
from pathlib import Path
from datetime import datetime,timezone
import numpy as np
HERE=Path(__file__).resolve().parent
OLD=HERE.parent/'target_selection_2026-09-23'
FOLLOW=HERE.parent/'target_selection_followups_2026-09-23'
sys.dont_write_bytecode=True
sys.path.insert(0,str(FOLLOW))
from common import core, independent_law, digest, write
from recovery_decoder import RecoveryDecoder
from recover_saved import kernels_from_raw
TOL=2e-7

def replay(T,Z,rows,leaf,E):
    assert rows.shape==(21,2) and leaf.shape==(64,) and E.shape==(len(T),64)
    for x in (T,Z,rows,E):
        assert np.isfinite(x).all() and x.min()>=0 and np.max(abs(x.sum(-1)-1))<1e-10
    law=independent_law(T,Z,core.levels(3)); weights=[]
    for h in core.levels(3)[-1]:
        w=1.;prefix=0
        for depth,(a,o) in enumerate(h):
            w*=rows[(4**depth-1)//3+prefix,a];prefix=4*prefix+2*a+o
        weights.append(w)
    raw=np.array([law[h] for h in core.levels(3)[-1]]).T
    assert np.max(abs(np.array(weights)-leaf))<1e-12
    assert np.max(abs(raw*np.array(weights)-E))<1e-12

def check_batch(path,expected,E,targets):
    assert digest(path)==expected,('witness hash',str(path))
    with np.load(path,allow_pickle=False) as z:
        ids=z['indices'];G=z['G'];alpha=z['alpha'];b=z['b'];keep=z['source_indices']
        assert np.array_equal(keep,np.flatnonzero(E.max(0)>0))
        F=np.array([targets.get(int(j))['kernel'] for j in ids]); source=E[:,keep]
        assert G.min()>=0 and np.max(abs(G.sum(2)-1))<1e-12
        assert alpha.min()>=0 and np.max(abs(alpha.sum(1)-1))<1e-12
        assert b.min()>=0 and np.max(b-alpha[:,:,None])<1e-15
        hi=np.max(abs(np.einsum('qx,bxy->bqy',source,G)-F).sum(2),axis=1)/2
        lo=np.sum(F*b,axis=(1,2))-np.max(np.einsum('qx,bqy->bxy',source,b),axis=2).sum(1)
        assert np.isfinite(lo).all() and np.isfinite(hi).all()
        assert np.max(hi-lo)<=TOL and np.max(lo-hi)<=TOL
        assert np.max(abs(lo-z['lower']))<1e-12 and np.max(abs(hi-z['upper']))<1e-12
    return ids,lo,hi

def check(folder):
    r=json.loads((folder/'result.json').read_text()); assert r['status']=='complete'
    for p,h in r['input_sha256'].items(): assert digest(Path(p))==h
    with np.load(r['policy']) as z:E=z['E'];rows=z['rows'];leaf=z['leaf']
    with np.load(r['model']) as z:T=z['T'];Z=z['Z']
    replay(T,Z,rows,leaf,E); targets=core.Targets(T,Z,4); ids=[];lo=[];hi=[]
    for batch in r['batches']:
        j,l,u=check_batch(Path(batch['path']),batch['sha256'],E,targets)
        ids.extend(j.tolist());lo.extend(l);hi.extend(u)
    assert ids==list(range(32768))
    assert abs(max(lo)-r['audit']['lower'])<1e-12 and abs(max(hi)-r['audit']['upper'])<1e-12
    result=dict(status='passed',targets=len(ids),max_gap=float(np.max(np.array(hi)-lo)),result_sha256=digest(folder/'result.json'),checked_utc=datetime.now(timezone.utc).isoformat(),scope='Every original-source decoder and bounded-decision-loss witness; independently generated target laws; floating-point arithmetic, not exact interval arithmetic.')
    write(folder/'CHECK.json',result);return result

def run(args):
    start=time.monotonic();out=args.output.resolve();out.mkdir(parents=True,exist_ok=False)
    source=args.source.resolve();meta=json.loads((source/'result.json').read_text());cp=meta['checkpoints'][-1]
    policy=source/f"checkpoint_{cp['k']:03d}"/'policy.npz';model=source/'model.npz'
    inputs={str(p):digest(p) for p in [policy,model,source/'result.json',Path(__file__)]}
    for name in ['common.py','recover_saved.py','recovery_decoder.py']:inputs[str(FOLLOW/name)]=digest(FOLLOW/name)
    with np.load(policy) as z:E=z['E'].copy();rows=z['rows'].copy();leaf=z['leaf'].copy()
    with np.load(model) as z:T=z['T'].copy();Z=z['Z'].copy()
    replay(T,Z,rows,leaf,E)
    report=dict(status='running',model=str(model),policy=str(policy),source_result=str(source/'result.json'),model_name=meta['model_name'],input_sha256=inputs,source_array_sha256=hashlib.sha256(E.tobytes()).hexdigest(),selection_used=False,collection_horizon=3,target_horizon=4,target_count=32768,completed_targets=0,batches=[],started_utc=datetime.now(timezone.utc).isoformat(),wall_seconds=args.seconds)
    write(out/'result.json',report);lower=[];upper=[]
    try:
        if args.resume:
            old=json.loads(args.resume.read_text());assert old['source_array_sha256']==report['source_array_sha256'] and old['target_horizon']==4
            report['input_sha256'][str(args.resume.resolve())]=digest(args.resume)
            targets=core.Targets(T,Z,4)
            for batch in old['batches']:
                path=(args.resume.parent/batch['path']).resolve();j,l,u=check_batch(path,batch['sha256'],E,targets)
                assert j.tolist()==list(range(len(lower),len(lower)+len(j)))
                lower.extend(l);upper.extend(u);report['batches'].append(dict(path=str(path),sha256=batch['sha256'],reused=True,targets=len(j)))
            report['reused_targets']=len(lower)
        layers=core.levels(4);law=independent_law(T,Z,[layers[-1]]);raw=np.array([law[h] for h in layers[-1]]).T
        decoder=RecoveryDecoder(E,16,'native-simplex',30.)
        for begin in range(len(lower),32768,128):
            assert shutil.disk_usage(HERE).free>15*1024**3,'Disk reserve'
            ids=np.arange(begin,min(begin+128,32768));F=kernels_from_raw(raw,4,ids)
            G=[];alpha=[];b=[];lo=[];hi=[]
            for j,f in zip(ids,F):
                if time.monotonic()-start>args.seconds:raise TimeoutError('Explicit whole-policy budget')
                d,w=decoder.solve(f);G.append(w['decoder']);alpha.append(w['alpha']);b.append(w['b']);lo.append(d['lower']);hi.append(d['upper'])
            p=out/f'witnesses_{begin:05d}.npz'
            with p.open('wb') as h:np.savez_compressed(h,indices=ids,G=G,alpha=alpha,b=b,lower=lo,upper=hi,source_indices=w['source_indices'])
            lower.extend(lo);upper.extend(hi);report['batches'].append(dict(path=str(p),sha256=digest(p),reused=False,targets=len(ids)))
            report.update(completed_targets=len(lower),seconds=time.monotonic()-start);write(out/'result.json',report)
        report.update(status='complete',exhaustive=True,audit=dict(lower=float(max(lower)),upper=float(max(upper)),mean_lower=float(np.mean(lower)),mean_upper=float(np.mean(upper)),hardest_target=int(np.argmax(upper))))
        np.savez_compressed(out/'profile.npz',indices=np.arange(32768),lower=lower,upper=upper)
        for p,h in inputs.items():assert digest(Path(p))==h
    except Exception as e:
        report.update(status='failed',error=repr(e),traceback=traceback.format_exc());raise
    finally:
        report.update(seconds=time.monotonic()-start,finished_utc=datetime.now(timezone.utc).isoformat());write(out/'result.json',report)
    print(json.dumps(check(out)),flush=True)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--source',type=Path);p.add_argument('--output',type=Path);p.add_argument('--resume',type=Path);p.add_argument('--seconds',type=float,default=2400);p.add_argument('--check',type=Path);args=p.parse_args()
    if args.check:print(json.dumps(check(args.check)))
    else:run(args)
