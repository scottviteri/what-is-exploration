"""Literal reward replay and bounded same-time order diagnostics on 22 classes."""
import os
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
import sys,hashlib,json,csv,argparse,time,collections,importlib.util
from pathlib import Path
import numpy as np
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2];OLD=HERE.parent/'target_selection_2026-09-23';FOLLOW=HERE.parent/'target_selection_followups_2026-09-23';CAND=HERE.parent/'empirical_ending_2026-09-23'
sys.path.insert(0,str(FOLLOW))
from common import core,digest,write,independent_law
from recovery_decoder import RecoveryDecoder
from extra_objectives import fixed_history_scores
from audit import replay

def reward(E):
    Q=len(E);m=E.mean(0);keep=m>0;post=E[:,keep]/(Q*m[keep]);logs=np.zeros_like(post);np.log2(post,out=logs,where=post>0)
    ig=float(np.log2(Q)+np.sum(m[keep]*np.sum(post*logs,axis=0)))
    br=float(np.sum(m[keep]*np.sum(post*post,axis=0))-1/Q)
    return dict(information=ig,brier=br)
def bellman(g,scores):
    v={h:float(g.p[h].mean())*float(scores[i]) for i,h in enumerate(g.layers[-1])}
    for layer in reversed(g.layers[:-1]):
        for h in layer:v[h]=max(sum(v[h+((a,o),)] for o in (0,1)) for a in (0,1))
    return v[()]
def inventory():
    check=json.loads((CAND/'FIGURE22_CHECK.json').read_text());s=json.loads((FOLLOW/'COMBINED_STATUS.json').read_text())
    for p,h in check['source_sha256'].items():assert digest(ROOT/p)==h,('original binding changed',p)
    records=[]
    for cell,item in check['checked_representatives'].items():
        prov=s['provenance'][cell];source=Path(prov.get('result_path',prov.get('original_result_path')));r=json.loads(source.read_text());cp=r['checkpoints'][-1]
        records.append(dict(cell=cell,**item,policy=str(source.parent/f"checkpoint_{cp['k']:03d}"/'policy.npz'),model=str(source.parent/'model.npz'),result=str(source)))
    return records

def derive():
    records=inventory();refs={};bindings={};out=[]
    for r in records:
        case=r['case'];pp=Path(r['policy']);mp=Path(r['model']);bindings[str(pp)]=digest(pp);bindings[str(mp)]=digest(mp);bindings[r['result']]=digest(Path(r['result']))
        with np.load(mp) as z:T=z['T'];Z=z['Z']
        with np.load(pp) as z:E=z['E'];rows=z['rows'];leaf=z['leaf']
        replay(T,Z,rows,leaf,E)
        if case not in refs:
            g=core.geometry(T,Z,3);score=fixed_history_scores(g)
            refs[case]={obj:dict(maximum=bellman(g,score[obj]),minimum=-bellman(g,-score[obj])) for obj in ['information','brier']}
        re=reward(E);res=dict(r,**{obj+'_reward':v for obj,v in re.items()},E_sha256=hashlib.sha256(E.tobytes()).hexdigest())
        for obj,v in re.items():
            ref=refs[case][obj];width=ref['maximum']-ref['minimum'];assert ref['minimum']-1e-10<=v<=ref['maximum']+1e-10
            res[obj+'_range']=width;res[obj+'_sacrifice']=(ref['maximum']-v)/width if width>1e-12 else None
            # An independent fixed-history coefficient expression must agree.
            if case==r['case']:
                gg=core.geometry(T,Z,3);sc=fixed_history_scores(gg)[obj];assert abs(float(E.mean(0)@sc)-v)<1e-12
        out.append(res)
    write(HERE/'REWARD_DIAGNOSTICS.json',dict(status='passed',representatives=len(out),classes=len(refs),records=out,ranges=refs,input_sha256=bindings,source_sha256=digest(Path(__file__)),scope='Rewards and full-history attainable ranges on the original 22 classes; literal policy/model replay plus two reward formulas. Float64 numerical calculations. Zero attainable ranges have undefined normalized sacrifice.'))
    with (HERE/'reward_diagnostics.csv').open('w') as f:w=csv.DictWriter(f,fieldnames=list(out[0]));w.writeheader();w.writerows(out)
    native=collections.Counter(r['method'] for r in out);print('rewards passed',len(out),dict(native),flush=True)

def order():
    d=json.loads((HERE/'REWARD_DIAGNOSTICS.json').read_text());r=d['records'];out=HERE/'order';out.mkdir(exist_ok=False)
    # One original representative per method/class: fixed in advance by lexical cell ID,
    # never by the held-out audit value or by these directed deficiencies.
    selected={}
    for x in sorted(r,key=lambda x:x['cell']):selected.setdefault((x['case'],x['method']),x)
    jobs=[]
    for case in d['ranges']:
        for nm in ['weighted128','minimax']:
            for bm in ['brier','face_brier_0.05']:
                if (case,bm) not in selected:continue
                n=selected[case,nm];b=selected[case,bm]
                for src,tgt in [(n,b),(b,n)]:jobs.append(dict(case=case,source=src['cell'],target=tgt['cell'],source_method=src['method'],target_method=tgt['method'],source_policy=src['policy'],target_policy=tgt['policy']))
    write(out/'MANIFEST.json',dict(selection='Lexically first original verified cell for each case/method, chosen without directed results. Missing five 5%-Brier controls are separate later additions.',jobs=jobs,reward_input_sha256=digest(HERE/'REWARD_DIAGNOSTICS.json')))
    results=[]
    for i,j in enumerate(jobs):
        start=time.monotonic()
        try:
            pp=Path(j['source_policy']);tp=Path(j['target_policy']);assert digest(pp)==d['input_sha256'][str(pp)] and digest(tp)==d['input_sha256'][str(tp)]
            with np.load(pp) as z:E=z['E'].copy()
            with np.load(tp) as z:F=z['E'].copy()
            dec=RecoveryDecoder(E,F.shape[1],'native-ipm',60.);v,w=dec.solve(F)
            G=w['decoder'];alpha=w['alpha'];b=w['b'];keep=w['source_indices']
            assert G.min()>=0 and np.max(abs(G.sum(1)-1))<1e-12 and alpha.min()>=0 and abs(alpha.sum()-1)<1e-12 and b.min()>=0 and np.max(b-alpha[:,None])<1e-15
            lower=float(np.sum(F*b)-np.max(E[:,keep].T@b,axis=1).sum());upper=float(np.max(abs(E[:,keep]@G-F).sum(1))/2)
            assert -2e-7<=upper-lower<=2e-7
            witness=out/f'witness_{i:03d}.npz';np.savez_compressed(witness,E=E,F=F,G=G,alpha=alpha,b=b,source_indices=keep,lower=lower,upper=upper)
            result=dict(j,status='passed',lower=lower,upper=upper,witness=str(witness),witness_sha256=digest(witness),seconds=time.monotonic()-start)
        except Exception as e:result=dict(j,status='failed',error=repr(e),seconds=time.monotonic()-start)
        results.append(result);write(out/'RESULTS.json',dict(status='running' if len(results)<len(jobs) else 'complete',planned=len(jobs),records=results))
    print('order complete',len(results),collections.Counter(x['status'] for x in results),flush=True)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--order',action='store_true');a=p.parse_args();order() if a.order else derive()
