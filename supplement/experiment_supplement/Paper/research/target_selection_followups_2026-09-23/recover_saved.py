"""Evaluate an unchanged saved policy; retain every newly computed witness."""
from common import *
from recovery_decoder import RecoveryDecoder
import argparse,time,traceback
from datetime import datetime,timezone


def all_kernels(T,Z,n,ids):
    # Independently compile controlled histories for all observation paths.
    layers=core.levels(n);law=independent_law(T,Z,[layers[-1]])
    raw=np.array([law[h] for h in layers[-1]]).T
    return kernels_from_raw(raw,n,ids)

def kernels_from_raw(raw,n,ids):
    obs=((np.arange(2**n)[:,None]>>np.arange(n-1,-1,-1))&1)
    tree_node=np.zeros(2**n,dtype=int);index=np.zeros((len(ids),2**n),dtype=int)
    for depth in range(n):
        a=(np.asarray(ids)[:,None]>>((2**n-2)-tree_node)[None,:])&1
        index=4*index+2*a+obs[:,depth][None,:]
        tree_node=2*tree_node+1+obs[:,depth]
    return raw[:,index].transpose(1,0,2)

def main():
    p=argparse.ArgumentParser();p.add_argument('--cell',required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--horizon',type=int,default=4);p.add_argument('--wall-seconds',type=float,default=1500);args=p.parse_args()
    args.output.mkdir(parents=True,exist_ok=True)
    original=ORIGINAL/'main_results'/args.cell;r=json.loads((original/'result.json').read_text())
    cp=r['checkpoints'][-1];policy=original/f"checkpoint_{cp['k']:03d}"/'policy.npz'
    with np.load(policy,allow_pickle=False) as z:E=z['E'].copy()
    with np.load(original/'model.npz',allow_pickle=False) as z:T=z['T'].copy();Z=z['Z'].copy()
    report=dict(status='running',original_cell=args.cell,original_status=r['status'],original_result_sha256=digest(original/'result.json'),model_sha256=digest(original/'model.npz'),policy_sha256=digest(policy),policy_checkpoint=f"checkpoint_{cp['k']:03d}",source_array_sha256=hashlib.sha256(E.tobytes()).hexdigest(),target_horizon=args.horizon,selection_used=False,started_utc=datetime.now(timezone.utc).isoformat(),source_sha256={n:digest(HERE/n) for n in ['common.py','recovery_decoder.py','recover_saved.py']},acceptance='Explicit feasible original-source decoder and decision-loss bounds, gap <= 2e-7. Solver stationarity recorded separately.',target_count=2**(2**args.horizon-1),completed_targets=0,batches=[])
    write(args.output/'result.json',report);start=time.monotonic();deadline=start+args.wall_seconds
    try:
        layers=core.levels(args.horizon);law=independent_law(T,Z,[layers[-1]]);raw=np.array([law[h] for h in layers[-1]]).T
        decoder=RecoveryDecoder(E,2**args.horizon,'native-simplex',30)
        low=[];high=[];worst_kkt=0.;fallbacks=[]
        for begin in range(0,report['target_count'],128):
            ids=np.arange(begin,min(begin+128,report['target_count']));F=kernels_from_raw(raw,args.horizon,ids)
            G=[];alphas=[];b=[];lo=[];hi=[]
            for j,f in zip(ids,F):
                if time.monotonic()>deadline:raise TimeoutError('Declared whole-policy evaluation budget')
                d,w=decoder.solve(f)
                G.append(w['decoder']);alphas.append(w['alpha']);b.append(w['b']);lo.append(d['lower']);hi.append(d['upper'])
                worst_kkt=max(worst_kkt,d['lp_stationarity_diagnostic'])
                if d.get('fallback_used'):fallbacks.append(dict(target=int(j),attempts=d['attempts']))
            fn=f'witnesses_{begin:05d}.npz';tmp=args.output/(fn+'.tmp')
            with tmp.open('wb') as f:np.savez_compressed(f,indices=ids,G=np.array(G),alpha=np.array(alphas),b=np.array(b),lower=np.array(lo),upper=np.array(hi),source_indices=w['source_indices'])
            tmp.replace(args.output/fn)
            report['batches'].append(dict(path=fn,sha256=digest(args.output/fn),targets=len(ids)))
            low.extend(lo);high.extend(hi);report.update(completed_targets=len(low),seconds=time.monotonic()-start,max_lp_stationarity_diagnostic=worst_kkt,fallbacks=fallbacks)
            write(args.output/'result.json',report)
        lower=np.array(low);upper=np.array(high)
        np.savez_compressed(args.output/'profile.npz',indices=np.arange(len(low)),lower=lower,upper=upper)
        report.update(status='complete',exhaustive=True,audit=dict(lower=float(lower.max()),upper=float(upper.max()),mean_lower=float(lower.mean()),mean_upper=float(upper.mean()),hardest_target=int(upper.argmax()),target_count=len(low),evaluated=len(low),exhaustive=True,bound_scope='full_target_class'))
        assert digest(policy)==report['policy_sha256'] and digest(original/'result.json')==report['original_result_sha256']
    except Exception as exc:
        report.update(status='failed',error=repr(exc),traceback=traceback.format_exc());raise
    finally:
        report.update(seconds=time.monotonic()-start,finished_utc=datetime.now(timezone.utc).isoformat());write(args.output/'result.json',report)
    print(json.dumps(dict(cell=args.cell,status=report['status'],seconds=report['seconds'],audit=report['audit'])),flush=True)
if __name__=='__main__':main()
