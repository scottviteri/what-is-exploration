"""Independent replay of EVERY new decoder and decision-loss witness."""
from common import *
import argparse,time
from datetime import datetime,timezone

def check(folder):
    start=time.monotonic();r=json.loads((folder/'result.json').read_text());assert r['status']=='complete'
    orig=ORIGINAL/'main_results'/r['original_cell'];assert digest(orig/'result.json')==r['original_result_sha256']
    assert digest(orig/'model.npz')==r['model_sha256']
    assert digest(orig/r['policy_checkpoint']/'policy.npz')==r['policy_sha256']
    with np.load(orig/r['policy_checkpoint']/'policy.npz') as z:E=z['E'].copy()
    with np.load(orig/'model.npz') as z:T=z['T'].copy();Z=z['Z'].copy()
    # Different target-generation route: literal production tree compiler; its
    # masses and source replay are separately checked by audit_saved.py.
    targets=core.Targets(T,Z,r['target_horizon']);all_lo=[];all_hi=[];all_ids=[];maxgap=0.
    for item in r['batches']:
        p=folder/item['path'];assert digest(p)==item['sha256']
        with np.load(p,allow_pickle=False) as z:
            ids=z['indices'];G=z['G'];alpha=z['alpha'];b=z['b'];keep=z['source_indices']
            assert np.array_equal(keep,np.flatnonzero(E.max(0)>0))
            F=np.array([targets.get(int(j))['kernel'] for j in ids]);source=E[:,keep]
            assert G.min()>=0 and np.max(abs(G.sum(2)-1))<1e-12
            assert alpha.min()>=0 and np.max(abs(alpha.sum(1)-1))<1e-12
            assert b.min()>=0 and np.max(b-alpha[:,:,None])<=1e-15
            hi=np.max(abs(np.einsum('qx,bxy->bqy',source,G)-F).sum(2),axis=1)/2
            lo=np.sum(F*b,axis=(1,2))-np.max(np.einsum('qx,bqy->bxy',source,b),axis=2).sum(1)
            assert np.isfinite(lo).all() and np.isfinite(hi).all()
            assert np.max(hi-lo)<=2e-7 and np.max(lo-hi)<=2e-7
            assert np.max(abs(lo-z['lower']))<1e-12 and np.max(abs(hi-z['upper']))<1e-12
            maxgap=max(maxgap,float(np.max(hi-lo)));all_lo.extend(lo);all_hi.extend(hi);all_ids.extend(ids.tolist())
    assert all_ids==list(range(targets.count))
    assert abs(max(all_lo)-r['audit']['lower'])<1e-12 and abs(max(all_hi)-r['audit']['upper'])<1e-12
    assert abs(np.mean(all_lo)-r['audit']['mean_lower'])<1e-12 and abs(np.mean(all_hi)-r['audit']['mean_upper'])<1e-12
    out=dict(status='passed',cell=r['original_cell'],target_count=len(all_ids),decoder_witnesses=len(all_ids),decision_loss_witnesses=len(all_ids),max_interval_gap=maxgap,seconds=time.monotonic()-start,checked_utc=datetime.now(timezone.utc).isoformat(),result_sha256=digest(folder/'result.json'),scope='All saved original-source upper/lower witnesses, not only the hardest target; floating-point checks.')
    write(folder/'INDEPENDENT_CHECK.json',out);return out
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('folders',nargs='+',type=Path);args=p.parse_args()
    for folder in args.folders:print(json.dumps(check(folder)),flush=True)
