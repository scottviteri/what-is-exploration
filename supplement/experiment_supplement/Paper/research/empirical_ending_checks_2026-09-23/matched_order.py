"""Check whether reward-matched scalar improvements imply record dominance."""
from diagnostics import *
m=json.loads((HERE/'matched_manifest.json').read_text());out=HERE/'matched_order';out.mkdir(exist_ok=False);rows=[]
for spec in m['thresholds']:
 cell=spec['id'];source=HERE/'matched_results'/cell;report=json.loads((source/'result.json').read_text());assert report['status']=='complete'
 cp=report['checkpoints'][-1];new=source/f"checkpoint_{cp['k']:03d}"/'policy.npz';old=Path(spec['reference_policy']);assert digest(old)==spec['reference_policy_sha256']
 with np.load(old) as z:N=z['E'].copy()
 with np.load(new) as z:C=z['E'].copy()
 for name,E,F in [('native_to_control',N,C),('control_to_native',C,N)]:
  d,w=RecoveryDecoder(E,64,'native-ipm',60).solve(F);G=w['decoder'];alpha=w['alpha'];b=w['b'];keep=w['source_indices']
  assert G.min()>=0 and np.max(abs(G.sum(1)-1))<1e-12 and alpha.min()>=0 and abs(alpha.sum()-1)<1e-12 and b.min()>=0 and np.max(b-alpha[:,None])<1e-15
  lo=float((F*b).sum()-np.max(E[:,keep].T@b,axis=1).sum());hi=float(abs(E[:,keep]@G-F).sum(1).max()/2);assert -2e-7<=hi-lo<=2e-7
  path=out/(cell+'_'+name+'.npz');np.savez_compressed(path,E=E,F=F,G=G,alpha=alpha,b=b,source_indices=keep,lower=lo,upper=hi)
  rows.append(dict(case=spec['case'],id=cell,direction=name,lower=lo,upper=hi,witness=str(path),witness_sha256=digest(path),native_policy=str(old),control_policy=str(new),native_policy_sha256=digest(old),control_policy_sha256=digest(new)))
pairs={}
for r in rows:pairs.setdefault(r['case'],[]).append(r)
write(HERE/'MATCHED_ORDER.json',dict(status='passed',directions=44,pairs=22,incomparable=sum(all(r['lower']>1e-6 for r in rs) for rs in pairs.values()),equivalent_within_tolerance=sum(all(r['upper']<1e-6 for r in rs) for rs in pairs.values()),records=rows,scope='Exact same selected policies as the reward-matched experiment; explicit numerical witnesses, collection time 3, threshold 1e-6.'))
print('matched order complete')
