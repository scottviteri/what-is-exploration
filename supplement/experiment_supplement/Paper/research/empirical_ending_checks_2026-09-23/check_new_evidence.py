"""Replay supplementary artifacts and deliberately corrupt witnesses to test rejection."""
import os
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
from pathlib import Path
import json,tempfile,hashlib,sys
import numpy as np
from audit import check,check_batch,core,digest,write,HERE
checks=[]
for p in [HERE/'uniform_audit']+sorted((HERE/'control_audits').glob('cell_*')):
    c=check(p);checks.append(dict(path=str(p),status=c['status'],targets=c['targets']))
assert len(checks)==19
order=json.loads((HERE/'COMPLETE_ORDER.json').read_text())
for r in order['records']:
    p=Path(r['witness']);assert digest(p)==r['witness_sha256']
    with np.load(p) as z:
        E=z['E'];F=z['F'];G=z['G'];a=z['alpha'];b=z['b'];keep=z['source_indices']
        with np.load(r['source_policy']) as q:assert np.array_equal(E,q['E'])
        with np.load(r['target_policy']) as q:assert np.array_equal(F,q['E'])
        assert np.array_equal(keep,np.flatnonzero(E.max(0)>0))
        assert G.min()>=0 and np.max(abs(G.sum(1)-1))<1e-12 and a.min()>=0 and abs(a.sum()-1)<1e-12 and b.min()>=0 and np.max(b-a[:,None])<1e-15
        hi=float(np.max(abs(E[:,keep]@G-F).sum(1))/2);lo=float((F*b).sum()-np.max(E[:,keep].T@b,axis=1).sum())
        assert abs(lo-r['lower'])<1e-12 and abs(hi-r['upper'])<1e-12 and -2e-7<=hi-lo<=2e-7
r=json.loads((HERE/'uniform_audit/result.json').read_text())
with np.load(r['model']) as z:T=z['T'];Z=z['Z']
with np.load(r['policy']) as z:E=z['E']
targets=core.Targets(T,Z,4);source=Path(r['batches'][-1]['path'])
with np.load(source) as z:arrays={k:z[k].copy() for k in z.files}
tamper=[]
with tempfile.TemporaryDirectory(prefix='empirical-check-') as tmp:
    for kind in ['negative_decoder','false_lower_bound','wrong_target','wrong_file_hash']:
        a={k:v.copy() for k,v in arrays.items()}
        if kind=='negative_decoder':a['G'][0,0,0]=-1.
        if kind=='false_lower_bound':a['lower'][0]+=.01
        if kind=='wrong_target':a['indices'][0]=0
        p=Path(tmp)/(kind+'.npz');np.savez_compressed(p,**a)
        try:check_batch(p,'bad' if kind=='wrong_file_hash' else digest(p),E,targets)
        except (AssertionError,ValueError):tamper.append(kind)
        else:raise RuntimeError('Corruption accepted: '+kind)
assert len(tamper)==4
write(HERE/'EVIDENCE_CHECK.json',dict(status='passed',complete_exhaustive_audits=len(checks),total_target_witnesses=19*32768,audits=checks,directed_checks=len(order['records']),rejected_corruptions=tamper,source_sha256=digest(Path(__file__)),scope='Fresh full numerical replay and negative controls. Neither outward-rounded floating-point arithmetic nor end-to-end Lean verification.'))
print('passed',len(checks),'full audits,',len(order['records']),'directed checks,',len(tamper),'negative tests')
