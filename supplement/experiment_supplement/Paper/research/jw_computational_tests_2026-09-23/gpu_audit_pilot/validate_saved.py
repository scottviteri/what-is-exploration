"""Independent CPU replay of saved GPU and CPU witnesses; no LP/GPU imports."""
import os
for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'):os.environ[key]='1'
from pathlib import Path
import hashlib,json,re,numpy as np
HERE=Path(__file__).resolve().parent

def main():
    records=[]
    for path in sorted(HERE.glob('*witness.npz')):
      data=np.load(path);E=data['E'];Fs=data['F'];row=[]
      for k,F in enumerate(Fs):
        if f'{k}_G' in data:
          G=data[f'{k}_G'];alpha=data[f'{k}_alpha'];b=data[f'{k}_b'];source=E
        elif f'{k}_decoder' in data:
          G=data[f'{k}_decoder'];alpha=data[f'{k}_alpha'];b=data[f'{k}_b'];source=E[:,data[f'{k}_source_indices']]
        else:raise RuntimeError(f'Missing witness in {path} at {k}')
        feasibility=max(float(np.abs(G.sum(1)-1).max()),float(max(0,-G.min())),float(abs(alpha.sum()-1)),float(max(0,-alpha.min())),float(max(0,-b.min())),float(np.maximum(b-alpha[:,None],0).max()))
        upper=float(np.abs(source@G-F).sum(1).max()/2);lower=float((F*b).sum()-np.max(source.T@b,axis=1).sum())
        if not np.isfinite([upper,lower,feasibility]).all() or feasibility>1e-12 or lower>upper+1e-10:raise RuntimeError(f'Invalid witness {path} index {k}')
        row.append(dict(index=k,lower=lower,upper=upper,gap=upper-lower,feasibility=feasibility,accuracy_accepted=upper-lower<=2e-7))
      records.append(dict(file=path.name,sha256=hashlib.sha256(path.read_bytes()).hexdigest(),rows=row))
    sources=json.loads((HERE/'PROTOCOL.json').read_text())['source_sha256'];source=HERE.parents[1]/'target_selection_2026-09-23'
    current={name:hashlib.sha256((HERE/name if name=='pilot.py' else source/name).read_bytes()).hexdigest()==digest for name,digest in sources.items()}
    if not all(current.values()):raise RuntimeError('Original execution source changed')
    result=dict(status='passed',scope='Repaired witness feasibility and original-probability brackets; not an exact-arithmetic/outward-rounded proof and not a guarantee that all GPU calls met accuracy.',files=len(records),witnesses=sum(len(x['rows']) for x in records),accuracy_rejections=sum(not r['accuracy_accepted'] for x in records for r in x['rows']),execution_sources_unchanged=current,records=records)
    (HERE/'VALIDATION.json').write_text(json.dumps(result,indent=2,allow_nan=False)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='records'},indent=2))
if __name__=='__main__':main()
