"""Independent saved-array replay of all completed full-audit CPU witnesses."""
import os
for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'):os.environ[key]='1'
from pathlib import Path
import json,hashlib,numpy as np
HERE=Path(__file__).resolve().parent

def main():
    result=json.loads((HERE/'CPU_FULL_RESULTS.json').read_text());records=[];seen=[];maximum=0.;maxgap=0.
    lookup={}
    for path in sorted((HERE/'cpu_full_chunks').glob('worker*.json')):
      for r in json.loads(path.read_text())['rows']:lookup[r['target']]=r
    for path in sorted((HERE/'cpu_full_chunks').glob('*.npz')):
      data=np.load(path);E=data['E'][:,data['source_indices']];worst=0.
      for j,F,G,alpha,b in zip(data['targets'],data['F'],data['G'],data['alpha'],data['b']):
        j=int(j);seen.append(j)
        residual=max(float(abs(G.sum(1)-1).max()),float(max(0,-G.min())),float(abs(alpha.sum()-1)),float(max(0,-alpha.min())),float(max(0,-b.min())),float(np.maximum(b-alpha[:,None],0).max()))
        upper=float(np.abs(E@G-F).sum(1).max()/2);lower=float((F*b).sum()-np.max(E.T@b,axis=1).sum());gap=upper-lower
        row=lookup[j];disagreement=max(abs(upper-row['upper']),abs(lower-row['lower']))
        if not np.isfinite([lower,upper,residual]).all() or residual>1e-12 or lower>upper+1e-10 or gap>2e-7 or disagreement>1e-13:raise RuntimeError(f'Invalid original-probability witness {j}')
        maximum=max(maximum,residual);maxgap=max(maxgap,gap);worst=max(worst,disagreement)
      records.append(dict(file=str(path.relative_to(HERE)),sha256=hashlib.sha256(path.read_bytes()).hexdigest(),count=len(data['targets']),max_replay_disagreement=worst))
    if len(set(seen))!=len(seen):raise RuntimeError('duplicate target IDs')
    if result['status']=='complete' and sorted(seen)!=list(range(32768)):raise RuntimeError('incomplete full audit')
    value=dict(status='passed',target_count=len(seen),complete=sorted(seen)==list(range(32768)),max_feasibility=maximum,max_gap=maxgap,scope='Independent CPU matrix replay of stochastic decoder uppers and feasible decision-dual lowers on original probabilities. Floating-point evidence, not exact arithmetic or eventual exploration.',witness_files=records)
    (HERE/'CPU_FULL_VALIDATION.json').write_text(json.dumps(value,indent=2)+'\n');print(json.dumps({k:v for k,v in value.items() if k!='witness_files'},indent=2))
if __name__=='__main__':main()
