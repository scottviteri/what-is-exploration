#!/usr/bin/env python3
"""Auditor must reject deliberate corruption; no solver invocation."""
from pathlib import Path
import json,shutil
import numpy as np
from independent_audit import audit
HERE=Path(__file__).resolve().parent

def alter_npz(path,key,delta):
 z=dict(np.load(path));a=z[key].copy();a.flat[0]+=delta;z[key]=a;np.savez_compressed(path,**z)
def main():
 root=HERE/'negative_fixtures';root.mkdir(exist_ok=True);results=[]
 for name in ['controlled_mass','master_cost','decoder_normalization','cached_witness']:
  dest=root/name
  if dest.exists():raise ValueError('Refuse replace negative fixture')
  shutil.copytree(HERE/'tiny'/'uniform',dest)
  if name=='controlled_mass':alter_npz(dest/'inputs.npz','raw',.01)
  elif name=='master_cost':alter_npz(next(dest.glob('iteration_*/master.npz')),'cost',.01)
  elif name=='decoder_normalization':alter_npz(dest/'selected_decoders.npz','witness_0_decoder',.01)
  else:
   p=dest/'witness_store.json';d=json.loads(p.read_text());d[next(iter(d))]['alpha'][0]+=.01;p.write_text(json.dumps(d))
  try:audit(dest)
  except Exception as exc:results.append({'test':name,'status':'rejected_as_expected','error':repr(exc)})
  else:raise AssertionError(name+' corruption accepted')
 (HERE/'NEGATIVE_AUDIT_CHECKS.json').write_text(json.dumps({'status':'passed','checks':results},indent=2)+'\n');print('passed',len(results))
if __name__=='__main__':main()
