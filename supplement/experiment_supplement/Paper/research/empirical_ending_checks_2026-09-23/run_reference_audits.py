"""Full-witness replays of the fixed native references used by reward matching."""
import json,os,subprocess,time,concurrent.futures
from pathlib import Path
HERE=Path(__file__).resolve().parent;M=json.loads((HERE/'matched_manifest.json').read_text());PYTHON='/tmp/exploration-lp-gpu-venv/bin/python';done=[];start=time.monotonic()
def chain(slot):
    result=[]
    for x in M['thresholds'][slot::3]:
        cell=x['id'];source=Path(x['reference_policy']).parents[1];out=HERE/'reference_audits'/cell
        with (HERE/(cell+'_reference.log')).open('a') as f:
            p=subprocess.run(['prlimit','--as=5368709120','--','taskset','-c',str(slot),PYTHON,str(HERE/'audit.py'),'--source',str(source),'--output',str(out),'--seconds','2400'],stdout=f,stderr=subprocess.STDOUT,timeout=2550)
        result.append(dict(id=cell,source=str(source),exit_code=p.returncode));path=HERE/f'reference_chain_{slot}.json';path.write_text(json.dumps(result,indent=2)+'\n')
    return result
with concurrent.futures.ThreadPoolExecutor(3) as pool:
    for result in pool.map(chain,range(3)):done+=result
(HERE/'REFERENCE_QUEUE.json').write_text(json.dumps(dict(status='complete' if all(x['exit_code']==0 for x in done) else 'issues',jobs=done,seconds=time.monotonic()-start),indent=2)+'\n')
