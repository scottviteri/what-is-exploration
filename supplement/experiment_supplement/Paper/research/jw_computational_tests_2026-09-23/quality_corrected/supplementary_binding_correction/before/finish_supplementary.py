#!/usr/bin/env python3
"""Run uniform supplementary diagnostics only after the primary report passes."""
from pathlib import Path
import datetime,hashlib,json,os,subprocess,sys,time
HERE=Path(__file__).resolve().parent
CPU_PYTHON='/tmp/exploration-lp-cpu-venv/bin/python'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(record):
    p=HERE/'SUPPLEMENTARY_EXECUTION.json';q=p.with_suffix('.tmp')
    q.write_text(json.dumps(record,indent=2)+'\n');q.replace(p)
def main():
    os.sched_setaffinity(0,{24})
    sources=[Path(__file__),HERE/'certificate_refinement/replay.py',HERE/'reward_diagnostics/diagnose.py',HERE/'compare_reward_faces.py']
    record={'started_utc':now(),'state':'waiting_for_primary_checks','cpu':24,'source_sha256':{str(p):sha(p) for p in sources},'steps':[],
       'scope':'Supplementary uniformly applied certificate and reward diagnostics. No optimization, retries, policy selection, or change to primary comparisons.'}
    save(record)
    while True:
        state=json.loads((HERE/'ANALYSIS_EXECUTION.json').read_text())['state']
        if state not in ['waiting_for_complete_audit_queue','reporting']:break
        time.sleep(45)
    changed=[p for p,h in record['source_sha256'].items() if sha(Path(p))!=h]
    if state!='passed' or changed:
        record.update(state='blocked',primary_state=state,changed_sources=changed,finished_utc=now());save(record);return 2
    commands=[
      [CPU_PYTHON,str(HERE/'certificate_refinement/replay.py'),'--audits',str(HERE/'exhaustive_audits'),'--summary',str(HERE/'summary'),'--output',str(HERE/'certificate_refinement/results'),'--cpu','24'],
      [CPU_PYTHON,str(HERE/'reward_diagnostics/diagnose.py'),'--summary',str(HERE/'summary/summary.json')],
      [sys.executable,str(HERE/'compare_reward_faces.py')],
    ]
    env=os.environ.copy()
    for key in ['OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:env[key]='1'
    record['state']='running';save(record)
    for i,command in enumerate(commands):
        log=HERE/f'supplementary_step_{i}.log';start=time.perf_counter()
        with log.open('w') as stream:
            completed=subprocess.run(command,stdout=stream,stderr=subprocess.STDOUT,env=env)
        record['steps'].append({'command':command,'exit':completed.returncode,'wall_seconds':time.perf_counter()-start,'log':str(log),'log_sha256':sha(log)})
        save(record)
    record.update(state='passed' if all(s['exit']==0 for s in record['steps']) else 'failed',finished_utc=now());save(record)
    print(json.dumps({'state':record['state'],'steps':len(record['steps'])}))
    return 0 if record['state']=='passed' else 1
if __name__=='__main__':raise SystemExit(main())
