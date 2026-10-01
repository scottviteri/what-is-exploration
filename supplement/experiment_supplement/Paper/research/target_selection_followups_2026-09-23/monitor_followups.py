"""Finish validation and maintain combined summaries without further optimization."""
from common import *
from summarize import summarize
import subprocess,time
from datetime import datetime,timezone
state=dict(status='running',pid=os.getpid(),started_utc=datetime.now(timezone.utc).isoformat());write(HERE/'MONITOR.json',state)
while True:
    q=json.loads((HERE/'completion_results/queue.json').read_text())
    if q['status']!='running' and not (HERE/'completion_audit/SUMMARY.json').exists():
        cmd=[sys.executable,str(HERE/'audit_completion.py'),'--output',str(HERE/'completion_audit')]
        with (HERE/'completion_audit.log').open('w') as log:
            run=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,timeout=300)
        state['completion_audit_returncode']=run.returncode;write(HERE/'MONITOR.json',state)
    summary=summarize()
    near=summary['queues']['near_optimal_results'];rec=summary['queues']['recovery_results'];comp=summary['queues']['completion_results']
    if near and near['status']!='running' and rec and rec['status']!='running' and comp and comp['status']!='running':break
    dispatch=json.loads((HERE/'EXTENSION_EXECUTION.json').read_text())
    if dispatch['status'] in ['failed','blocked_by_recovery']:
        state['extension_dispatch_status']=dispatch['status'];break
    time.sleep(30)
state.update(status='finished',finished_utc=datetime.now(timezone.utc).isoformat());write(HERE/'MONITOR.json',state)
