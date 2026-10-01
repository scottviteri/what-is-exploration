"""Wait for the recovery CPU allocation, then execute the authorized extension."""
from common import *
import subprocess,time,signal,shutil
from datetime import datetime,timezone
state=dict(status='waiting_for_recovery',pid=os.getpid(),created_utc=datetime.now(timezone.utc).isoformat())
write(HERE/'EXTENSION_EXECUTION.json',state)
while True:
    q=json.loads((HERE/'recovery_results/queue.json').read_text())
    if q['status']=='finished':break
    if q['status'] not in ['running']:
        state.update(status='blocked_by_recovery',recovery_status=q['status']);write(HERE/'EXTENSION_EXECUTION.json',state);raise SystemExit(1)
    time.sleep(15)
cmd=[sys.executable,str(HERE/'run_extension_queue.py'),str(HERE/'near_optimal_manifest.json'),'--output',str(HERE/'near_optimal_results')]
with (HERE/'near_optimal_supervisor.log').open('w') as log:
    proc=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,start_new_session=True,stdin=subprocess.DEVNULL)
    state.update(status='running',worker_supervisor_pid=proc.pid,started_utc=datetime.now(timezone.utc).isoformat(),command=cmd);write(HERE/'EXTENSION_EXECUTION.json',state)
    while proc.poll() is None:
        used=sum(p.stat().st_size for p in (HERE/'near_optimal_results').rglob('*') if p.is_file())
        if used>6*1024**3 or shutil.disk_usage(HERE).free<15*1024**3:
            state['stop_reason']='disk_or_output_limit';os.killpg(proc.pid,signal.SIGTERM);proc.wait(timeout=30);break
        time.sleep(15)
state.update(status='finished' if proc.returncode==0 else 'failed',returncode=proc.returncode,finished_utc=datetime.now(timezone.utc).isoformat())
write(HERE/'EXTENSION_EXECUTION.json',state)
