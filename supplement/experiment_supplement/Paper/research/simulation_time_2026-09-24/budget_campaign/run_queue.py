"""Single-worker, guarded staged campaign; only owns its child process groups."""
from io_utils import *
import subprocess,signal,time,shutil,resource,csv
PYTHON='/tmp/exploration-lp-gpu-venv/bin/python'

def main():
    source_hash=verify_sources();m=json.loads((HERE/'MANIFEST.json').read_text());start=time.monotonic();records=[];active=None;phase='initializing'
    def update(status='running'):
        counts={}
        for r in records:counts[r['status']]=counts.get(r['status'],0)+1
        write(HERE/'STATUS.json',dict(status=status,updated_utc=now(),started_utc=started,supervisor_pid=os.getpid(),sources_sha256=source_hash,manifest_sha256=sha(HERE/'MANIFEST.json'),phase=phase,active=active,elapsed_seconds=time.monotonic()-start,planned=len(m['jobs']),finished=len(records),pending=len(m['jobs'])-len(records),counts=counts,records=records,compatibility_status='registered; not launched; wrapper and dedicated validation pending'))
        lines=['# Campaign status','',f'Status: {status}. Finished {len(records)} of {len(m["jobs"])} primary jobs. Counts: {counts}.',f'Active: {active}. Elapsed seconds: {time.monotonic()-start:.1f}.','', 'Three-step rows replay frozen references; longer rows are independently planned collectors. Numerical certificate checks do not establish all-optima or eventual behavior.','', 'Compatibility diagnostics are registered but not launched.']
        (HERE/'STATUS.md').write_text('\n'.join(lines)+'\n')
    def allowed(j):
        if j['phase']=='reference_replay':return True,''
        if any(r['status']!='passed' for r in records if r['phase']=='reference_replay'):return False,'a reference replay/check failed'
        if j['phase']=='pilot_h4':return True,''
        priorphase={'pilot_h5':'pilot_h4','expanded_h4':'pilot_h4','expanded_h5':'pilot_h5'}[j['phase']]
        rs=[r for r in records if r['phase']==priorphase and r['method']==j['method']]
        n=sum(r['status']=='passed' for r in rs)
        need=1 if j['phase']=='expanded_h4' else 4
        return n>=need,f'{priorphase} accepted {n}/{need} required'
    def run_child(cmd,log,seconds):
        def limits():
            os.sched_setaffinity(0,{m['cpu']});resource.setrlimit(resource.RLIMIT_AS,(m['address_space_gib']*1024**3,)*2)
        with log.open('w') as f:
            child=subprocess.Popen(cmd,cwd=str(HERE),stdout=f,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=limits)
            ts=time.monotonic();last=0
            while child.poll() is None:
                elapsed=time.monotonic()-ts
                if (HERE/'STOP').exists() or time.monotonic()-start>=m['wall_seconds'] or elapsed>seconds:
                    os.killpg(child.pid,signal.SIGTERM)
                    try:child.wait(timeout=5)
                    except subprocess.TimeoutExpired:os.killpg(child.pid,signal.SIGKILL);child.wait()
                    return dict(code=child.returncode,status='stopped' if (HERE/'STOP').exists() else 'timeout',seconds=elapsed,pid=child.pid)
                if elapsed-last>=15:update();last=elapsed
                time.sleep(.5)
            return dict(code=child.returncode,status='exited',seconds=time.monotonic()-ts,pid=child.pid)
    started=now();write(HERE/'LAUNCH.json',dict(started_utc=started,pid=os.getpid(),cpu=m['cpu'],worker_count=1,wall_seconds=m['wall_seconds'],source_hash=source_hash));update()
    try:
        for j in m['jobs']:
            if time.monotonic()-start>=m['wall_seconds'] or (HERE/'STOP').exists():break
            if shutil.disk_usage(HERE).free<m['disk_reserve_gib']*1024**3:phase='disk_reserve';break
            used=sum(p.stat().st_size for p in (HERE/'results').rglob('*') if p.is_file()) if (HERE/'results').exists() else 0
            if used>m['output_cap_gib']*1024**3:phase='output_cap';break
            verify_sources();phase=j['phase'];ok,reason=allowed(j)
            if not ok:records.append(dict(id=j['id'],phase=j['phase'],method=j['method'],status='skipped_feasibility_gate',reason=reason));update();continue
            out=HERE/'results'/j['id'];assert not out.exists(),('Refusing overwrite',str(out));out.parent.mkdir(exist_ok=True)
            active=dict(id=j['id'],case=j['case'],method=j['method'],t=j['t'],stage='worker');update()
            execution=run_child([PYTHON,str(HERE/'worker.py'),'--job',j['id']],out.parent/(j['id']+'.log'),j['job_seconds'])
            rec=dict(id=j['id'],case=j['case'],t=j['t'],phase=j['phase'],method=j['method'],execution=execution,status='failed')
            rp=out/'result.json'
            if rp.exists():
                r=json.loads(rp.read_text());rec.update(result_status=r['status'],result=str(rp.relative_to(HERE)),planning_seconds=r.get('planning_elapsed_seconds'),peak_rss_mib=r.get('peak_rss_mib'))
                if r['status'] in ['complete','incomplete_optimization']:
                    active['stage']='independent_check';update();ck=run_child([PYTHON,str(HERE/'check.py'),str(out)],out/'check.log',300);rec['check_execution']=ck
                    cp=out/'CHECK.json'
                    if cp.exists():
                        c=json.loads(cp.read_text());rec['check_status']=c['status']
                        if c['status']=='passed':rec['status']='passed' if r['planning_certified'] else 'incomplete_optimization'
            if execution['status']!='exited':rec['status']=execution['status']
            records.append(rec);active=None;update()
        phase='finished';active=None
        update('complete' if len(records)==len(m['jobs']) else 'stopped_or_budget_exhausted')
    except Exception as e:
        phase='supervisor_error';active=None;records.append(dict(id='supervisor',phase=phase,method='none',status='failed',error=repr(e)));update('failed');raise
    finally:
        rows=[]
        for rr in records:
            if rr['status'] not in ['passed','incomplete_optimization']:continue
            r=json.loads((HERE/rr['result']).read_text())
            for a in r['audits']:
                rows.append(dict(case=r['spec']['case'],method=r['spec']['method'],t=r['spec']['t'],reference=a['reference'],lower=a['lower'],upper=a['upper'],planning_certified=r['planning_certified'],planning_seconds=r['planning_elapsed_seconds'],**{'at_'+k:v for k,v in a['classification'].items()}))
        if rows:
            with (HERE/'comparisons.csv').open('w') as f:w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
if __name__=='__main__':main()
