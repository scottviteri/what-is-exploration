#!/usr/bin/env python3
"""Wait for the fixed audit queue, then build and independently check its report.
No optimization, selection, retry, or changes to the numerical queue occur here.
"""
from pathlib import Path
import datetime, hashlib, json, os, subprocess, sys, time
HERE = Path(__file__).resolve().parent
AUDITS = HERE / 'exhaustive_audits'
SUMMARY = HERE / 'summary'
SOURCES = [HERE / n for n in ['finish_analysis.py', 'summarize.py', 'REPORT_TEMPLATE.md', 'check_summary.py', 'resource_summary.py']]
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def stamp():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(data):
    p = HERE / 'ANALYSIS_EXECUTION.json'
    temp = p.with_suffix('.tmp')
    temp.write_text(json.dumps(data, indent=2) + '\n')
    temp.replace(p)
def main():
    record = {'started_utc': stamp(), 'state': 'waiting_for_complete_audit_queue',
              'source_sha256': {str(p): sha(p) for p in SOURCES}, 'steps': [],
              'scope': 'Reporting and independent summary validation only; no numerical retries or selection.'}
    save(record)
    while True:
        status = json.loads((AUDITS / 'STATUS.json').read_text())
        if status.get('state') != 'running':
            break
        time.sleep(45)
    record['audit_terminal_state'] = status.get('state')
    changed = [p for p, h in record['source_sha256'].items() if sha(Path(p)) != h]
    if changed or status.get('state') != 'finished':
        record.update(state='blocked', changed_reporting_sources=changed, finished_utc=stamp())
        save(record)
        return 2
    if SUMMARY.exists():
        record.update(state='blocked_existing_summary', finished_utc=stamp())
        save(record)
        return 2
    commands = [
        [sys.executable, str(HERE/'summarize.py'), '--audits', str(AUDITS)],
        [sys.executable, str(HERE/'check_summary.py'), '--audits', str(AUDITS), '--summary', str(SUMMARY), '--output', str(HERE/'SUMMARY_CHECK.json')],
        [sys.executable, str(HERE/'resource_summary.py'), '--output', str(HERE/'RESOURCE_REPORT.json')],
    ]
    env = os.environ.copy()
    for key in ['OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:
        env[key] = '1'
    record['state'] = 'reporting'
    save(record)
    for i, cmd in enumerate(commands):
        log = HERE / f'analysis_step_{i}.log'
        start = time.perf_counter()
        with log.open('w') as f:
            result = subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT, env=env)
        record['steps'].append({'command':cmd, 'exit':result.returncode, 'wall_seconds':time.perf_counter()-start, 'log':str(log), 'log_sha256':sha(log)})
        save(record)
        if result.returncode:
            record.update(state='failed', finished_utc=stamp())
            save(record)
            return result.returncode
    record.update(state='passed', finished_utc=stamp())
    save(record)
    print(json.dumps({'state':record['state'], 'summary':str(SUMMARY), 'steps':len(record['steps'])}))
    return 0
if __name__ == '__main__':
    raise SystemExit(main())
