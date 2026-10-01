"""Freeze then execute the complete post-design same-time order diagnostic once."""
import os
for key in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS', 'NUMEXPR_NUM_THREADS'):
    os.environ[key] = '1'
os.environ['CUDA_VISIBLE_DEVICES'] = ''
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import argparse
import collections
import subprocess
import time
import traceback
from common import (HERE, STUDY, BACKEND, METHODS, BASELINES, CPU, CAP, MARGIN,
                    csv_write, design, now, pair_classification, read, require, sha, unchanged, write)
sys.path.insert(0, str(STUDY))
from checked_summary import checked_summary
execution_created = False

def prepare():
    path = HERE / 'PLAN.json'; require(not path.exists(), 'The frozen plan already exists')
    queue = read(STUDY / 'QUEUE.json'); models = [m['id'] for m in queue['models']]
    require(len(models) == len(set(models)) == 12, 'Expected all 12 original models')
    sources = [HERE/n for n in ('run.py', 'worker.py', 'check.py', 'common.py', 'tests.py', 'PROTOCOL.md')]
    sources += [STUDY / 'checked_summary.py']
    sources += [BACKEND/n for n in ('certified_decoder.py', 'fast_decoder.py', 'scaling_core.py')]
    jobs = design(models); require(len(jobs) == 288, 'Wrong grid size')
    doc = dict(created_utc=now(), post_design=True, models=models, jobs=jobs,
               source_sha256={str(p):sha(p) for p in sources},
               design_input_sha256={str(STUDY/n):sha(STUDY/n) for n in ('QUEUE.json', 'MODELS.json')},
               cpu=CPU, niceness_minimum=10, process_wall_cap_seconds=CAP,
               scope='Same-time length-three experiments only; 40-second saved policies; no eventual-order claim')
    write(path, doc); return doc

def primary_comparison(a, b):
    if not (a['comparison_eligible'] and b['comparison_eligible']):
        return dict(native_audit_classification='unavailable', native_audit_difference_lower=None,
                    native_audit_difference_upper=None)
    lo, hi = a['audit_lower']-b['audit_upper'], a['audit_upper']-b['audit_lower']
    classification = 'native_win' if hi < -MARGIN else 'native_loss' if lo > MARGIN else 'unresolved'
    return dict(native_audit_classification=classification, native_audit_difference_lower=lo,
                native_audit_difference_upper=hi)

def endpoint_paths(row, frozen):
    require(row.get('available_seconds') is not None and row['available_seconds'] <= 40, 'Missing or late policy')
    require(row.get('planning_check_status') == 'passed', 'Planning validation did not pass')
    policy = Path(row['policy_path']).resolve()
    check = STUDY / 'runs' / row['model'] / row['arm'] / 'PLANNING_CHECK.json'
    paths = (policy, policy.with_suffix('.json'), check)
    for path in paths:
        require(str(path) in frozen and path.is_file() and sha(path) == frozen[str(path)], 'Unbound endpoint: ' + str(path))
    require(read(check)['status'] == 'passed', 'Bound planning check failed')
    return policy, {str(p):frozen[str(p)] for p in paths}

def render(rows, pairs):
    counts = collections.Counter(r['status'] for r in rows)
    lines = ['# Post-design same-time experiment-order diagnostic', '',
             'All 288 requested directions and 144 pairs are retained. Direction status counts: '+str(dict(counts))+'.', '',
             'Each entry compares saved length-three experiments from the 40-second planning row. The LP optimizes only a decoder. Lower deficiency is better.', '',
             'A positive lower above 1e-6 in both directions is numerical evidence of same-time incomparability. Approximate simulation uses an upper at most 2e-7; it establishes neither exact zero nor exact dominance. These floating-point bounds are not outward-rounded certificates. No eventual exploration or process-order claim follows.', '',
             '| Native method | Baseline | Numerical incomparability | Mutual approximate simulation | Native approximate simulation, reverse separated | Baseline approximate simulation, reverse separated | Unresolved | Unavailable |',
             '| --- | --- | --- | --- | --- | --- | --- | --- |']
    categories = ['numerical_incomparability', 'mutual_approximate_simulation',
                  'native_approximate_simulation_reverse_separated', 'baseline_approximate_simulation_reverse_separated',
                  'unresolved', 'unavailable']
    for method in METHODS:
        for baseline in BASELINES:
            c = collections.Counter(p['classification'] for p in pairs if p['method']==method and p['baseline']==baseline)
            lines.append('| '+method+' | '+baseline+' | '+' | '.join(str(c[k]) for k in categories)+' |')
    lines += ['', '## Relation to the original scalar native audit', '',
              'The following joins use every original comparison; they do not select the LP grid. A scalar native-audit win can coexist with same-time incomparability.', '',
              '| Original native-audit comparison | Incomparability | Other resolved approximate relation | Unresolved | Unavailable |',
              '| --- | --- | --- | --- | --- |']
    for result in ('native_win', 'native_loss', 'unresolved', 'unavailable'):
        selected = [p for p in pairs if p['native_audit_classification']==result]
        c = collections.Counter(p['classification'] for p in selected)
        approximate = sum(c[k] for k in categories[1:4])
        lines.append(f'| {result} | {c[categories[0]]} | {approximate} | {c["unresolved"]} | {c["unavailable"]} |')
    lines += ['', 'Twelve model settings share two independent seed families; these are descriptive counts, not significance tests or independent replication counts.', '',
              '[All directions](DIRECTIONS.csv), [all paired outcomes](PAIRS.csv), [independent replay](CHECKS.json), and [full machine-readable record](SUMMARY.json). Failures and timeouts are retained with their logs and reasons.', '']
    return '\n'.join(lines)

def run(wait):
    global execution_created
    plan_path = HERE/'PLAN.json'; plan = read(plan_path)
    unchanged(plan['source_sha256']); unchanged(plan['design_input_sha256'])
    require(CPU in os.sched_getaffinity(0), 'CPU25 unavailable')
    os.sched_setaffinity(0, {CPU})
    if os.nice(0) < 10: os.nice(10 - os.nice(0))
    execution = dict(started_utc=now(), state='waiting_for_primary', plan_sha256=sha(plan_path),
                     cpu=CPU, niceness=os.nice(0), planned_directions=288, completed_directions=0)
    require(not (HERE/'EXECUTION.json').exists(), 'Execution record exists; no automatic rerun')
    write(HERE/'EXECUTION.json', execution)
    execution_created = True
    primary_path = STUDY/'ANALYSIS_EXECUTION.json'
    while True:
        primary = read(primary_path)
        if primary['state'] == 'passed': break
        require(wait and primary['state'] in ('waiting_for_complete_audit_queue', 'reporting'),
                'Primary analysis has not passed: '+primary['state'])
        time.sleep(45)
    unchanged(plan['source_sha256']); unchanged(plan['design_input_sha256'])
    report, bound = checked_summary(STUDY/'summary/summary.json')
    frozen = report['metadata']['input_sha256']
    all_bindings = {**bound, **plan['source_sha256'], **plan['design_input_sha256'],
                    str(plan_path):execution['plan_sha256'], str(primary_path):sha(primary_path)}
    inventory_path = STUDY/'MODELS.json'; inventory = read(inventory_path)
    model_index = {m['id']:m for m in inventory['models']}
    require(set(model_index)==set(plan['models']), 'Model grid changed')
    index = {(r['model'],r['method'],r['budget_seconds']):r for r in report['endpoints']}
    out = HERE/'results'; out.mkdir(exist_ok=False); (out/'jobs').mkdir()
    from check import check_job, check_results
    rows = []; started = time.perf_counter()
    execution.update(state='running', numerical_started_utc=now()); write(HERE/'EXECUTION.json', execution)
    for job in plan['jobs']:
        row = dict(job, status='input_unavailable', error=None)
        jobfolder = out/'jobs'/job['job_id']; jobfolder.mkdir()
        try:
            native = index[job['model'],job['method'],40]; baseline = index[job['model'],job['baseline'],40]
            row.update(primary_comparison(native,baseline), native_endpoint_status=native['endpoint_status'], baseline_endpoint_status=baseline['endpoint_status'])
            pa, ba = endpoint_paths(native,frozen); pb, bb = endpoint_paths(baseline,frozen)
            model = model_index[job['model']]; model_path = Path(model['path'])
            model_path = (model_path if model_path.is_absolute() else STUDY/model_path).resolve()
            require(str(model_path) in frozen and frozen[str(model_path)]==model['sha256']==sha(model_path), 'Model binding mismatch')
            bindings = {**all_bindings, **ba, **bb, str(model_path):model['sha256']}
            source, target = (pa,pb) if job['direction']=='native_to_baseline' else (pb,pa)
            request = dict(job, model_path=str(model_path), source_policy=str(source), target_policy=str(target),
                           primary_execution=str(primary_path), input_sha256=bindings)
            write(jobfolder/'request.json',request); row['request_sha256']=sha(jobfolder/'request.json')
            before = time.perf_counter()
            try:
                with (jobfolder/'worker.log').open('w') as log:
                    child = subprocess.run([sys.executable,str(HERE/'worker.py'),'--job',str(jobfolder)],
                                           stdout=log,stderr=subprocess.STDOUT,timeout=CAP)
                row.update(worker_exit=child.returncode, worker_seconds=time.perf_counter()-before)
                if child.returncode:
                    row.update(status='lp_failed',error=read(jobfolder/'failure.json').get('error') if (jobfolder/'failure.json').exists() else 'Worker exited without a witness')
                else:
                    row['status']='validation_failed'
                    validated=check_job(jobfolder); write(jobfolder/'validation.json',validated); row.update(validated)
            except subprocess.TimeoutExpired:
                row.update(status='lp_timeout',error='30-second worker wall cap',worker_seconds=time.perf_counter()-before)
            all_bindings.update(ba); all_bindings.update(bb); all_bindings[str(model_path)]=model['sha256']
        except Exception as error:
            row['error']=repr(error)
            write(jobfolder/'driver_failure.json',dict(error=repr(error),traceback=traceback.format_exc()))
        rows.append(row); write(jobfolder/'result.json',row)
        execution.update(completed_directions=len(rows),status_counts=dict(collections.Counter(r['status'] for r in rows)))
        write(HERE/'EXECUTION.json',execution)
    require(len(rows)==288, 'Lost requested directions')
    pairs=[]
    for i in range(0,len(rows),2):
        f,r=rows[i:i+2]
        a=index[f['model'],f['method'],40]; b=index[f['model'],f['baseline'],40]
        pairs.append(dict(model=f['model'],method=f['method'],baseline=f['baseline'],budget_seconds=40,
                          forward_job=f['job_id'],reverse_job=r['job_id'],classification=pair_classification(f,r),
                          forward_lower=f.get('lower'),forward_upper=f.get('upper'),reverse_lower=r.get('lower'),reverse_upper=r.get('upper'),
                          **primary_comparison(a,b)))
    unchanged(all_bindings)
    summary=dict(created_utc=now(),post_design=True,input_sha256=all_bindings,directions=rows,pairs=pairs,
                 seconds=time.perf_counter()-started,status_counts=dict(collections.Counter(r['status'] for r in rows)),
                 interpretation='Same-time length-three experiments only; numerical brackets, no exact dominance or eventual order')
    write(out/'SUMMARY.json',summary); csv_write(out/'DIRECTIONS.csv',rows); csv_write(out/'PAIRS.csv',pairs)
    checked=check_results(out); write(out/'CHECKS.json',checked)
    (out/'REPORT.md').write_text(render(rows,pairs))
    write(out/'FILES.json',{str(p.relative_to(out)):sha(p) for p in out.rglob('*') if p.is_file() and p.name!='FILES.json'})
    execution.update(state='passed' if checked['status']=='passed' else 'failed',finished_utc=now(),seconds=summary['seconds'])
    write(HERE/'EXECUTION.json',execution)
    print({k:execution[k] for k in ('state','completed_directions','status_counts','seconds')})
    return 0 if checked['status']=='passed' else 1

if __name__=='__main__':
    parser=argparse.ArgumentParser(); group=parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--prepare',action='store_true'); group.add_argument('--run',action='store_true'); parser.add_argument('--wait',action='store_true')
    args=parser.parse_args()
    if args.prepare:
        result=prepare(); print({'prepared_jobs':len(result['jobs']),'plan':str(HERE/'PLAN.json')})
    else:
        try:
            raise SystemExit(run(args.wait))
        except Exception as error:
            if execution_created:
                path=HERE/'EXECUTION.json'; record=read(path)
                record.update(state='blocked',error=repr(error),finished_utc=now()); write(path,record)
            raise
