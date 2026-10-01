#!/usr/bin/env python3
"""Bind this completed computational study, including preserved failed attempts.
This is a local evidence inventory, not a commit, publication, or theorem check.
"""
from pathlib import Path
import collections, datetime, hashlib, json, os, time
ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'DELIVERY.json'
def digest(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
    return h.hexdigest()
def read(relative):return json.loads((ROOT/relative).read_text())
def main():
    terminal=read('quality_corrected/ANALYSIS_EXECUTION.json')
    if terminal.get('state')!='passed':raise RuntimeError('Final analysis and checks are not complete')
    supplementary=read('quality_corrected/SUPPLEMENTARY_EXECUTION.json')
    if supplementary.get('state')!='passed':raise RuntimeError('Supplementary checks are not complete')
    refinement=read('quality_corrected/certificate_refinement/results/CERTIFICATES.json')
    faces=read('quality_corrected/reward_face_comparisons/CHECKS.json')
    rewards=read('quality_corrected/reward_diagnostics/results/SUMMARY.json')
    if refinement.get('status')!='passed' or faces.get('status')!='passed':
        raise RuntimeError('A supplementary certificate or comparison check failed')
    if rewards.get('row_count')!=540 or sum(rewards.get('status_counts',{}).values())!=540:
        raise RuntimeError('Scalar reward diagnostics do not account for all endpoints')
    order=read('quality_corrected/same_time_order/results/CHECKS.json')
    order_execution=read('quality_corrected/same_time_order/EXECUTION.json')
    static=read('quality_corrected/static_certificate_aggregation/CHECKS.json')
    resource=read('quality_corrected/RESOURCE_REPORT.json')
    if order.get('status')!='passed' or order_execution.get('state')!='passed' or static.get('status')!='passed':
        raise RuntimeError('Additional diagnostic checks are incomplete')
    if 'recovery_timing_scope_correction' not in resource:
        raise RuntimeError('Resource scope must reflect the recovered queue')
    start=time.perf_counter()
    inventory={}; totals=collections.defaultdict(lambda:{'files':0,'bytes':0})
    for p in sorted(ROOT.rglob('*')):
        if not p.is_file() or p==OUT or '__pycache__' in p.parts or p.suffix in {'.pyc','.tmp'}:continue
        if p.is_symlink():raise RuntimeError(f'Symlink needs explicit inventory treatment: {p}')
        before=p.stat(); rel=str(p.relative_to(ROOT)); h=digest(p); after=p.stat()
        if (before.st_size,before.st_mtime_ns)!=(after.st_size,after.st_mtime_ns):raise RuntimeError(f'File changed during hashing: {p}')
        inventory[rel]={'bytes':after.st_size,'sha256':h}
        group=rel.split('/')[0] if '/' in rel else 'top_level'
        totals[group]['files']+=1;totals[group]['bytes']+=after.st_size
    audit=read('quality_corrected/exhaustive_audits/STATUS.json')
    report=read('quality_corrected/summary/summary.json')['metadata']
    record={'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
      'status':'completed_local_research_snapshot',
      'scope':'Computational and numerical evidence only. No new Lean theorem, manuscript edit, commit, or push. Preserved exploratory/development failures are not accepted evidence.',
      'primary_quality_run':'quality_corrected',
      'preserved_initial_execution':'quality',
      'checks':{'analysis_execution':terminal['state'],'summary_status':report['status'],
        'supplementary_execution':supplementary['state'],
        'certificate_refinement':refinement['status'],
        'reward_face_comparisons':faces['status'],
        'scalar_reward_endpoint_statuses':rewards['status_counts'],
        'same_time_order':order['status'],'validated_directional_LPs':order['validated_directions'],
        'static_certificate_aggregation':static['status'],'static_certificate_rows':static['row_count'],
        'audit_state':audit['state'],'complete_validated_audits':audit.get('successful_complete'),
        'validated_partial_audits':audit.get('validated_partial'),'failed_audits':audit.get('failed'),
        'safe_fast_exact_replay':read('safe_fast/AUDIT.json')['status'],
        'safe_fast_literal_replay':read('safe_fast/LITERAL_AUDIT.json')['status'],
        'backend_checks':read('backend_validation/CHECKS.json')['status'],
        'gpu_witness_replay':read('gpu_audit_pilot/VALIDATION.json')['status']},
      'excluded_generated_files':['__pycache__/**','*.pyc','*.tmp','DELIVERY.json (this inventory)'],
      'totals_by_directory':dict(totals),'total_files':len(inventory),
      'total_bytes':sum(x['bytes'] for x in inventory.values()),
      'largest_files':sorted(({'path':p,**x} for p,x in inventory.items()),key=lambda x:x['bytes'],reverse=True)[:20],
      'hashing_seconds':time.perf_counter()-start,'files':inventory}
    OUT.write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({k:record[k] for k in ['status','total_files','total_bytes','hashing_seconds','checks']},indent=2))
if __name__=='__main__':main()
