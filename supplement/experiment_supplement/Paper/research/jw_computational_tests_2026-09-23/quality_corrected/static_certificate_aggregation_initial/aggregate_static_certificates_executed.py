#!/usr/bin/env python3
"""Aggregate already checked in-budget lower bounds for unchanged objectives.
No optimization, policy changes, stronger numerical tolerance, or primary edits.
Original exported gaps remain visible; moving-weight methods are excluded.
"""
from pathlib import Path
import csv,datetime,hashlib,json,time
from checked_summary import checked_summary,verify_unchanged
HERE=Path(__file__).resolve().parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    started=time.perf_counter();out=HERE/'static_certificate_aggregation';out.mkdir(exist_ok=False)
    report,bindings=checked_summary(HERE/'summary/summary.json')
    aq=HERE/'exhaustive_audits/AUDIT_QUEUE.json';bindings[str(aq)]=sha(aq)
    frozen=json.loads(aq.read_text())['frozen_files'];rows=[]
    def bound_json(p,expected):
        raw=p.read_bytes();assert hashlib.sha256(raw).hexdigest()==expected,str(p)
        bindings[str(p)]=expected;return json.loads(raw)
    for row in report['endpoints']:
        method=row['method']
        if method not in ['fixed','minimax'] and '_face' not in method:continue
        folder=HERE/'runs'/row['model']/method;budget=row['budget_seconds']
        manifest_path=folder/'FILES.json';manifest=bound_json(manifest_path,frozen[str(manifest_path)])
        check_path=folder/'PLANNING_CHECK.json';check=bound_json(check_path,frozen[str(check_path)]);assert check['status']=='passed'
        meta=bound_json(folder/'metadata.json',manifest['metadata.json'])
        assert meta['arm']==method
        accepted=[]
        for name,h in sorted(manifest.items()):
            if not name.startswith('round_') or not name.endswith('/record.json'):continue
            r=bound_json(folder/name,h)
            if 'error' not in r and 'lower' in r and 'upper' in r and r.get('available_seconds',float('inf'))<=40:
                accepted.append(r)
        assert len(accepted)==check['accepted_rounds'],(method,row['model'],'accepted-round count')
        assert len({tuple(x['weights']) for x in accepted})==1,'Static weights changed'
        eligible=[x for x in accepted if x['available_seconds']<=budget];assert eligible
        chosen=next(x for x in eligible if x['iteration']==row['iteration'])
        assert abs(chosen['upper']-row['selected_upper'])<=2e-7 and abs(chosen['lower']-row['selected_lower'])<=2e-7
        strongest=max(eligible,key=lambda x:x['lower']);lo=strongest['lower'];upper=row['selected_upper']
        assert lo+2e-7>=row['selected_lower'] and lo<=upper+2e-7
        rows.append({'model':row['model'],'method':method,'budget_seconds':budget,'incumbent_iteration':row['iteration'],
          'incumbent_available_seconds':row['available_seconds'],'original_selected_lower':row['selected_lower'],
          'selected_upper':upper,'original_exported_gap':row['selected_gap'],'strongest_timely_lower':lo,
          'lower_bound_iteration':strongest['iteration'],'lower_bound_available_seconds':strongest['available_seconds'],
          'combined_certificate_available_seconds':max(row['available_seconds'],strongest['available_seconds']),
          'aggregated_gap_raw':upper-lo,'aggregated_gap_upper':max(0.,upper-lo),'eligible_rounds':len(eligible)})
    assert len(rows)==288
    verify_unchanged(bindings)
    with (out/'certificates.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)
    text=['# Static in-budget certificate aggregation','',
      'The exported checkpoint attaches the lower bound available when its best incumbent was first found. The stopping rule can use a stronger later lower bound for the same unchanged objective. Thus a large exported gap alone does not show that the static solver failed to converge.', '',
      'This post-design calculation aggregates all already checked, fully audited rounds available by each original budget for all eight static methods. It performs no optimization and changes no policy, reward face, budget, target, numerical witness or comparison. Adaptive moving-weight methods are excluded. Original exported gaps are retained.', '',
      'Record hashes are bound through the original FILES manifest in the frozen audit queue, and the passing independent PLANNING_CHECK covers their LP bounds. This is aggregation of previously checked numerical evidence, not new exact arithmetic or a new numerical LP replay. Both original and combined evidence-availability times remain visible.', '',
      '| Method | Budget | Count | Largest exported gap | Largest aggregated gap |','| --- | ---: | ---: | ---: | ---: |']
    for method in sorted({r['method'] for r in rows}):
        for budget in [2,10,40]:
            subset=[r for r in rows if r['method']==method and r['budget_seconds']==budget]
            text.append(f"| {method} | {budget} | {len(subset)} | {max(r['original_exported_gap'] for r in subset):.8g} | {max(r['aggregated_gap_upper'] for r in subset):.8g} |")
    text+=['','These are numerical upper bounds on finite training-objective regret. Small gap does not characterize every optimizer or guarantee eventual exploration. No bound is backdated to the earlier incumbent-availability time.','']
    (out/'README.md').write_text('\n'.join(text))
    doc={'status':'passed','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'post_design':True,'rows':rows,'row_count':len(rows),
      'source_sha256':{str(Path(__file__).resolve()):sha(Path(__file__))},'input_sha256':bindings,'additional_aggregation_seconds':time.perf_counter()-started,
      'scope':'Same fixed finite objective only, strongest already audited lower bound available by each budget. No new optimization or primary endpoint change.'}
    (out/'CHECKS.json').write_text(json.dumps(doc,indent=2,allow_nan=False)+'\n')
    print(json.dumps({'status':'passed','row_count':len(rows),'maximum_40s_aggregated_gap':max(r['aggregated_gap_upper'] for r in rows if r['budget_seconds']==40)}))
if __name__=='__main__':main()
