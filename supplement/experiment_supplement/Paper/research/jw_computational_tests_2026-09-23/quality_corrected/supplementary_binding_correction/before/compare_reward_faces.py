#!/usr/bin/env python3
"""Complete cross-comparison with the prospectively specified reward-face controls.
The table layout was added after the 40-second preview. This adds no metric,
policy selection, optimization, or exclusions, and retains every budget/model.
"""
from pathlib import Path
from collections import Counter
import csv, datetime, hashlib, json
HERE=Path(__file__).resolve().parent
CORE=('fixed','tractability','hard','minimax')
FACES=tuple(f'{reward}_face{percent}' for reward in ('information','brier') for percent in (0,1,5))
MARGIN=1e-6
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    report_path=HERE/'summary/summary.json';check_path=HERE/'SUMMARY_CHECK.json'
    report=json.loads(report_path.read_text());check=json.loads(check_path.read_text())
    assert report['metadata']['status']=='final_snapshot' and check['status']=='passed'
    rows=report['endpoints'];index={(r['model'],r['method'],r['budget_seconds']):r for r in rows}
    models=[x['id'] for x in report['metadata']['models']];budgets=report['metadata']['budgets'];pairs=[]
    for budget in budgets:
        for model in models:
            for method in CORE:
                for face in FACES:
                    a=index[model,method,budget];b=index[model,face,budget]
                    eligible=a['comparison_eligible'] and b['comparison_eligible']
                    lo=a['audit_lower']-b['audit_upper'] if eligible else None
                    hi=a['audit_upper']-b['audit_lower'] if eligible else None
                    result='unavailable' if not eligible else 'win' if hi < -MARGIN else 'loss' if lo > MARGIN else 'unresolved'
                    pairs.append({'model':model,'method':method,'face':face,'budget_seconds':budget,'classification':result,
                       'difference_lower':lo,'difference_upper':hi,'method_status':a['endpoint_status'],'face_status':b['endpoint_status'],
                       'method_audit':a['audit_id'],'face_audit':b['audit_id'],'margin':MARGIN})
    assert len(pairs)==len(models)*len(budgets)*len(CORE)*len(FACES)
    against_fixed=[]
    for budget in budgets:
        for model in models:
            for method in CORE[1:]:
                a=index[model,method,budget];b=index[model,'fixed',budget]
                eligible=a['comparison_eligible'] and b['comparison_eligible']
                lo=a['audit_lower']-b['audit_upper'] if eligible else None
                hi=a['audit_upper']-b['audit_lower'] if eligible else None
                result='unavailable' if not eligible else 'win' if hi < -MARGIN else 'loss' if lo > MARGIN else 'unresolved'
                against_fixed.append({'model':model,'method':method,'comparator':'fixed','budget_seconds':budget,
                    'classification':result,'difference_lower':lo,'difference_upper':hi,
                    'method_status':a['endpoint_status'],'comparator_status':b['endpoint_status'],
                    'method_audit':a['audit_id'],'comparator_audit':b['audit_id'],'margin':MARGIN})
    assert len(against_fixed)==108
    out=HERE/'reward_face_comparisons';out.mkdir(exist_ok=False)
    with (out/'pairs.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(pairs[0]));w.writeheader();w.writerows(pairs)
    with (out/'against_fixed.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(against_fixed[0]));w.writeheader();w.writerows(against_fixed)
    text=['# Native planners versus all prespecified controls','',
       'These are complete descriptive cross-comparisons of the existing policies, using the same held-out deficiency intervals and 1e-6 separation rule. The table layout was added after the primary 40-second preview. No new metric, optimizer, target, or policy was selected.', '',
       'Entries are wins / losses / unresolved / unavailable for the native method against the named face control; lower deficiency is better. The 12 model settings share two seed families, and budgets reuse evidence. They are not independent replication counts.', '',
       'Face percentages refer to the attainable range of that Bayesian reward. The nominal zero face permits 1e-10 numerical reward slack. These are returned representatives, not a characterization of all exact optima. Selection used training targets; evaluation uses depth-four targets.', '']
    for budget in budgets:
        text += [f'## {budget} seconds','', '| Method | '+' | '.join(FACES)+' |', '| --- | '+' | '.join('---' for _ in FACES)+' |']
        for method in CORE:
            values=[]
            for face in FACES:
                counts=Counter(x['classification'] for x in pairs if x['method']==method and x['face']==face and x['budget_seconds']==budget)
                assert sum(counts.values())==len(models)
                values.append(' / '.join(str(counts[k]) for k in ['win','loss','unresolved','unavailable']))
            text.append('| '+method+' | '+' | '.join(values)+' |')
        text.append('')
    text += ['## Alternate native planners versus fixed weights', '',
       'The same rule compares all three alternatives with the fixed-weight control at every budget. These are capability comparisons under a common planning allowance; a converged fixed objective may stop before the allowance is exhausted.', '',
       '| Method versus fixed | 2 seconds | 10 seconds | 40 seconds |',
       '| --- | --- | --- | --- |']
    for method in CORE[1:]:
        values=[]
        for budget in budgets:
            c=Counter(x['classification'] for x in against_fixed if x['method']==method and x['budget_seconds']==budget)
            assert sum(c.values())==len(models)
            values.append(' / '.join(str(c[k]) for k in ['win','loss','unresolved','unavailable']))
        text.append('| '+method+' | '+' | '.join(values)+' |')
    text += ['', '[All comparisons against fixed weights](against_fixed.csv).', '']
    text += ['[Every paired interval](pairs.csv) preserves every setting, including baseline wins. These scalar comparisons establish no strict native process-order dominance.','']
    (out/'README.md').write_text('\n'.join(text))
    record={'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'passed','pairs':len(pairs),'expected_pairs':864,'against_fixed_pairs':len(against_fixed),
       'source_sha256':sha(Path(__file__)),'input_sha256':{str(p):sha(p) for p in [report_path,check_path]},
       'files':{p.name:sha(p) for p in sorted(out.iterdir()) if p.is_file()}}
    (out/'CHECKS.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({'status':'passed','pairs':len(pairs),'output':str(out)}))
if __name__=='__main__':main()
