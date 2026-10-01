#!/usr/bin/env python3
"""Account for every registered attempt and compare certified objective intervals."""
from pathlib import Path
import collections,csv,hashlib,json,statistics,time
HERE=Path(__file__).resolve().parent;ROOT=next(p for p in HERE.parents if (p/'AGENTS.md').exists());TOL=1e-6

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 q=json.loads((HERE/'QUEUE.json').read_text());rows=[];missing=[];failed=[];paired=[];changed=[];source_errors=[];identity_corrections=[]
 for name,h in q['source_hashes'].items():
  if sha(HERE/name)!=h:source_errors.append(name)
 for i,c in enumerate(q['cells']):
  found={}
  for method in c['methods']:
   stages=['uniform_initial','increasing' if method.endswith('increasing') else 'decreasing','uniform_final'] if method in ['bridge_increasing','bridge_decreasing'] else ['uniform']
   for stage in stages:
    p=HERE/'runs'/f'case_{i:03d}'/method/stage
    if not (p/'result.json').exists() or not (p/'audit.json').exists():missing.append({'index':i,'method':method,'stage':stage});continue
    r=json.loads((p/'result.json').read_text());a=json.loads((p/'audit.json').read_text());meta=json.loads((p/'metadata.json').read_text());policy=p/'policy.npz'
    signature={'kind':c['kind'],'model_sha256':sha(ROOT/c['model_path']),'t':c['t'],'n':c['n'],'target_indices':c['target_indices'],'weights':meta['weights'] if c['kind']=='native_weighted' else None,'policy_family':'all randomized full-history policies','decoder':'world-independent stochastic'}
    scientific_id=hashlib.sha256(json.dumps(signature,sort_keys=True,separators=(',',':')).encode()).hexdigest()
    if c['kind']=='native_minimax':identity_corrections.append({'path':str(p.relative_to(ROOT)),'raw_incorrect_weighted_id':meta.get('objective_id'),'corrected_scientific_objective_id':scientific_id,'signature':signature})
    row={k:c[k] for k in ['case','t','n','K','kind','repeat']};row.update(index=i,method=method,stage=stage,status=r['status'],audit_status=a['status'],lower=a.get('lower'),upper=a.get('upper'),gap=a.get('gap'),seconds=r.get('seconds'),export_seconds=r.get('export_seconds'),independent_audit_seconds=a.get('seconds'),policy_sha256=sha(policy) if policy.exists() else None,objective_id=scientific_id,raw_metadata_objective_id=meta.get('objective_id'),path=str(p.relative_to(ROOT)))
    rows.append(row);found[(method,stage)]=row
    if r['status'] not in ['passed','converged','converged_numerically'] or a['status']!='passed':failed.append(row)
  comparisons=[(('decomposition','uniform'),('monolithic','uniform'))]
  if c['kind']=='native_weighted':comparisons += [(('bridge_cold','uniform'),('decomposition','uniform')),(('bridge_increasing','uniform_final'),('bridge_cold','uniform')),(('bridge_decreasing','uniform_final'),('bridge_cold','uniform'))]
  for left,right in comparisons:
   a,b=found.get(left),found.get(right)
   if not a or not b or any(x['upper'] is None or x['audit_status']!='passed' or x['status'] not in ['passed','converged','converged_numerically'] for x in [a,b]):continue
   overlap=max(a['lower'],b['lower'])<=min(a['upper'],b['upper'])+TOL
   record={'index':i,'left':'/'.join(left),'right':'/'.join(right),'interval_overlap_within_tolerance':overlap,'upper_difference':a['upper']-b['upper'],'left_seconds':a['seconds'],'right_seconds':b['seconds'],'policy_hashes_differ':a['policy_sha256']!=b['policy_sha256']}
   paired.append(record)
   if record['policy_hashes_differ']:changed.append(record)
 # Bind all model files back to the original archived identity recorded before this study.
 old=ROOT/'Paper/research/target_selection_2026-09-23/decomposition_research'
 for source in csv.DictReader((old/'SUMMARY.csv').open()):
  key=f"{source['case']}__t{source['t']}n{source['n']}K{source['K']}__{source['objective']}";r=json.loads((old/source['run']/key/'comparison.json').read_text());path=ROOT/f"Paper/research/native_objective_benchmark_2026-09-15/results/{source['case']}/model.npz"
  if sha(path)!=r['input_sha256']:source_errors.append(str(path))
 with (HERE/'RESULTS.csv').open('w',newline='') as f:
  if rows:w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
 timing=[]
 for case in q['cells'][:16]:
  groups={method:[r['seconds'] for r in rows if all(r[k]==case[k] for k in ['case','t','n','K','kind']) and r['method']==method and r['stage']=='uniform' and r['status'] in ['passed','converged','converged_numerically']] for method in ['monolithic','decomposition','bridge_cold']}
  timing.append({k:case[k] for k in ['case','t','n','K','kind']}|{m:{'completed':len(v),'median_seconds':statistics.median(v) if v else None} for m,v in groups.items()})
 out={'status':'passed' if not source_errors and not missing and all(r['audit_status']=='passed' for r in rows) and all(p['interval_overlap_within_tolerance'] for p in paired) else 'incomplete_or_failed',
  'registered_cells':48,'expected_method_processes':177,'expected_endpoints':285,'recorded_endpoints':len(rows),'outcome_counts':dict(collections.Counter(r['status'] for r in rows)),
  'audit_counts':dict(collections.Counter(r['audit_status'] for r in rows)),'failed_or_incomplete_endpoints':failed,'missing_endpoints':missing,'source_errors':source_errors,'objective_comparisons':paired,'selection_differences':changed,'timing_medians':timing,
  'scope':'Numerical finite-objective backend agreement. No depth-four scientific audit or optimizer-set characterization in Track A.'}
 (HERE/'OBJECTIVE_ID_CORRECTION.json').write_text(json.dumps({'issue':'Original minimax worker metadata reused weighted score identity; actual matrices/objective kind were correct. Raw artifacts preserved; derived analysis now uses explicit kind-bound scientific identity for every arm.','corrections':identity_corrections},indent=2)+'\n')
 (HERE/'ANALYSIS.json').write_text(json.dumps(out,indent=2)+'\n');print({k:out[k] for k in ['status','recorded_endpoints','outcome_counts','audit_counts','source_errors']})
if __name__=='__main__':main()
