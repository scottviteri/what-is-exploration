"""Bind complete repairs to the original cohort and calculate transparent summaries."""
import os
for key in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[key]='1'
from pathlib import Path
import json,csv,collections,hashlib,sys
import numpy as np
from diagnostics import HERE,ROOT,OLD,FOLLOW,CAND,reward,core,replay,bellman,fixed_history_scores,digest,write
orig=json.loads((HERE/'REWARD_DIAGNOSTICS.json').read_text());records=orig['records'][:];ids={r['cell'] for r in records};bindings=orig['input_sha256'].copy();inputs={}
def read(p):
    inputs[str(p)]=digest(p);return json.loads(p.read_text())
def add(source,method,au,checkpath):
    r=read(source/'result.json');cp=r['checkpoints'][-1];p=source/f"checkpoint_{cp['k']:03d}"/'policy.npz';m=source/'model.npz';check=read(checkpath);assert check['status']=='passed'
    for pp in [p,m,source/'result.json']:bindings[str(pp)]=digest(pp)
    with np.load(m) as z:T=z['T'];Z=z['Z']
    with np.load(p) as z:E=z['E'];rows=z['rows'];leaf=z['leaf']
    replay(T,Z,rows,leaf,E);values=reward(E);case=r['model_name'];row=dict(cell=source.name,case=case,method=method,lower=au['lower'],upper=au['upper'],verification_scope='all 32768 target witnesses independently replayed',provenance_kind='supplemental' if HERE in source.parents else 'original_followup',source_verification=str(checkpath),policy=str(p),model=str(m),result=str(source/'result.json'),E_sha256=hashlib.sha256(E.tobytes()).hexdigest())
    for obj,v in values.items():
        ref=orig['ranges'][case][obj];width=ref['maximum']-ref['minimum'];assert ref['minimum']-1e-10<=v<=ref['maximum']+1e-10
        row[obj+'_reward']=v;row[obj+'_range']=width;row[obj+'_sacrifice']=(ref['maximum']-v)/width if width>1e-12 else None
    records.append(row);ids.add(source.name)

s=read(FOLLOW/'COMBINED_STATUS.json');nm=read(FOLLOW/'near_optimal_manifest.json')
for item in nm['selected_policy_instances']:
    if item['cell'] in ids:continue
    cell=item['cell'];prov=s['provenance'][cell];ev=read(Path(prov['evaluation_path']));assert digest(Path(prov['evaluation_path']))==prov['evaluation_sha256']
    add(OLD/'main_results'/cell,f"face_{item['face_objective']}_{item['normalized_regret']:g}",ev['audit'],Path(prov['verification_path']))
manifest=read(HERE/'completion_manifest.json')
for job in manifest['jobs']:
    cell=job['id'];pc=read(HERE/'planning_checks'/cell/(cell+'.json'));source=HERE/'completion_retry_results'/cell
    assert pc['status']=='passed' and pc['result_sha256']==digest(source/'result.json')
    ev=read(HERE/'control_audits'/cell/'result.json');check=read(HERE/'control_audits'/cell/'CHECK.json');assert check['result_sha256']==digest(HERE/'control_audits'/cell/'result.json') and ev['completed_targets']==32768
    add(source,f"face_{job['face_objective']}_{job['regret']:g}",ev['audit'],HERE/'control_audits'/cell/'CHECK.json')
u=read(HERE/'uniform_audit/result.json');add(OLD/'main_results/cell_1009','uniform',u['audit'],HERE/'uniform_audit/CHECK.json')
assert len(records)==427 and len(ids)==427
for p,h in bindings.items():assert digest(Path(p))==h
write(HERE/'COMPLETE_REWARDS.json',dict(status='passed',records=records,representatives=len(records),classes=22,ranges=orig['ranges'],input_sha256=bindings,additional_input_sha256=inputs,scope='Original 355 figure representatives, all 88 original 1%/5% posterior controls, and recovered uniform control. Replayed literal policies; numerical reward ranges. No all-optima or equal-computation assertion.'))
with (HERE/'complete_rewards.csv').open('w') as f:
    w=csv.DictWriter(f,fieldnames=list(dict.fromkeys(k for r in records for k in r)));w.writeheader();w.writerows(records)
methods=['information','brier','pseudo_count','uniform','weighted128','minimax','face_information_0.01','face_information_0.05','face_brier_0.01','face_brier_0.05']
cases=s['case_order'];groups={}
for r in records:groups.setdefault((r['case'],r['method']),[]).append(r)
assert all((c,m) in groups for c in cases for m in methods)
points=[]
for c in cases:
    for m in methods:
        rr=groups[c,m];ss=[r['brier_sacrifice'] for r in rr if r['brier_sacrifice'] is not None]
        points.append(dict(case=c,method=m,lower=min(r['lower'] for r in rr),upper=max(r['upper'] for r in rr),cells=[r['cell'] for r in rr],brier_sacrifice_min=min(ss) if ss else None,brier_sacrifice_max=max(ss) if ss else None,brier_range=orig['ranges'][c]['brier']['maximum']-orig['ranges'][c]['brier']['minimum']))
ix={(r['case'],r['method']):r for r in points};comparisons=[]
for arm in ['weighted128','minimax']:
    for baseline in ['information','brier','pseudo_count','uniform','face_information_0.01','face_information_0.05','face_brier_0.01','face_brier_0.05']:
        pairs=[]
        for c in cases:
            a=ix[c,arm];b=ix[c,baseline];lo=b['lower']-a['upper'];hi=b['upper']-a['lower'];label='win' if lo>1e-6 else 'loss' if hi< -1e-6 else 'tie' if max(abs(lo),abs(hi))<=1e-6 else 'mixed'
            pairs.append(dict(case=c,lower=lo,upper=hi,outcome=label))
        comparisons.append(dict(arm=arm,baseline=baseline,cases=22,counts=dict(collections.Counter(r['outcome'] for r in pairs)),pairs=pairs,median_midpoint=float(np.median([(r['lower']+r['upper'])/2 for r in pairs]))))
write(HERE/'COMPLETE_COMPARISON.json',dict(status='passed',cases=cases,points=points,comparisons=comparisons,absolute_entries=132,posterior_controls=88,controls_added=18,uniform_added=1,source_sha256=digest(Path(__file__)),reward_report_sha256=digest(HERE/'COMPLETE_REWARDS.json'),limitations=['Retrospective completion, not independent confirmation.','Original native profiles retain their original narrower witness boundary.','Intervals cover saved numerical representatives, not all optima or statistical uncertainty.','22 heterogeneous classes are not independent identically distributed samples.','Finite uniform 128-target loss is not eventual J_w.']))
print(json.dumps([{k:r[k] for k in ['arm','baseline','counts','median_midpoint']} for r in comparisons if r['baseline'] in ['brier','face_brier_0.05']],indent=2))
