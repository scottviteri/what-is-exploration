"""Analyze the preregistered-within-this-diagnostic reference/control pairs."""
import os
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
from diagnostics import *
rows=[];bindings={}
def read(p):bindings[str(p)]=digest(p);return json.loads(p.read_text())
manifest=read(HERE/'matched_manifest.json');orig=read(HERE/'COMPLETE_REWARDS.json');refmap={r['cell']:r for r in orig['records']}
def checked_audit(p):
    r=read(p/'result.json');ch=read(p/'CHECK.json');assert r['status']=='complete' and r['completed_targets']==32768 and ch['status']=='passed' and ch['result_sha256']==digest(p/'result.json')
    for path,h in r['input_sha256'].items():assert digest(Path(path))==h
    with np.load(r['policy']) as z:E=z['E'];prows=z['rows'];leaf=z['leaf']
    with np.load(r['model']) as z:T=z['T'];Z=z['Z']
    replay(T,Z,prows,leaf,E)
    return r,reward(E)
for spec in manifest['thresholds']:
    mid=spec['id'];base=refmap[spec['reference_cell']];pc=read(HERE/'matched_planning_checks'/mid/(mid+'.json'));assert pc['status']=='passed'
    newsource=HERE/'matched_results'/mid;new=read(newsource/'result.json');old=read(Path(base['result']));assert pc['result_sha256']==digest(newsource/'result.json')
    ra,rw=checked_audit(HERE/'reference_audits'/mid);ca,cw=checked_audit(HERE/'matched_audits'/mid)
    assert digest(Path(ra['policy']))==spec['reference_policy_sha256']
    assert max(abs(ra['audit']['lower']-base['lower']),abs(ra['audit']['upper']-base['upper']))<2e-7
    threshold=new['reward_face']['threshold'];assert abs(threshold-(spec['reference_brier']-1e-10))<1e-12
    assert cw['brier']>=threshold-1e-12 and abs(rw['brier']-spec['reference_brier'])<1e-12
    nm=new['checkpoints'][-1];om=old['checkpoints'][-1]
    assert nm['full_minimax_certified'] and nm['full_minimax_gap']<=2e-7
    assert nm['audit']['upper']<=om['audit']['upper']+2e-7,'Training optimum should have the reference as a feasible alternative'
    lo=ca['audit']['lower']-ra['audit']['upper'];hi=ca['audit']['upper']-ra['audit']['lower']
    outcome='native_win' if lo>1e-6 else 'native_loss' if hi< -1e-6 else 'tie' if max(abs(lo),abs(hi))<=1e-6 else 'unresolved'
    width=base['brier_range'];sac=lambda val:(orig['ranges'][spec['case']]['brier']['maximum']-val)/width if width>1e-12 else None
    rows.append(dict(id=mid,case=spec['case'],reference_cell=spec['reference_cell'],native_lower=ra['audit']['lower'],native_upper=ra['audit']['upper'],control_lower=ca['audit']['lower'],control_upper=ca['audit']['upper'],difference_lower=lo,difference_upper=hi,outcome=outcome,native_brier=rw['brier'],control_brier=cw['brier'],reward_threshold=threshold,native_sacrifice=sac(rw['brier']),control_sacrifice=sac(cw['brier']),native_training_worst=om['audit']['upper'],control_training_worst=nm['audit']['upper'],control_optimizer_gap=nm['full_minimax_gap'],control_planning_seconds=new['training_seconds'],control_audit_seconds=ca['seconds'],reference_audit_seconds=ra['seconds']))
assert len(rows)==22
report=dict(status='passed',cases=22,counts=dict(collections.Counter(r['outcome'] for r in rows)),median_midpoint=float(np.median([(r['difference_lower']+r['difference_upper'])/2 for r in rows])),all_training_checks_nonworse=True,reward_matching='Control has at least reference Brier reward, with the original explicit 1e-10 slack. At most the same sacrifice; not exactly equal reward.',records=rows,input_sha256=bindings,source_sha256=digest(Path(__file__)),scope='Post-design diagnostic on all original classes, single references selected lexically without held-out values, every depth-four witness checked for both policies. No all-optima, population, eventual-order, or generic Brier-learner claim.')
write(HERE/'MATCHED_COMPARISON.json',report)
with (HERE/'matched_comparison.csv').open('w') as f:w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
print({k:v for k,v in report.items() if k not in ['records','input_sha256']})
