"""Render an isolated candidate from completed evidence; no optimization or training."""
from pathlib import Path
import csv, hashlib, json, statistics
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.ticker import NullLocator
import numpy as np

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[2]
BASE = ROOT / 'Paper/research/jw_computational_tests_2026-09-23/quality_corrected'

def load_csv(rel):
    p = BASE / rel
    return list(csv.DictReader(p.open()))

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def mid(r): return (float(r['audit_lower']) + float(r['audit_upper'])) / 2

rows = load_csv('summary/endpoints.csv')
check = json.loads((BASE / 'SUMMARY_CHECK.json').read_text())
assert check['status'] == 'passed' and len(rows) == 540
# Bind the source table to its independent reporting check, not just its filename.
assert sha(BASE / 'summary/endpoints.csv') == check['input_sha256'][str(BASE / 'summary/endpoints.csv')]
for r in rows:
    assert r['comparison_eligible'] == 'True' and r['endpoint_status'] == 'validated_complete'
    assert r['audit_validation_status'] == 'passed' and int(r['audit_completed_targets']) == 32768
    assert int(r['collection_horizon']) == 3 and int(r['target_depth']) == 4
    assert float(r['audit_lower']) <= float(r['audit_upper']) + 1e-10
lookup = {(r['model'], r['method'], int(r['budget_seconds'])): r for r in rows}
assert len(lookup) == len(rows)
models = sorted({r['model'] for r in rows}, key=lambda m: (int(m.split('_')[0][1:]), float(m.split('_')[1][1:]), int(m.split('_')[2][1:])))
assert len(models) == 12
rewards = load_csv('reward_diagnostics/results/DIAGNOSTICS.csv')
rlookup = {(r['model'],r['method'],int(r['budget_seconds'])): r for r in rewards}
assert len(rlookup) == 540
for r in rows:
    d = rlookup[r['model'],r['method'],int(r['budget_seconds'])]
    assert d['exact_E_sha256'] == r['exact_E_sha256'] and d['reward_status'] == 'computed'
pairs = load_csv('same_time_order/results/PAIRS.csv')
order_check = json.loads((BASE/'same_time_order/results/CHECKS.json').read_text())
assert order_check['status'] == 'passed' and len(pairs) == 144
assert sha(BASE/'same_time_order/results/SUMMARY.json') == order_check['summary_sha256']
# Bind post-design CSVs to the completed immutable output manifests.
for directory, names in [('same_time_order/results',['PAIRS.csv','SUMMARY.json','CHECKS.json']),('reward_diagnostics/results',['DIAGNOSTICS.csv','SUMMARY.json'])]:
    manifest=json.loads((BASE/directory/'FILES.json').read_text())
    for name in names: assert sha(BASE/directory/name)==manifest[name]
assert all(r['classification'] == 'numerical_incomparability' for r in pairs)
assert all(float(r[d]) > 1e-6 for r in pairs for d in ('forward_lower','reverse_lower'))
certs = load_csv('static_certificate_aggregation/certificates.csv')
static_check=json.loads((BASE/'static_certificate_aggregation/CHECKS.json').read_text())
assert static_check['status']=='passed' and static_check['row_count']==len(certs)==288
checked_rows={(r['model'],r['method'],int(r['budget_seconds'])):r for r in static_check['rows']}
for r in certs:
    matched=checked_rows[r['model'],r['method'],int(r['budget_seconds'])]
    for k,v in r.items():
        assert str(matched[k])==v, (r['model'],r['method'],k)
for path,expected in static_check['input_sha256'].items():
    assert sha(Path(path))==expected, path
for path,expected in static_check['source_sha256'].items():
    assert sha(Path(path))==expected, path
static40 = [r for r in certs if r['budget_seconds']=='40']
assert len(static40)==96 and max(float(r['aggregated_gap_upper']) for r in static40)<8.1e-7

colors = {'information':'#0072B2','brier':'#D55E00','fixed':'#009E73','minimax':'#CC79A7','uniform':'#777777'}
labels = {'information':'Information gain','brier':'Posterior Brier','fixed':'Fixed native weights','minimax':'Finite minimax','uniform':'Uniform actions'}
markers = {'information':'o','brier':'s','fixed':'D','minimax':'^','uniform':'x'}
plt.rcParams.update({'font.size':10,'axes.spines.top':False,'axes.spines.right':False,'pdf.fonttype':42,'savefig.facecolor':'white'})
fig = plt.figure(figsize=(12.5,8))
gs = fig.add_gridspec(2,2,width_ratios=[1.16,1],hspace=.57,wspace=.35)
ax = fig.add_subplot(gs[:,0])
methods = ['uniform','information','brier','fixed','minimax']
for i,m in enumerate(methods):
    rs = [lookup[q,m,40] for q in models]
    xs = np.array([mid(r) for r in rs]); ys = np.arange(12)+(i-2)*.13
    ax.errorbar(xs,ys,xerr=np.array([[max(0,mid(r)-float(r['audit_lower'])) for r in rs],[max(0,float(r['audit_upper'])-mid(r)) for r in rs]]),fmt=markers[m],ms=4.8,color=colors[m],lw=.9,label=labels[m])
for y in np.arange(.5,12,2): ax.axhline(y,color='#ededed',lw=.8,zorder=0)
ax.axhline(5.5,color='#aaaaaa',lw=1,zorder=0)
shortlabels=[]
for q in models:
    r=lookup[q,'fixed',40]
    shortlabels.append(f"{r['worlds']} worlds | α={float(r['concentration']):g} | {'A' if r['seed']=='926103' else 'B'}")
ax.set_yticks(range(12),shortlabels);ax.invert_yaxis();ax.set_xlim(left=0)
ax.set_xlabel(r'Worst four-step simulation error $A_{3,4}$  (lower is better)')
ax.set_title('(a) Same evidence budget, different objectives',loc='left',fontweight='bold',pad=18)
ax.text(0,1.005,'40-second planning allowance; all 12 model settings',transform=ax.transAxes,fontsize=9,color='#555555')
ax.grid(axis='x',alpha=.18);ax.legend(loc='lower right',fontsize=8.5,frameon=True,facecolor='white')

ax=fig.add_subplot(gs[0,1])
for b in ['information','brier']:
    curves=[]
    for q in models:
        ds=[mid(lookup[q,b,t])-mid(lookup[q,'fixed',t]) for t in (2,10,40)]
        curves.append(ds)
        ax.plot([2,10,40],ds,color=colors[b],lw=.7,alpha=.24,marker='o' if q.endswith('926103') else 's',ms=2.5)
    ax.plot([2,10,40],np.median(curves,axis=0),color=colors[b],lw=2.5,marker=markers[b],ms=5,label='vs '+labels[b])
ax.axhline(0,color='#555555',lw=.8)
ax.set_xscale('log');ax.xaxis.set_minor_locator(NullLocator());ax.set_xticks([2,10,40],['2','10','40']);ax.set_xlim(1.7,47)
ax.set_ylabel(r'$A_{3,4}$(baseline) − $A_{3,4}$(fixed native)')
ax.set_xlabel('Planning allowance (seconds)')
ax.set_title('(b) Capability depends on planning time',loc='left',fontweight='bold',pad=18)
ax.text(0,1.01,'Above zero favors fixed native; Bayesian DP takes about 5 ms',transform=ax.transAxes,fontsize=8.7,color='#555555')
ax.legend(fontsize=8.3,loc='lower right');ax.grid(alpha=.15)

ax=fig.add_subplot(gs[1,1])
for b in ['information','brier']:
    curves=[]; observed_x=[]
    for q in models:
        rr=[rlookup[q,f'{b}_face{p}',40] for p in (0,1,5)]
        xx=[100*max(0,float(r[f'{b}_normalized_regret'])) for r in rr]
        yy=[mid(lookup[q,f'{b}_face{p}',40])-mid(lookup[q,'fixed',40]) for p in (0,1,5)]
        curves.append(yy);observed_x.append(xx)
        ax.plot(xx,yy,color=colors[b],lw=.7,alpha=.28,marker='o' if q.endswith('926103') else 's',ms=2.5)
    ax.plot(np.median(observed_x,axis=0),np.median(curves,axis=0),color=colors[b],lw=2.5,marker=markers[b],ms=5,label='vs '+labels[b]+' control')
ax.axhline(0,color='#555555',lw=.8)
ax.set_xlim(-.25,5.3);ax.set_xticks([0,1,5]);ax.grid(alpha=.15)
ax.set_ylabel(r'$A_{3,4}$(control) − $A_{3,4}$(fixed native)')
ax.set_xlabel('Actual posterior-reward loss (% of attainable range)')
ax.set_title('(c) Reward concessions reduce the gap',loc='left',fontweight='bold',pad=18)
ax.text(0,1.01,'Controls selected on three-step targets; all methods at 40 seconds',transform=ax.transAxes,fontsize=8.6,color='#555555')
ax.legend(fontsize=8,loc='upper right')
fig.subplots_adjust(left=.18,right=.985,bottom=.12,top=.91)
fig.suptitle('Candidate replacement: what can three collected observations reproduce?',fontsize=14,y=.98)
fig.text(.18,.038,'A/B identify two independent seed families reused across parameter settings. Thin curves show all settings; no statistical error bars.\nA lower scalar audit is not experiment dominance: all 144 tested native/baseline pairs were incomparable at collection time three.',fontsize=8.8,color='#444444')
for ext in ('pdf','png'):fig.savefig(OUT/f'CANDIDATE_FIGURE.{ext}',dpi=180)
plt.close(fig)

fig,axs=plt.subplots(1,2,figsize=(10,4.4))
for m in ('fixed','minimax'):
    x=[100*float(rlookup[q,m,40]['brier_normalized_regret']) for q in models]
    y=[mid(lookup[q,'brier',40])-mid(lookup[q,m,40]) for q in models]
    axs[0].scatter(x,y,c=colors[m],marker=markers[m],s=30,label=labels[m])
    ps=[r for r in pairs if r['method']==m and r['baseline']=='brier']
    axs[1].scatter([(float(r['forward_lower'])+float(r['forward_upper']))/2 for r in ps],[(float(r['reverse_lower'])+float(r['reverse_upper']))/2 for r in ps],c=colors[m],marker=markers[m],s=30,label=labels[m])
axs[0].axhline(0,color='#555555',lw=.8);axs[0].set_xlabel('Brier reward sacrificed (% of attainable range)');axs[0].set_ylabel(r'$A_{3,4}$(Brier) − $A_{3,4}$(native)');axs[0].set_title('(a) Native gains have a reward cost',loc='left')
axs[1].set_xlim(left=0);axs[1].set_ylim(bottom=0);axs[1].set_xlabel('Error simulating Brier record from native record');axs[1].set_ylabel('Error simulating native record from Brier record');axs[1].set_title('(b) Neither record replaces the other',loc='left')
for ax in axs:ax.grid(alpha=.15);ax.legend(fontsize=8)
fig.suptitle('Supporting tradeoff diagnostics — all 12 settings, 40-second endpoints',fontsize=12)
fig.tight_layout(rect=(0,.06,1,.94));fig.text(.08,.025,'Post-design diagnostics, fixed collection length 3. Numerical witnesses are not statistical intervals or eventual-order claims.',fontsize=8.2)
for ext in ('pdf','png'):fig.savefig(OUT/f'TRADEOFF_DIAGNOSTIC.{ext}',dpi=180)
plt.close(fig)

# Compact, auditable derived values; keep all methods and checkpoints in the source.
figure_rows=[]
for r in rows:
    d=rlookup[r['model'],r['method'],int(r['budget_seconds'])]
    figure_rows.append({k:r[k] for k in ('model','worlds','concentration','seed','method','budget_seconds','audit_lower','audit_upper','available_seconds','audit_id')} | {'audit_midpoint':mid(r),'information_normalized_regret':d['information_normalized_regret'],'brier_normalized_regret':d['brier_normalized_regret']})
with (OUT/'figure_data.csv').open('w') as f:
    w=csv.DictWriter(f,fieldnames=list(figure_rows[0]));w.writeheader();w.writerows(figure_rows)
def comparison(m,b,t):
    wins=losses=unresolved=0;ds=[]
    for q in models:
        a,z=lookup[q,m,t],lookup[q,b,t]
        if float(a['audit_upper']) < float(z['audit_lower'])-1e-6:wins+=1
        elif float(z['audit_upper']) < float(a['audit_lower'])-1e-6:losses+=1
        else:unresolved+=1
        ds.append(mid(z)-mid(a))
    return {'wins':wins,'losses':losses,'unresolved':unresolved,'median_baseline_minus_native':statistics.median(ds),'all_differences':dict(zip(models,ds))}
summary={'role':'Post-design candidate presentation of a completed prospectively specified study; no new optimization.', 'models':models,'independent_seed_families':2,'comparisons':{f'{m}_vs_{b}_at_{t}':comparison(m,b,t) for m in ('fixed','minimax','tractability','hard') for b in ('information','brier','uniform','information_face0','information_face1','information_face5','brier_face0','brier_face1','brier_face5') for t in (2,10,40)},'maximum_audit_interval_width':max(float(r['audit_upper'])-float(r['audit_lower']) for r in rows),'static_40s_max_aggregated_gap':max(float(r['aggregated_gap_upper']) for r in static40),'same_time_incomparable_pairs':len(pairs),'fixed_40s_brier_regret_percent':{'median':statistics.median(100*float(rlookup[q,'fixed',40]['brier_normalized_regret']) for q in models),'min':min(100*float(rlookup[q,'fixed',40]['brier_normalized_regret']) for q in models),'max':max(100*float(rlookup[q,'fixed',40]['brier_normalized_regret']) for q in models)}}
(OUT/'ANALYSIS.json').write_text(json.dumps(summary,indent=2)+'\n')
inputs=['summary/endpoints.csv','SUMMARY_CHECK.json','same_time_order/results/FILES.json','reward_diagnostics/results/FILES.json','reward_diagnostics/results/DIAGNOSTICS.csv','reward_diagnostics/results/SUMMARY.json','same_time_order/results/PAIRS.csv','same_time_order/results/SUMMARY.json','same_time_order/results/CHECKS.json','static_certificate_aggregation/certificates.csv','static_certificate_aggregation/CHECKS.json','PROTOCOL.md']
manifest={'status':'passed','scope':'Source reporting-check binding, fixed 540-row coverage, policy-experiment joins, static gap and same-time diagnostic checks; derived plotting arithmetic. No new numerical LP replay.','source_sha256':{str((BASE/p).relative_to(ROOT)):sha(BASE/p) for p in inputs},'output_sha256':{p.name:sha(p) for p in OUT.iterdir() if p.name in ['make_candidate.py','ANALYSIS.json','figure_data.csv','CANDIDATE_FIGURE.pdf','CANDIDATE_FIGURE.png','TRADEOFF_DIAGNOSTIC.pdf','TRADEOFF_DIAGNOSTIC.png']}}
(OUT/'FIGURE_CHECK.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({k:summary[k] for k in ('maximum_audit_interval_width','static_40s_max_aggregated_gap','same_time_incomparable_pairs','fixed_40s_brier_regret_percent')},indent=2))
print('Wrote two figures and 540-row source-bound plotting table; no optimization or training.')
