"""Standalone 22-class candidate; read saved certificates, never run a solver."""
from pathlib import Path
from collections import Counter
import csv, hashlib, json, math
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D

OUT=Path(__file__).resolve().parent
ROOT=OUT.parents[2]
BASE=ROOT/'Paper/research/target_selection_followups_2026-09-23'
ARCHIVE=ROOT/'Paper/research/target_selection_2026-09-23'
TOL=1e-6
inputs={}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def bind(p,expected=None):
    p=Path(p); h=sha(p)
    if expected is not None: assert h==expected,(str(p),'hash mismatch')
    inputs[str(p.relative_to(ROOT))]=h
    return p
def read(p,expected=None): return json.loads(bind(p,expected).read_text())
frozen=read(BASE/'FINAL_SUMMARY_HASHES.json')
for name,h in frozen['files'].items(): bind(BASE/name,h)
s=read(BASE/'COMBINED_STATUS.json')
manifest=read(ARCHIVE/'main_manifest.json')
cases=[a['case'] if a['case']!='fresh' else f"fresh_hmm_{a['seed']}_q{a['worlds']}_s3_c{a['concentration']}" for a in manifest['cases']]
assert cases==s['case_order'] and len(cases)==22
assert s['original_audit']['status']=='passed' and s['completion_audit']['status']=='passed'
assert not s['unverified_completed_jobs']
methods=['information','brier','pseudo_count','uniform','weighted128','minimax']
points={(r['case'],r['method']):r for r in s['figure_points']}
assert len(points)==131
with (BASE/'combined_figure_data.csv').open() as f: csvpoints=list(csv.DictReader(f))
assert len(csvpoints)==len(points)
for r in csvpoints:
    p=points[r['case'],r['method']]
    assert r['cells']==p['cells']
    assert float(r['lower'])==p['lower'] and float(r['upper'])==p['upper']
comparisons={(r['arm'],r['baseline']):r for r in s['comparisons']}
pairs={(a,b):{r['case']:r for r in comparisons[a,b]['pairs']} for a in ('weighted128','minimax') for b in ('brier','face_brier_0.05')}
needed=set()
for p in points.values():needed.update(p['cells'].split(';'))
for pp in pairs.values():
    for p in pp.values():needed.update(p['arm_cells']+p['baseline_cells'])
recovery_items={}
for filename in ('recovery_manifest.json','near_optimal_manifest.json'):
    for j in read(BASE/filename)['jobs']:
        for item in [j]+j['aliases']: recovery_items[item['cell']]=item
representatives={}
for cell in sorted(needed):
    prov=s['provenance'][cell]
    check=read(prov['verification_path']);assert check['status']=='passed'
    if 'result_path' in prov:
        r=read(prov['result_path'],prov['result_sha256'])
        assert r['status']=='complete' and check['result_sha256']==prov['result_sha256']
        held=r['held_out_horizon'];au=held['audit']
        scope='saved master/hardest/revelation witness replay plus complete profile arithmetic; not every old decoder replayed'
    else:
        r=read(prov['original_result_path'],prov['original_result_sha256'])
        ev=read(prov['evaluation_path'],prov['evaluation_sha256'])
        assert ev['status']=='complete' and check['result_sha256']==prov['evaluation_sha256']
        assert check['target_count']==check['decoder_witnesses']==check['decision_loss_witnesses']==32768
        item=recovery_items[cell];original=Path(prov['original_result_path']).parent
        assert item['result_sha256']==prov['original_result_sha256']
        policy=bind(original/item['checkpoint']/'policy.npz',item['policy_sha256'])
        bind(original/'model.npz',ev['model_sha256'])
        with np.load(policy,allow_pickle=False) as z: assert hashlib.sha256(z['E'].tobytes()).hexdigest()==ev['source_array_sha256']
        held={'n':ev['target_horizon'],'selection_used':ev['selection_used']};au=ev['audit']
        assert ev['completed_targets']==32768
        scope='all 32768 saved decoder and decision-loss witnesses replayed in follow-up'
    a=r['arguments'];cp=r['checkpoints'][-1]
    assert a['t']==3 and a['n']==3 and held['n']==4 and not held['selection_used']
    assert cp['status']=='complete' and au['exhaustive'] and au['target_count']==32768
    face=a.get('face_objective','none')
    if face!='none':
        assert cp['full_minimax_certified'];method=f"face_{face}_{a['regret']:g}"
    elif a['strategy']=='baseline':method='legacy_'+a['objective'] if a['objective'].startswith('native_') else a['objective']
    elif a['objective']=='native_weighted':assert cp['k']==128 and cp['full_uniform_mean_certified'];method='weighted128'
    else:assert a['objective']=='native_minimax' and cp['full_minimax_certified'];method='minimax'
    representatives[cell]={'case':r['model_name'],'method':method,'lower':au['lower'],'upper':au['upper'],'verification_scope':scope,'provenance_kind':prov['kind'],'source_verification':prov['verification_path']}
def envelope(ids,case,method):
    rr=[representatives[i] for i in ids]
    assert rr and all(r['case']==case and r['method']==method for r in rr)
    return [min(r['lower'] for r in rr),max(r['upper'] for r in rr)]
def equal(x,y):assert max(abs(float(a)-float(b)) for a,b in zip(x,y))<1e-12,(x,y)
for (case,method),p in points.items():equal(envelope(p['cells'].split(';'),case,method),[p['lower'],p['upper']])
def outcome(lo,hi):
    return 'win' if lo>TOL else 'loss' if hi< -TOL else 'tie' if max(abs(lo),abs(hi))<=TOL else 'mixed'
allcounts={};matchedcounts={}
for (arm,base),pp in pairs.items():
    counts=Counter()
    for case,p in pp.items():
        equal(envelope(p['arm_cells'],case,arm),p['arm_interval'])
        equal(envelope(p['baseline_cells'],case,base),p['baseline_interval'])
        equal(p['arm_interval'],[points[case,arm]['lower'],points[case,arm]['upper']])
        if base=='brier':equal(p['baseline_interval'],[points[case,base]['lower'],points[case,base]['upper']])
        p['difference_lower']=p['baseline_interval'][0]-p['arm_interval'][1]
        p['difference_upper']=p['baseline_interval'][1]-p['arm_interval'][0]
        label=outcome(p['difference_lower'],p['difference_upper']);assert label==p['outcome'];counts[label]+=1
    assert dict(counts)==comparisons[arm,base]['counts'] and len(pp)==comparisons[arm,base]['cases']
    allcounts[f'{arm}_vs_{base}']={'cases':len(pp),'counts':dict(counts)}
for arm in ('weighted128','minimax'):
    matched=set(pairs[arm,'face_brier_0.05']);assert len(matched)==17
    matchedcounts[arm]={base:dict(Counter(pairs[arm,base][c]['outcome'] for c in matched)) for base in ('brier','face_brier_0.05')}
missing_uniform=[c for c in cases if (c,'uniform') not in points]
missing_control=[c for c in cases if c not in pairs['weighted128','face_brier_0.05']]
assert missing_uniform==['fresh_hmm_2026100801_q8_s3_c0.2'] and len(missing_control)==5
assert missing_control==[c for c in cases if c not in pairs['minimax','face_brier_0.05']]

labels=[]
for i,c in enumerate(cases):
    if c.startswith('fresh'):
        _,_,seed,q,_,alpha=c.split('_');labels.append(f'{i+1:02d}  Fresh {q.upper()}, α={float(alpha[1:]):g}, draw {int(seed)%10+1}')
    elif c.startswith('hmm'):
        _,seed,alpha=c.split('_');labels.append(f'{i+1:02d}  Earlier HMM {seed}, α={float(alpha):g}')
    else:labels.append(f'{i+1:02d}  '+c.replace('_',' '))
colors={'information':'#0072B2','brier':'#D55E00','pseudo_count':'#E69F00','uniform':'#777777','weighted128':'#009E73','minimax':'#CC79A7'}
names={'information':'World information','brier':'Posterior Brier','pseudo_count':'Categorical count','uniform':'Uniform actions','weighted128':'Weighted native (128)','minimax':'Finite minimax'}
markers={'information':'o','brier':'s','pseudo_count':'^','uniform':'x','weighted128':'D','minimax':'P'}
plt.rcParams.update({'font.size':10,'axes.spines.top':False,'axes.spines.right':False,'pdf.fonttype':42})
fig=plt.figure(figsize=(14.6,12.2));gs=fig.add_gridspec(1,2,width_ratios=[1.06,1],left=.245,right=.975,bottom=.17,top=.83,wspace=.12)
ax=fig.add_subplot(gs[0,0]);bx=fig.add_subplot(gs[0,1],sharey=ax)
spread=[];plotrows=[]
for i,c in enumerate(cases):
    for j,m in enumerate(methods):
        p=points.get((c,m));y=i+(j-2.5)*.108
        base={'panel':'absolute','case_index':i+1,'case':c,'label':labels[i],'method':m,'comparator':'','status':'available' if p else 'missing','lower':'','upper':'','midpoint':'','representatives':0,'cells':'','baseline_cells':'','outcome':'','verification_scope':''}
        if p:
            lo,hi=p['lower'],p['upper'];mid=(lo+hi)/2;rr=[representatives[k] for k in p['cells'].split(';')]
            ax.errorbar(mid,y,xerr=[[mid-lo],[hi-mid]],fmt=markers[m],color=colors[m],markersize=4.8,elinewidth=1.35,capsize=2.4,markeredgewidth=.9,zorder=3)
            if hi-lo>2e-6:
                ax.annotate('†',(hi,y),xytext=(3,0),textcoords='offset points',fontsize=7,color=colors[m],va='center');spread.append((c,m))
            base.update(lower=lo,upper=hi,midpoint=mid,representatives=len(rr),cells=p['cells'],verification_scope='; '.join(sorted({r['verification_scope'] for r in rr})))
        else:ax.text(.985,y,'uniform missing',transform=ax.get_yaxis_transform(),ha='right',va='center',fontsize=7.5,color='#555555',bbox={'facecolor':'white','edgecolor':'none','pad':1.1})
        plotrows.append(base)
    for arm,off in [('weighted128',-.20),('minimax',.20)]:
        for control,bump in [('brier',-.07),('face_brier_0.05',.07)]:
            p=pairs[arm,control].get(c);y=i+off+bump
            base={'panel':'difference','case_index':i+1,'case':c,'label':labels[i],'method':arm,'comparator':control,'status':'available' if p else 'missing','lower':'','upper':'','midpoint':'','representatives':0,'cells':'','baseline_cells':'','outcome':'','verification_scope':''}
            if p:
                lo,hi=p['difference_lower'],p['difference_upper'];mid=(lo+hi)/2
                bx.errorbar(mid,y,xerr=[[mid-lo],[hi-mid]],fmt='o' if control=='brier' else 'D',color=colors[arm],markerfacecolor=colors[arm] if control=='brier' else 'white',markersize=4.5,elinewidth=1.2,capsize=2.1,zorder=3)
                base.update(lower=lo,upper=hi,midpoint=mid,representatives=len(p['arm_cells']),cells=';'.join(p['arm_cells']),baseline_cells=';'.join(p['baseline_cells']),outcome=p['outcome'],verification_scope='native representative envelope minus baseline/control envelope; follow-up controls replay every saved target witness')
            plotrows.append(base)
    if c in missing_control:bx.text(.99,i,'5% control missing',transform=bx.get_yaxis_transform(),ha='right',va='center',fontsize=7.4,color='#555555',bbox={'facecolor':'white','edgecolor':'none','pad':1.1})
    for axis in (ax,bx):
        if i%2==0:axis.axhspan(i-.48,i+.48,color='#f5f5f5',zorder=0)
for axis in (ax,bx):
    axis.axhline(9.5,color='#999999',lw=1.2,zorder=1);axis.grid(axis='x',alpha=.2);axis.set_ylim(21.6,-.6)
ax.set_yticks(range(22),labels,fontsize=8.7);ax.tick_params(axis='y',length=0,pad=7)
bx.tick_params(axis='y',labelleft=False,left=False)
ax.set_xlim(-.015,.585);bx.set_xlim(-.075,.37);bx.axvline(0,color='#555555',lw=.9)
ax.set_xlabel(r'Worst four-step error $A_{3,4}$ (lower is better)',labelpad=10)
bx.set_xlabel(r'$A_{3,4}$(Brier) − $A_{3,4}$(native)'+'\npositive values favor the native method',labelpad=10)
ax.set_title('(a) Absolute capability across all 22 classes',loc='left',fontweight='bold',fontsize=12,pad=13)
bx.set_title('(b) Ordinary and favorable Brier selection',loc='left',fontweight='bold',fontsize=12,pad=13)
handles=[Line2D([0],[0],marker=markers[m],color=colors[m],lw=0,markersize=5,label=names[m]) for m in methods]
fig.legend(handles=handles,loc='upper left',bbox_to_anchor=(.243,.913),ncol=2,frameon=False,fontsize=8.8,columnspacing=1.2)
right_handles=[Line2D([0],[0],marker='o',color=colors[a],lw=0,markersize=5,label=names[a]) for a in ('weighted128','minimax')]+[Line2D([0],[0],marker='o',color='#555555',lw=0,markersize=5,label='Ordinary Brier'),Line2D([0],[0],marker='D',markerfacecolor='white',color='#555555',lw=0,markersize=5,label='5% Brier control')]
fig.legend(handles=right_handles,loc='upper left',bbox_to_anchor=(.642,.913),ncol=2,frameon=False,fontsize=8.8,columnspacing=1.2)
fig.suptitle('Which short collection objective preserves longer experimental capabilities?',x=.245,y=.975,ha='left',fontsize=15,fontweight='bold')
fig.text(.245,.945,'Collect 3 action–observation pairs; native training targets have length 3; evaluation targets have length 4.',fontsize=10.3)
fig.text(.245,.923,'Supplied candidate models; actual world unknown. All full-history adaptive policies are allowed.',fontsize=10.1,color='#444444')
fig.text(.035,.594,'10 earlier cases',rotation=90,va='center',fontsize=10,color='#555555')
fig.text(.035,.318,'12 fresh random classes',rotation=90,va='center',fontsize=10,color='#555555')
fig.text(.245,.112,'On the same 17 cases with 5% controls (wins / numerical ties / losses):',fontsize=9.4,fontweight='bold')
fig.text(.245,.091,'Weighted: ordinary Brier 14 / 2 / 1 → 5% control 13 / 0 / 4.    Minimax: 15 / 0 / 2 → 15 / 0 / 2.',fontsize=9.3)
fig.text(.245,.064,'Intervals enclose saved representatives and numerical bounds, not all optima or statistical uncertainty. † marks visible spread.\nOne uniform entry and five 5% controls are unavailable. These finite objectives are not eventual J_w.',fontsize=9,color='#444444')
fig.text(.245,.027,'Floating-point witness checks differ by archive: original results replay saved hardest/revelation witnesses and profile arithmetic;\nnew recovered and 5% control audits replay every target witness. See CAPTION_22.md and FIGURE22_CHECK.json.',fontsize=8.4,color='#555555')
for ext in ('pdf','png'):fig.savefig(OUT/f'CANDIDATE_22_CLASSES.{ext}',dpi=180,facecolor='white')
plt.close(fig)
with (OUT/'figure22_data.csv').open('w',newline='') as f:
    writer=csv.DictWriter(f,fieldnames=list(plotrows[0]));writer.writeheader();writer.writerows(plotrows)
assert len(plotrows)==220 and sum(r['status']=='available' for r in plotrows)==209
check={'status':'passed','scope':'Frozen summary and original manifest hashes; per-plotted-cell result/check binding, recovered experiment/model/policy binding, optimization flags, complete target coverage, reconstructed saved-representative envelopes and interval subtraction. No numerical solver or new witness replay.', 'model_order':cases,'collection_horizon':3,'training_target_horizon':3,'evaluation_target_horizon':4,'comparison_tolerance':TOL,'absolute_available':131,'absolute_expected':132,'difference_available':78,'difference_expected':88,'missing_uniform':missing_uniform,'missing_5percent_brier':missing_control,'all_case_comparisons':allcounts,'common_17_case_comparisons':matchedcounts,'representative_spread_marker_threshold':2e-6,'visible_spreads':[{'case':c,'method':m} for c,m in spread],'checked_representatives':representatives,'source_sha256':inputs,'output_sha256':{n:sha(OUT/n) for n in ['make_candidate22.py','CANDIDATE_22_CLASSES.pdf','CANDIDATE_22_CLASSES.png','figure22_data.csv','CAPTION_22.md'] if (OUT/n).exists()},'limitations':['Numerical/reported representative envelopes do not characterize all optimizers.','Original archive does not retain every target decoder; follow-up audits do.','The 22 settings are heterogeneous and are not i.i.d. replications.','No equal-time comparison or rich-background certificate is transferred from the separate 12-setting study.']}
(OUT/'FIGURE22_CHECK.json').write_text(json.dumps(check,indent=2)+'\n')
print(json.dumps({'status':'passed','checked_representatives':len(representatives),'absolute_available':131,'differences_available':78,'all_case_comparisons':allcounts,'common_17_case_comparisons':matchedcounts,'missing_uniform':missing_uniform,'missing_5percent_brier':missing_control},indent=2))
