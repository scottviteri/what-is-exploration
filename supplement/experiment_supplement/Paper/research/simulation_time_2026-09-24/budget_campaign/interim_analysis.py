"""Read-only snapshot and joint-figure preview; never changes running inputs."""
from pathlib import Path
import json,hashlib,datetime
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%d_%H%M%S')
out=HERE/('interim_'+stamp);out.mkdir()
status=json.loads((HERE/'STATUS.json').read_text());refs=json.loads((HERE/'REFERENCES.json').read_text());cases=refs['cases'][:4]
methods=refs['methods'];data={};bindings={};rows=[]
for item in status['records']:
 if item['status']!='passed' or item.get('case') not in cases:continue
 rp=HERE/item['result'];cp=rp.parent/'CHECK.json';r=json.loads(rp.read_text());c=json.loads(cp.read_text())
 assert c['status']=='passed' and c['result_sha256']==sha(rp)
 bindings[str(rp.relative_to(ROOT))]=sha(rp);bindings[str(cp.relative_to(ROOT))]=sha(cp)
 for a in r['audits']:
  wp=rp.parent/a['witness'];assert sha(wp)==a['witness_sha256'];bindings[str(wp.relative_to(ROOT))]=a['witness_sha256']
 data[r['spec']['case'],r['spec']['method'],r['spec']['t']]=r;rows.append(r)
assert len(data)==72
oldp=ROOT/'Paper/research/empirical_ending_checks_2026-09-23/COMPLETE_REWARDS.json';old=json.loads(oldp.read_text());bindings[str(oldp.relative_to(ROOT))]=sha(oldp)
oldby={r['cell']:r for r in old['records']};refby={(r['case'],r['method']):r for r in refs['records']}
summary=[]
for case in cases:
 for method in methods:
  rs=[data[case,method,t] for t in [3,4,5]]
  summary.append(dict(case=case,method=method,all_six_reproduced_at_002=[all(a['classification']['0.02']=='reproduced' for a in r['audits']) for r in rs],targets_reproduced_at_002=[sum(a['classification']['0.02']=='reproduced' for a in r['audits']) for r in rs],to_brier=[next(a['upper'] for a in r['audits'] if a['reference']=='brier') for r in rs],to_native_mean=[next(a['upper'] for a in r['audits'] if a['reference']=='weighted128') for r in rs]))
(out/'SNAPSHOT.json').write_text(json.dumps(dict(snapshot_utc=stamp,live_status_at_read=status,scope='All four prespecified pilot cases, six methods, budgets 3/4/5; no selection by outcome. This preview is not a manuscript replacement.',bindings=bindings,summary=summary,records=rows),indent=2)+'\n')
colors=dict(information='#0072B2',brier='#D55E00',pseudo_count='#E69F00',uniform='#777777',weighted128='#009E73',minimax='#CC79A7')
labels=dict(information='Information',brier='Brier',pseudo_count='Pseudo-count',uniform='Uniform',weighted128='Native mean',minimax='Native maximum')
case_labels=['Repeatable sensors (0.1, 0.1)','Delayed sensor (0.1, 0.1)','Irreversible choice (0.1, 0.1)','Generated hidden-state class (4 worlds, concentration 0.2)']
plt.rcParams.update({'font.size':9,'axes.spines.top':False,'axes.spines.right':False,'pdf.fonttype':42})
fig,axes=plt.subplots(4,2,figsize=(9.5,9.1),gridspec_kw={'width_ratios':[1,1.2]})
fig.subplots_adjust(left=.16,right=.97,bottom=.14,top=.84,wspace=.27,hspace=.65)
fig.suptitle('Short-record tradeoffs and recovery with a larger collection budget',x=.05,y=.98,ha='left',fontsize=13,weight='bold')
fig.text(.05,.947,'Research preview: all four prespecified pilot cases; wider 22-class campaign remains in progress.',fontsize=9)
fig.text(.16,.907,'A. Three collected steps → four-step targets',fontsize=10,weight='bold')
fig.text(.60,.907,'B. Larger budgets → fixed three-step records',fontsize=10,weight='bold')
fig.legend(handles=[Line2D([0],[0],color=colors['brier'],marker='o',label='Brier collector → native-mean reference'),Line2D([0],[0],color=colors['weighted128'],marker='D',label='Native-mean collector → Brier reference')],loc='upper left',bbox_to_anchor=(.16,.899),ncol=2,frameon=False,fontsize=8.5)
for i,case in enumerate(cases):
 a,b=axes[i];a.set_title(case_labels[i],loc='left',fontsize=9.3,pad=8,weight='bold')
 for k,method in enumerate(methods):
  ref=refby[case,method];r=oldby[ref['cell']];ensemble=[x for x in old['records'] if x['case']==case and x['method']==method]
  lo=min(x['lower'] for x in ensemble);hi=max(x['upper'] for x in ensemble);mid=(r['lower']+r['upper'])/2
  a.plot([lo,hi],[k,k],color=colors[method],lw=2,alpha=.35);a.plot(mid,k,'o',color=colors[method],ms=4)
 a.set_yticks(range(6),[labels[m] for m in methods]);a.set_ylim(5.6,-.6);a.set_xlim(-.01,.55);a.set_xticks([0,.25,.5]);a.grid(axis='x',alpha=.15)
 a.set_xlabel('Worst four-step target error',fontsize=8.5)
 for method,target,marker in [('brier','weighted128','o'),('weighted128','brier','D')]:
  audits=[next(v for v in data[case,method,t]['audits'] if v['reference']==target) for t in [3,4,5]]
  vals=[max(0,(v['lower']+v['upper'])/2) for v in audits];b.plot([3,4,5],vals,marker=marker,color=colors[method],ms=4,lw=1.5)
 b.axhline(.02,color='#555555',linestyle=':',lw=1);b.set_ylim(-.008,.265);b.set_yticks([0,.1,.2]);b.set_xlim(2.85,5.15);b.set_xticks([3,4,5]);b.grid(alpha=.12);b.set_xlabel('Total collection budget (new policy at each point)',fontsize=8.3)
 b.set_ylabel('Fixed-reference error',fontsize=8.5)
 if i==0:b.text(4.25,.033,'0.02 tolerance',fontsize=8,color='#555555')
 if i==2:b.text(3.04,.147,'Equal native-mean scores can select\ndifferent initial branches.',fontsize=8,color='#333333')
fig.text(.05,.052,'A: dots are the frozen reference representatives; faint ranges retain other archived representatives. B: numerical intervals',fontsize=8)
fig.text(.05,.036,'are smaller than markers. Independently optimized collectors need not improve monotonically. The matched 6/1/15 result,',fontsize=8)
fig.text(.05,.020,'reward costs, all method pairs, and all 22 classes remain required context for a final joint figure; omitted here for layout review.',fontsize=8)
fig.savefig(out/'JOINT_PILOT_PREVIEW.pdf');fig.savefig(out/'JOINT_PILOT_PREVIEW.png',dpi=160);plt.close(fig)
print(out)
print(json.dumps({'snapshot_status':status['counts'],'pilot_cells':len(data),'source_bindings':len(bindings)},indent=2))
