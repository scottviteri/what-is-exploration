"""Display both audit differences and the actual attained reward constraint."""
from pathlib import Path
import json,numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
HERE=Path(__file__).resolve().parent
d=json.loads((HERE/'MATCHED_COMPARISON.json').read_text());r=d['records'];n=len(r)
plt.rcParams.update({'font.size':10,'axes.spines.top':False,'axes.spines.right':False,'pdf.fonttype':42})
fig,(a,b)=plt.subplots(1,2,figsize=(14,10),gridspec_kw={'width_ratios':[1,1]});fig.subplots_adjust(left=.29,right=.975,top=.84,bottom=.17,wspace=.16)
labels=[]
for i,x in enumerate(r):
 c=x['case']
 if c.startswith('fresh'):
  _,_,seed,q,_,alpha=c.split('_');label=f'{i+1:02d}  Fresh {q.upper()}, α={float(alpha[1:]):g}, draw {int(seed)%10+1}'
 elif c.startswith('hmm'):
  _,seed,alpha=c.split('_');label=f'{i+1:02d}  Earlier HMM {seed}, α={float(alpha):g}'
 else:label=f'{i+1:02d}  '+c.replace('_',' ')
 labels.append(label);lo=x['difference_lower'];hi=x['difference_upper'];mid=(lo+hi)/2
 color='#009E73' if x['outcome']=='native_win' else '#D55E00' if x['outcome']=='native_loss' else '#777777'
 a.errorbar(mid,i,xerr=[[mid-lo],[hi-mid]],fmt='o',color=color,markersize=5,capsize=3)
 if x['native_sacrifice'] is not None:
  v=100*x['native_sacrifice'];w=100*x['control_sacrifice'];b.plot([w,v],[i,i],color='#bbbbbb');b.scatter([v],[i],color='#009E73',marker='D',s=29);b.scatter([w],[i],color='#D55E00',marker='s',s=26)
 else:b.text(1,i,'constant Brier reward',fontsize=8,va='center')
 for ax in [a,b]:
  if i%2==0:ax.axhspan(i-.47,i+.47,color='#f5f5f5',zorder=0)
for ax in [a,b]:ax.set_ylim(n-.5,-.5);ax.set_yticks(range(n));ax.grid(axis='x',alpha=.18)
a.set_yticklabels(labels,fontsize=8.5);a.tick_params(axis='y',length=0);b.set_yticklabels([]);b.tick_params(axis='y',length=0)
a.axvline(0,color='#666666',lw=1);a.set_xlabel(r'$A_{3,4}$(matched control) − $A_{3,4}$(weighted native)'+'\npositive favors weighted native',labelpad=10)
b.set_xlabel('Actual Brier sacrifice (% of attainable range)\ncontrol may retain more reward than required',labelpad=10)
b.plot([],[],color='#009E73',marker='D',ls='',label='Weighted native reference');b.plot([],[],color='#D55E00',marker='s',ls='',label='Reward-matched minimax control');b.legend(frameon=False,loc='upper right',bbox_to_anchor=(1,1.10),fontsize=9)
a.set_title('(a) Longer-target audit at matched reward',loc='left',fontweight='bold',pad=14)
b.set_title('(b) Actual reward sacrificed',loc='left',fontweight='bold',pad=14)
fig.suptitle('Does the longer-target advantage survive reward matching?',x=.29,ha='left',y=.973,fontsize=17,fontweight='bold')
fig.text(.29,.936,'All 22 original classes. Select the control using depth-three targets and the reference’s Brier reward.',fontsize=10)
fig.text(.29,.914,'Both collect three interactions; every depth-four target witness is checked for both resulting policies.',fontsize=10)
c=d['counts'];fig.text(.29,.097,f"Weighted native: {c.get('native_win',0)} wins, {c.get('tie',0)} numerical ties, {c.get('native_loss',0)} losses, {c.get('unresolved',0)} unresolved.",fontsize=10)
fig.text(.29,.069,'Post-design diagnostic; one fixed reference per class, selected without the new audit results. Not an all-optima or population claim.',fontsize=9)
fig.text(.29,.044,'The control is a constrained native minimax planner, not an ordinary Brier learner. Its reward floor includes the stated 1e−10 allowance.',fontsize=9,color='#555555')
for ext in ['pdf','png']:fig.savefig(HERE/f'REWARD_MATCHED_DIAGNOSTIC.{ext}',dpi=175,facecolor='white')
