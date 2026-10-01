"""Standalone, post-design candidate; never modifies the manuscript."""
from pathlib import Path
import json,numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
HERE=Path(__file__).resolve().parent
d=json.loads((HERE/'COMPLETE_COMPARISON.json').read_text());cases=d['cases'];ix={(r['case'],r['method']):r for r in d['points']};cmp={(r['arm'],r['baseline']):{p['case']:p for p in r['pairs']} for r in d['comparisons']}
colors={'information':'#0072B2','brier':'#D55E00','pseudo_count':'#E69F00','uniform':'#777777','weighted128':'#009E73','minimax':'#CC79A7','face_brier_0.05':'#333333'}
names={'information':'World information','brier':'World-posterior Brier','pseudo_count':'Categorical pseudo-count','uniform':'Uniform actions','weighted128':'Weighted native (128)','minimax':'Finite minimax','face_brier_0.05':'Minimax with 5%-Brier allowance'}
markers={'information':'o','brier':'s','pseudo_count':'^','uniform':'x','weighted128':'D','minimax':'P','face_brier_0.05':'o'}
methods=['information','brier','pseudo_count','uniform','weighted128','minimax']
labels=[]
for i,c in enumerate(cases):
 if c.startswith('fresh'):
  _,_,seed,q,_,alpha=c.split('_');labels.append(f'{i+1:02d}  Fresh {q.upper()}, α={float(alpha[1:]):g}, draw {int(seed)%10+1}')
 elif c.startswith('hmm'):
  _,seed,alpha=c.split('_');labels.append(f'{i+1:02d}  Earlier HMM {seed}, α={float(alpha):g}')
 else:labels.append(f'{i+1:02d}  '+c.replace('_',' '))
plt.rcParams.update({'font.size':10,'axes.spines.top':False,'axes.spines.right':False,'pdf.fonttype':42})
fig=plt.figure(figsize=(17,12));gs=fig.add_gridspec(1,3,left=.21,right=.98,top=.805,bottom=.195,width_ratios=[1.15,1,.95],wspace=.15);axes=[fig.add_subplot(gs[0,k]) for k in range(3)];a,b,c=axes
for i,case in enumerate(cases):
 for j,m in enumerate(methods):
  r=ix[case,m];lo,hi=r['lower'],r['upper'];mid=(lo+hi)/2
  a.errorbar(mid,i+(j-2.5)*.11,xerr=[[mid-lo],[hi-mid]],fmt=markers[m],color=colors[m],markersize=4.4,capsize=2,elinewidth=1.2)
 for j,m in enumerate(['weighted128','minimax']):
  r=cmp[m,'face_brier_0.05'][case];lo,hi=r['lower'],r['upper'];mid=(lo+hi)/2
  b.errorbar(mid,i+(j-.5)*.24,xerr=[[mid-lo],[hi-mid]],fmt=markers[m],color=colors[m],markersize=5,capsize=2,elinewidth=1.4)
 for j,m in enumerate(['weighted128','minimax','face_brier_0.05']):
  r=ix[case,m];lo=r['brier_sacrifice_min'];hi=r['brier_sacrifice_max']
  if lo is not None:
   lo=max(0,lo)*100;hi=max(0,hi)*100;mid=(lo+hi)/2
   c.errorbar(mid,i+(j-1)*.18,xerr=[[mid-lo],[hi-mid]],fmt=markers[m],color=colors[m],markersize=4.4,capsize=2,elinewidth=1.3,markerfacecolor='white' if m=='face_brier_0.05' else colors[m])
  elif j==0:c.text(2,i,'constant Brier reward',va='center',fontsize=8,color='#555555')
 for ax in axes:
  if i%2==0:ax.axhspan(i-.49,i+.49,color='#f4f4f4',zorder=0)
for ax in axes:
 ax.set_ylim(21.6,-.6);ax.grid(axis='x',alpha=.18);ax.axhline(9.5,color='#aaaaaa',lw=1);ax.set_yticks(range(22))
a.set_yticklabels(labels,fontsize=8.5);a.tick_params(axis='y',length=0);a.set_xlim(-.01,.58)
for ax in [b,c]:ax.set_yticklabels([]);ax.tick_params(axis='y',length=0)
b.axvline(0,color='#555555',lw=1);b.set_xlim(-.058,.105);b.set_xticks([-.05,0,.05,.10]);c.axvline(5,color='#777777',ls=':',lw=1);c.set_xlim(-2,51)
a.set_title('(a) Same collection length',loc='left',fontweight='bold',pad=14)
b.set_title('(b) Minimax with 5%-Brier allowance',loc='left',fontweight='bold',pad=14)
c.set_title('(c) Actual Brier reward sacrificed',loc='left',fontweight='bold',pad=14)
a.set_xlabel(r'Worst four-step error $A_{3,4}$'+'\nlower is better',labelpad=9)
b.set_xlabel(r'$A_{3,4}$(Brier5) − $A_{3,4}$(native)'+'\npositive favors the native method',labelpad=9)
c.set_xlabel('Percent of the attainable Brier reward range\nnormalized separately within each class',labelpad=9)
fig.suptitle('Finite objectives select different reusable evidence',x=.21,ha='left',y=.981,fontsize=19,fontweight='bold')
fig.text(.21,.949,'22 supplied model classes; actual world unknown. Three collected action–observation pairs; all depth-four targets audited.',fontsize=10.4)
fig.text(.21,.927,'Native selection uses only depth-three targets. Complete favorable controls; unequal reward sacrifices remain visible.',fontsize=10.4)
handles=[Line2D([0],[0],marker=markers[m],color=colors[m],lw=0,markersize=5,label=names[m]) for m in methods+['face_brier_0.05']]
fig.legend(handles=handles,loc='upper left',bbox_to_anchor=(.206,.912),ncol=3,frameon=False,fontsize=9.5)
fig.text(.21,.105,'Against Brier5: weighted native 16 wins / 6 losses; minimax 18 wins / 1 tie / 2 losses / 1 mixed representative comparison.',fontsize=10)
fig.text(.21,.08,'Reward-matched controls are a separate diagnostic. Panel (c) does not assert equal reward or computation cost.',fontsize=9.5)
fig.text(.21,.052,'Post-design presentation of completed data. Intervals enclose saved representatives and numerical bounds, not all optima or statistical uncertainty.',fontsize=9)
fig.text(.21,.032,'Original profiles and new repairs have different witness-retention boundaries. These finite objectives and audits do not establish eventual J_w optimality.',fontsize=9,color='#555555')
for ext in ['pdf','png']:fig.savefig(HERE/f'CANDIDATE_22_COMPLETE.{ext}',dpi=175,facecolor='white')
plt.close(fig)
