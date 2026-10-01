"""Render a candidate figure from one snapshot of verified follow-up results."""
from pathlib import Path
import csv,json,math
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D

HERE=Path(__file__).resolve().parent
A=json.loads((HERE/'COMBINED_STATUS.json').read_text());cases=A['case_order']
methods=['uniform','information','brier','pseudo_count','weighted128','minimax']
names=['Uniform','Information','Brier','Pseudo-count','Weighted\nnative (128)','Finite\nminimax']
points={}
for row in A['figure_points']:
 points[row['case'],row['method']]={'interval':[float(row['lower']),float(row['upper'])],'representatives':len(row['cells'].split(';')),'cells':row['cells'].split(';')}
short=[]
for c in cases:
 if c.startswith('fresh'):
  parts=c.split('_');seed=int(parts[2]);q=parts[3][1:];alpha=parts[5][1:];short.append(f'Fresh Q={q}, α={alpha}, #{seed%10+1}')
 elif c.startswith('hmm'):short.append(c.replace('hmm_','Existing HMM ').replace('_',', α='))
 else:short.append(c.replace('_', ' '))
matrix=np.full((len(cases),len(methods)),np.nan)
rows=[]
for i,c in enumerate(cases):
 for j,m in enumerate(methods):
  p=points.get((c,m))
  if p:
   lo,hi=p['interval'];matrix[i,j]=hi
   rows.append(dict(case=c,label=short[i],method=m,lower=lo,upper=hi,representatives=p['representatives'],cells=';'.join(p['cells'])))
with (HERE/'figure_data.csv').open('w',newline='') as f:
 w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)

plt.rcParams.update({'font.size':9,'font.family':'DejaVu Sans','axes.spines.top':False,'axes.spines.right':False,'pdf.fonttype':42,'ps.fonttype':42})
fig=plt.figure(figsize=(14,8.7));gs=fig.add_gridspec(1,2,width_ratios=[1.55,1],left=.19,right=.96,bottom=.21,top=.86,wspace=.16)
ax=fig.add_subplot(gs[0,0]);bx=fig.add_subplot(gs[0,1],sharey=ax)
cmap=plt.get_cmap('viridis_r').copy();cmap.set_bad('#eeeeee')
vmax=max(.5,math.ceil(np.nanmax(matrix)*10)/10)
im=ax.imshow(np.ma.masked_invalid(matrix),vmin=0,vmax=vmax,cmap=cmap,aspect='auto')
ax.set_xticks(range(len(methods)),names,rotation=35,ha='right',fontsize=8)
ax.set_yticks(range(len(cases)),short,fontsize=8)
ax.tick_params(axis='both',length=0,pad=5)
for i in range(len(cases)):
 for j in range(len(methods)):
  x=matrix[i,j]
  if np.isnan(x):ax.text(j,i,'—',ha='center',va='center',color='#aaaaaa',fontsize=8)
  else:
   p=points[(cases[i],methods[j])];spread=p['interval'][1]-p['interval'][0]
   ax.text(j,i,f'{x:.3f}'+('†' if spread>2e-6 else ''),ha='center',va='center',fontsize=6.7,color='white' if x/vmax>.47 else '#14232c')
ax.axhline(9.5,color='white',lw=2);ax.set_title('(a) Longer targets that did not select the policy',loc='left',pad=12,fontweight='bold',fontsize=11)
cbax=fig.add_axes([.24,.105,.29,.017]);cb=fig.colorbar(im,cax=cbax,orientation='horizontal');cb.set_label('Worst-target deficiency  (lower is better)',fontsize=9);cb.ax.tick_params(labelsize=8)

colors={'weighted128':'#bb721c','minimax':'#236b9a'}
for arm in colors:
 for base in ['brier','face_brier_0']:
  comp=next(x for x in A['comparisons'] if x['arm']==arm and x['baseline']==base )
  for r in comp['pairs']:
   i=cases.index(r['case']);lo=r['baseline_interval'][0]-r['arm_interval'][1];hi=r['baseline_interval'][1]-r['arm_interval'][0];mid=(lo+hi)/2
   off=(-.18 if arm=='weighted128' else .18)+(-.055 if base=='brier' else .055)
   bx.errorbar(mid,i+off,xerr=np.array([[max(0,mid-lo)],[max(0,hi-mid)]]),fmt='o' if base=='brier' else 'D',markersize=4.5,color=colors[arm],markerfacecolor=colors[arm] if base=='brier' else 'white',markeredgewidth=1,elinewidth=1,capsize=2,zorder=3)
bx.axvline(0,color='#555555',lw=1);bx.axhline(9.5,color='#bbbbbb',lw=1)
bx.grid(axis='x',color='#dddddd',lw=.6);bx.tick_params(axis='y',left=False,labelleft=False)
bx.set_xlabel('Brier error − native-method error\npositive values favor the native method',labelpad=10)
bx.set_title('(b) Comparison with Brier, including favorable selection',loc='left',pad=12,fontweight='bold',fontsize=10)
bx.set_ylim(len(cases)-.5,-.5)
handles=[Line2D([0],[0],marker='o',color='none',markerfacecolor=colors[a],markeredgecolor=colors[a],label=l,markersize=6) for a,l in [('weighted128','Weighted native'),('minimax','Finite minimax')]]
handles += [Line2D([0],[0],marker='o',color='none',markerfacecolor='#555555',markeredgecolor='#555555',label='Default Brier selection',markersize=6),Line2D([0],[0],marker='D',color='none',markerfacecolor='white',markeredgecolor='#555555',label='Favorable Brier selection on 3-step audit',markersize=5)]
fig.legend(handles=handles,loc='lower right',bbox_to_anchor=(.975,.068),frameon=False,fontsize=8,ncol=2,columnspacing=1.4,handletextpad=.4)
fig.suptitle('Follow-up comparison — verified finite-policy results',x=.19,ha='left',y=.98,fontsize=14,fontweight='bold')
fig.text(.19,.932,'Collection: 3 observations. Evaluation: all 32,768 four-step target policies. The actual model remains unknown.',fontsize=10)
fig.text(.19,.895,'Missing entries are incomplete comparisons, not zero error. Each row is one supplied hypothesis class.',fontsize=9,color='#555555')
fig.text(.19,.019,'Cells show upper bounds across verified representatives; intervals are not confidence intervals. † marks representative spread; see figure_data.csv.\nFavorable Brier selection permits 1e−10 numerical reward slack. These are finite objectives, not complete-return or eventual J_w results.',fontsize=8,color='#444444')
fig.savefig(HERE/'FOLLOWUP_FIGURE.png',dpi=170);fig.savefig(HERE/'FOLLOWUP_FIGURE.pdf');plt.close(fig)
print('Created figure with',len(rows),'available method/class entries of',len(cases)*len(methods))
