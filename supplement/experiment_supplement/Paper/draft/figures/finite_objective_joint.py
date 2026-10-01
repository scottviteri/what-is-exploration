"""Paper-size joint figure and fixed-reference appendix; frozen saved data only."""
from pathlib import Path
import json,hashlib
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.colors import Normalize
from matplotlib.ticker import FuncFormatter
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2]
OLD=ROOT/'Paper/research/empirical_ending_checks_2026-09-23/COMPLETE_COMPARISON.json'
NEW=ROOT/'Paper/research/simulation_time_integration_2026-09-24/RESULTS.json'
def frozen(p,h):
    b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,str(p);return json.loads(b)
d=frozen(OLD,'2f606d871c87df27f660fdd4b8ab7b0592628d09f39999d8d5cf5805c330df4a')
r=frozen(NEW,'c46d876ba1f25b3c83c2d1918013e27e257b498104e6a61874d94087389ce25e')
cases=d['cases'];assert cases==r['cases'];methods=r['methods']
ix={(x['case'],x['method']):x for x in d['points']}
comp={(x['arm'],x['baseline']):{v['case']:v for v in x['pairs']} for x in d['comparisons']}
by={(x['case'],x['method'],x['t']):x for x in r['records']}
co={x['id']:x for x in r['compatibility']}
colors=dict(information='#0072B2',brier='#D55E00',pseudo_count='#E69F00',uniform='#777777',weighted128='#009E73',minimax='#CC79A7',brier5='#333333')
markers=dict(information='o',brier='s',pseudo_count='^',uniform='x',weighted128='D',minimax='P',brier5='o')
names=dict(information='World information',brier='World-posterior Brier',pseudo_count='Categorical count',uniform='Uniform actions',weighted128='Native mean (128)',minimax='Native maximum (128)')
labels=[]
for i,case in enumerate(cases):
    if case.startswith('fresh'):
        _,_,seed,q,_,alpha=case.split('_');label=f'{q}, c={float(alpha[1:]):g}, draw {int(seed)%10+1}'
    elif case.startswith('hmm'):
        _,seed,alpha=case.split('_');label=f'HMM {seed}, c={float(alpha):g}'
    else:
        family,x,y=case.split('_');family={'sensors':'Sensors','delayed':'Delay','irreversible':'Irrev.'}[family];label=f'{family} ({float(x):g}, {float(y):g})'
    labels.append(f'{i+1:02d}  {label}')
plt.rcParams.update({'font.size':7.5,'axes.spines.top':False,'axes.spines.right':False,'pdf.fonttype':42})
layout={}
def finish(fig,name,minimum):
    fig.canvas.draw();renderer=fig.canvas.get_renderer();outside=[]
    for text in fig.findobj(matplotlib.text.Text):
        if not text.get_visible() or not text.get_text():continue
        b=text.get_window_extent(renderer)
        if b.x0<-.5 or b.y0<-.5 or b.x1>fig.bbox.width+.5 or b.y1>fig.bbox.height+.5:outside.append(text.get_text())
    assert not outside,outside
    layout[name]=dict(size_inches=fig.get_size_inches().tolist(),minimum_text_points=minimum,text_outside_canvas=outside)
    fig.savefig(HERE/(name+'.pdf'));fig.savefig(ROOT/'Paper/research/simulation_time_integration_2026-09-24'/(name+'.png'),dpi=180);plt.close(fig)
def point(ax,lo,hi,y,m,hollow=False):
    mid=(lo+hi)/2;ax.errorbar(mid,y,xerr=[[mid-lo],[hi-mid]],fmt=markers[m],color=colors[m],markersize=2.5,capsize=1,elinewidth=.65,markerfacecolor='white' if hollow else colors[m],markeredgewidth=.65)
def error(case,method,t,target):return next(a for a in by[case,method,t]['audits'] if a['reference']==target)
fig=plt.figure(figsize=(5.5,7.25))
gs=fig.add_gridspec(1,3,left=.285,right=.985,top=.837,bottom=.38,width_ratios=[1.05,1,1],wspace=.26)
a,b,c=axes=[fig.add_subplot(gs[0,k]) for k in range(3)]
for i,case in enumerate(cases):
    for j,m in enumerate(methods):x=ix[case,m];point(a,x['lower'],x['upper'],i+(j-2.5)*.13,m)
    for j,m in enumerate(['weighted128','minimax']):
        x=comp[m,'face_brier_0.05'][case];point(b,x['lower'],x['upper'],i+(j-.5)*.22,m)
    for j,(m,k) in enumerate([('weighted128','weighted128'),('minimax','minimax'),('brier5','face_brier_0.05')]):
        x=ix[case,k];lo=x['brier_sacrifice_min'];hi=x['brier_sacrifice_max']
        if lo is not None:point(c,max(0,lo)*100,max(0,hi)*100,i+(j-1)*.2,m,hollow=m=='brier5')
        elif j==0:c.text(25,i,'constant',ha='center',va='center',fontsize=7)
    for ax in axes:
        if i%2==0:ax.axhspan(i-.5,i+.5,color='#f3f3f3',zorder=0)
for ax in axes:
    ax.set_ylim(21.6,-.6);ax.set_yticks(range(22));ax.tick_params(axis='y',length=0);ax.tick_params(axis='x',labelsize=7,length=2);ax.grid(axis='x',alpha=.16);ax.axhline(9.5,color='#888',lw=.6)
a.set_yticklabels(labels,fontsize=7.1)
for ax in (b,c):ax.set_yticklabels([])
a.set_xlim(-.015,.575);a.set_xticks([0,.25,.5]);b.set_xlim(-.058,.105);b.set_xticks([-.05,0,.05,.1]);b.axvline(0,color='#777',lw=.7)
b.xaxis.set_major_formatter(FuncFormatter(lambda x,pos:'0' if x==0 else f'{x:.2f}'.replace('-0.','-.').lstrip('0')))
c.set_xlim(-2,51);c.set_xticks([0,25,50]);c.axvline(5,color='#777',ls=':',lw=.7)
for ax,title,label in zip(axes,['(a) Audit error','(b) Audit difference','(c) Brier sacrifice'],['$A_{3,4}$\nlower is better','control − native\npositive favors native','% of reward range\n○ 5%-Brier control']):
    ax.set_title(title,fontsize=7.6,loc='left',pad=7,weight='bold');ax.set_xlabel(label,fontsize=7.1,labelpad=4)
fig.text(.035,.989,'Objective choice, collection budget, and reward cost',fontsize=9,weight='bold',va='top')
handles=[Line2D([0],[0],marker=markers[m],color=colors[m],ls='',markersize=3.4,label=names[m]) for m in methods]
fig.legend(handles=handles,ncol=2,frameon=False,loc='upper left',bbox_to_anchor=(.025,.964),fontsize=7.4,columnspacing=1.2,handletextpad=.4,labelspacing=.28)
fig.text(.035,.862,'3 collected interactions; hardest of all four-step targets. All 22 classes.',fontsize=7.3)
gs2=fig.add_gridspec(1,3,left=.095,right=.982,top=.265,bottom=.089,wspace=.55)
f,g,h=lower=[fig.add_subplot(gs2[0,k]) for k in range(3)]
for m in methods:
    yy=[r['thresholds']['0.02'][m][str(t)]['success'] for t in [3,4,5]]
    f.plot([3,4,5],yy,marker=markers[m],color=colors[m],ms=3,lw=1)
f.set_ylim(-.6,23);f.set_yticks([0,11,22]);f.set_ylabel('Classes passing',fontsize=7.2,labelpad=1)
f.set_title('(d) All six references',fontsize=7.6,loc='left',weight='bold',pad=7)
for ax,case,m,target,title in [(g,'delayed_0.1_0.1','brier','brier','(e) Delay (.1, .1)'),(h,'irreversible_0.1_0.1','information','brier','(f) Irrev. (.1, .1)')]:
    vals=[error(case,m,t,target) for t in [3,4,5]];ax.plot([3,4,5],[v['upper'] for v in vals],color=colors[m],marker=markers[m],lw=1,ms=3)
    ax.axhline(.02,color='#777',ls=':',lw=.7);ax.set_ylim(-.008,.26);ax.set_yticks([0,.1,.2]);ax.set_title(title,fontsize=7.6,loc='left',weight='bold',pad=7)
    ax.set_ylabel('Reference error',fontsize=7.2,labelpad=1)
    ax.text(.04,.94,('Brier → Brier' if m=='brier' else 'Information → Brier'),transform=ax.transAxes,fontsize=6.9,va='top')
q=co['case_01__t4__brier__to_brier'];g.plot(4,q['cap_upper'],marker='*',color='#222',ms=6,ls='')
q=co['case_02__t5__information__to_brier'];h.plot(5,q['cap_upper'],marker='*',color='#222',ms=6,ls='')
for ax in lower:ax.set_xticks([3,4,5]);ax.set_xlabel('Collection budget',fontsize=7.2,labelpad=2);ax.tick_params(labelsize=7,length=2);ax.grid(alpha=.14)
fig.text(.035,.307,'Fresh policy at each budget; targets remain fixed three-step records.',fontsize=7.3)
fig.text(.035,.039,'(d) Error ≤ .02.  ★ costs: 0.47% of max. Brier gain; ≈0 information.',fontsize=7.1)
fig.text(.035,.014,'Matched control comparison remains 6 wins / 1 tie / 15 losses (appendix).',fontsize=7.1)
finish(fig,'finite_objective_joint',6.9)
# The two directions above t=3 involve distinct source/reference pairs.
fig=plt.figure(figsize=(5.5,6.2));ax=fig.add_axes([.315,.16,.66,.66]);data=np.zeros((22,6));brackets=[]
for i,case in enumerate(cases):
    for group,(m,target) in enumerate([('brier','weighted128'),('weighted128','brier')]):
        for k,t in enumerate([3,4,5]):
            v=error(case,m,t,target);data[i,3*group+k]=v['upper'];brackets.append(v['upper']-v['lower'])
im=ax.imshow(data,cmap='YlGnBu',vmin=0,vmax=.36,aspect='auto')
for i in range(22):
    for j in range(6):ax.text(j,i,f'{data[i,j]:.3f}',ha='center',va='center',fontsize=7.1,color='white' if data[i,j]>.18 else '#111')
ax.set_yticks(range(22),labels,fontsize=7.1);ax.set_xticks(range(6),[3,4,5,3,4,5],fontsize=7.3);ax.tick_params(length=0);ax.axvline(2.5,color='white',lw=2)
ax.set_xlabel('Collector interactions; each target has three interactions',fontsize=7.5)
fig.text(.035,.975,'Errors to fixed competing records',fontsize=9,weight='bold',va='top')
fig.text(.035,.929,'All 22 classes; independently selected collector at each budget.',fontsize=7.5)
fig.text(.48,.850,'Brier → native mean',ha='center',fontsize=7.7);fig.text(.812,.850,'Native mean → Brier',ha='center',fontsize=7.7)
cb=fig.colorbar(im,cax=fig.add_axes([.36,.058,.54,.017]),orientation='horizontal');cb.ax.tick_params(labelsize=7,length=2);cb.set_label('Simulation error (upper bound; smaller is better)',fontsize=7.2,labelpad=1)
finish(fig,'finite_objective_budget_matrix',7.1)
(HERE/'finite_objective_joint_layout.json').write_text(json.dumps(dict(status='passed',figures=layout,max_matrix_bracket=max(brackets),inputs={str(OLD.relative_to(ROOT)):hashlib.sha256(OLD.read_bytes()).hexdigest(),str(NEW.relative_to(ROOT)):hashlib.sha256(NEW.read_bytes()).hexdigest()},scope='Physical canvas/text checks; separate visual inspection required.'),indent=2)+'\n')
