#!/usr/bin/env python3
"""Standalone finite-optimal-profile and certified-envelope research figure."""
from pathlib import Path
import json
from fractions import Fraction
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
HERE=Path(__file__).resolve().parent
plt.rcParams.update({'font.size':10,'axes.spines.top':False,'axes.spines.right':False,'pdf.fonttype':42})
fig,(ax,bx)=plt.subplots(1,2,figsize=(10,3.6),gridspec_kw={'width_ratios':[1,1.35]})
t=np.linspace(0,.072,100)
ax.plot(t,.072-t,color='#225e79',lw=2.6)
ax.scatter([0,.036,.072],[.072,.036,0],color='#225e79',s=35,zorder=3)
ax.annotate('Same scored profile can\nhide different experiments',xy=(.036,.036),xytext=(.031,.067),fontsize=8.5,arrowprops={'arrowstyle':'-','color':'#666'})
ax.set(xlabel='LLL deficiency',ylabel='RRR deficiency',xlim=(-.004,.08),ylim=(-.004,.08),title='Exact scored frontier')
ax.set_aspect('equal');ax.set_xticks([0,.036,.072]);ax.set_yticks([0,.036,.072]);ax.grid(alpha=.15)
lower=.072
upper=[.079071,.07384,.072000001123]
labels=['General full-count transfer','Native-optimal count decoder','Native-optimal history decoder']
for y,(u,label) in enumerate(zip(upper,labels)):
 bx.plot([lower,u],[y,y],lw=3,color=['#8c9eaa','#477993','#163f5b'][y])
 bx.plot([u],[y],marker='|',markersize=13,color='#163f5b',mew=2)
 bx.scatter([lower],[y],s=24,color='#163f5b',zorder=3)
bx.axvline(lower,color='#777',ls=':',lw=1)
bx.set_yticks(range(3),labels);bx.invert_yaxis();bx.set(xlim=(.0713,.080),xlabel='Worst adaptive-target deficiency',title='Certified intervals on the exact optimizer set')
bx.set_xticks([.072,.074,.076,.078,.080]);bx.grid(axis='x',alpha=.15)
bx.annotate('Width < 2 × 10⁻⁹',xy=(lower,2),xytext=(.074,1.85),fontsize=9,arrowprops={'arrowstyle':'-','color':'#666'})
fig.tight_layout(w_pad=2)
fig.savefig(HERE/'adaptive_envelope.pdf',bbox_inches='tight')
fig.savefig(HERE/'adaptive_envelope.png',dpi=180,bbox_inches='tight')
