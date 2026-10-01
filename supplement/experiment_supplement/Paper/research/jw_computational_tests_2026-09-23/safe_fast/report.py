#!/usr/bin/env python3
import csv,hashlib,json,time
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
BASE=Path(__file__).resolve().parent
rows=json.load(open(BASE/'RESULTS.json'))['rows'];audit=json.load(open(BASE/'AUDIT.json'));lit=json.load(open(BASE/'LITERAL_AUDIT.json'))
assert audit['status']==lit['status']=='passed' and len(rows)==2448 and all(r['status']=='passed' for r in rows)
fields=['grid','schedule','eps_num','eps_den','d','H','N','M','candidate_q','q_lower','q_upper','safe1_loss_lower','safe1_loss_upper','retained_lower','candidate_retained_upper','full_optimum_upper','tail','full_regret_bound','solver_seconds','elapsed_seconds','IG_q_lower','IG_q_upper']
with (BASE/'results.csv').open('w') as f:
    writer=csv.DictWriter(f,fieldnames=fields);writer.writeheader()
    for r in rows:
        z={k:r[k] for k in fields if k in r and not isinstance(r[k],dict)}
        z.update(candidate_q=r['candidate_q']['float'],q_lower=r['all_full_optima_q_outer'][0]['float'],q_upper=r['all_full_optima_q_outer'][1]['float'],safe1_loss_lower=r['all_full_optima_safe1_loss_outer'][0]['float'],safe1_loss_upper=r['all_full_optima_safe1_loss_outer'][1]['float'],retained_lower=r['retained_lower']['float'],candidate_retained_upper=r['candidate_retained_upper']['float'],full_optimum_upper=r['full_optimum_upper']['float'],tail=r['omitted_weight']['float'],full_regret_bound=r['candidate_full_regret_bound']['float'])
        if 'information_gain' in r:z.update(IG_q_lower=r['information_gain']['all_optimal_q'][0],IG_q_upper=r['information_gain']['all_optimal_q'][1])
        writer.writerow(z)
primary=[r for r in rows if r['grid']=='primary'];colors={100:'#2166ac',20:'#d89018',4:'#8c2670'}
fig,axes=plt.subplots(2,3,figsize=(13.5,7.6),sharex=True,sharey=True)
for ax,d in zip(axes.flat,[None,1,2,4,8,16]):
    for e in (100,20,4):
        for schedule,style in [('fixed','-'),('moving','--')]:
            rr=sorted([r for r in primary if r['d']==d and r['eps_den']==e and r['schedule']==schedule],key=lambda r:r['H'])
            h=[r['H'] for r in rr];q=[r['candidate_q']['float'] for r in rr]
            ax.plot(h,q,style,color=colors[e],lw=1.3,alpha=.8)
            ax.fill_between(h,[r['all_full_optima_q_outer'][0]['float'] for r in rr],[r['all_full_optima_q_outer'][1]['float'] for r in rr],color=colors[e],alpha=.10)
    if d is not None:
        rr=sorted([r for r in primary if r['d']==d and r['eps_den']==4 and r['schedule']=='fixed'],key=lambda r:r['H'])
        hh=[r['H'] for r in rr];lo=[r['information_gain']['all_optimal_q'][0] for r in rr];hi=[r['information_gain']['all_optimal_q'][1] for r in rr]
        ax.scatter(hh,lo,marker='_',s=42,color='black',zorder=5);ax.scatter(hh,hi,marker='_',s=42,color='black',zorder=5)
        for h,l,u in zip(hh,lo,hi):
            if l<u:ax.vlines(h,l,u,color='black',alpha=.22,lw=2)
        ax.axvline(2*d-1,color='gray',lw=.7,alpha=.45)
    ax.set_title('One infinite world class' if d is None else f'Fixed finite class: {d} bits ({2**d:,} worlds)')
    ax.set_xscale('log',base=2);ax.set_xticks([1,2,4,8,16,32,64,128]);ax.set_xticklabels(['1','2','4','8','16','32','64','128']);ax.grid(alpha=.2);ax.set_ylim(-.045,1.045)
for ax in axes[:,0]:ax.set_ylabel('SAFE probability q')
for ax in axes[-1,:]:ax.set_xlabel('Collection/scoring horizon H (not solver time)')
handles=[Line2D([0],[0],color='black',ls='-',label='Fixed target emphasis'),Line2D([0],[0],color='black',ls='--',label='Moving FAST_H emphasis'),Line2D([0],[0],color='black',marker='_',ls='',label='Information-gain optimum endpoints')]+[Line2D([0],[0],color=colors[e],label=f'background mass ε={1/e:g}') for e in (100,20,4)]
fig.legend(handles=handles,loc='lower center',ncol=3,bbox_to_anchor=(.5,-.005),frameon=False)
fig.suptitle('SAFE/FAST: fixed weights, moving weights, and finite-world saturation\nLines: retained-LP candidates; shaded bands: certified outer ranges of full-objective optima',fontsize=12)
fig.tight_layout(rect=(0,.09,1,.93));fig.savefig(BASE/'optimizer_curves.pdf',bbox_inches='tight');fig.savefig(BASE/'optimizer_curves.png',dpi=160,bbox_inches='tight');plt.close(fig)
fig,axes=plt.subplots(1,2,figsize=(11,4.3))
for N,M in [(12,4),(8,4),(16,4),(12,2),(12,6)]:
    for ax,s in zip(axes,['fixed','moving']):
        rr=sorted([r for r in rows if r['d'] is None and r['eps_den']==4 and r['schedule']==s and r['N']==N and r['M']==M and r['H'] in (1,2,4,8,16,32,64,128)],key=lambda r:r['H'])
        idx=1 if s=='fixed' else 0
        ax.plot([r['H'] for r in rr],[r['all_full_optima_safe1_loss_outer'][idx]['float'] for r in rr],marker='o',ms=3,label=f'N={N}, M={M}')
        ax.set_xscale('log',base=2);ax.set_xlabel('Collection/scoring horizon H');ax.grid(alpha=.2)
axes[0].set_title('Fixed weights: upper bound on SAFE_1 loss');axes[0].set_yscale('log');axes[0].set_ylabel('Loss bound (tail included)')
axes[1].set_title('Moving weights: lower bound on SAFE_1 loss');axes[1].set_ylim(.48,.501)
axes[1].legend(fontsize=8);fig.suptitle('Prespecified truncation sensitivity, infinite worlds, ε=1/4\nBounds over all full-objective optimizers',fontsize=11);fig.tight_layout();fig.savefig(BASE/'truncation_sensitivity.pdf');fig.savefig(BASE/'truncation_sensitivity.png',dpi=160);plt.close(fig)

lines=[]
for e in (100,20,4):
    fx=[r for r in primary if r['d'] is None and r['eps_den']==e and r['schedule']=='fixed'];mv=[r for r in primary if r['d'] is None and r['eps_den']==e and r['schedule']=='moving']
    lines.append(f"| {1/e:g} | {next(r['H'] for r in fx if r['candidate_q']['float']>.999999)} | {max(r['all_full_optima_safe1_loss_outer'][1]['float'] for r in fx if r['H']>=3):.6g} | {min(r['all_full_optima_safe1_loss_outer'][0]['float'] for r in mv):.6g} |")
summary='\n'.join(lines)
maxgap=audit['max_retained_primal_dual_gap'];rss=max(r['peak_rss_kib'] for r in rows)/1024;runtime=json.load(open(BASE/'RESULTS.json'))['elapsed_seconds']
text=f'''# SAFE/FAST computational study

All **2,448 prospectively specified optimization cells** passed independent exact-rational
certificate replay. The compressed solver also agreed with literal full-record
decoder LPs in **356 cases**, including observation-dependent randomized later
actions. Their saved literal decoders and dual bounds were independently replayed
with exact fractions; the largest literal primal/dual gap was {lit['maximum_primal_dual_gap']:.3g}.

The controlled example distinguishes **changing the finite-time objective** from
**having insufficient time to solve a fixed objective**. With the frozen target
emphasis, the certified near-optimal retained candidate chooses SAFE initially
from H=3 onward. In the infinite-world version, the corresponding candidates
with emphasis moving to FAST_H choose FAST initially through H=128. These small
optimization problems have tightly certified global bounds. This is not
a general efficiency result or a benchmark showing a practical advantage over
information gain.

## Results, including uncertainty about the omitted targets

Both schedules use a fixed positive rich background. Fixed weighting is
`epsilon*b+(1-epsilon)*FAST_1`; moving weighting is
`epsilon*b+(1-epsilon)*FAST_H`. They agree at H=1. Target weighting is a declared
preference, not a canonical choice. The full dyadic-policy background and the
special-environment compression are explained in [DERIVATION.md](DERIVATION.md).
The latter is a new written argument, **not an additional Lean theorem**.

For the infinite-world primary grid, the following are outer bounds covering every
optimizer of the full countable objective, with the omitted tail and 1e-9 range
slack charged. “Candidate first SAFE” describes the retained-LP candidate, not an
exact characterization of the infinite sum's optimizer.

| Background epsilon | Candidate first SAFE horizon | Largest certified SAFE_1 loss upper bound, fixed weights, H>=3 | Smallest certified SAFE_1 loss lower bound, moving weights, all H |
|---|---:|---:|---:|
{summary}

The exact SAFE_1 capability error is `(1-q)/2`. On the infinite-world primary grid,
all retained candidates have q=0 for moving emphasis and q=1 for fixed emphasis from H=3; the table's
intervals show what the certified tail still permits for full-objective optima.
The existing Lean theorem proves persistent all-horizon loss for moving weights;
the numerical grid does not extend that theorem or prove an asymptotic limit.

![All primary curves](optimizer_curves.png)

The finite controls keep d fixed within each curve. For H>=2d-1, SAFE knows all d
unknown bits. Consequently every full native optimum has q=1 by the written
zero-loss/positive-SAFE-target argument; the numeric certificates include that
point. Exact finite-world information gain also selects SAFE by that horizon.
Earlier information-gain ties are shown as full endpoint intervals; a convenient
member of a tie is never substituted for all optima. The finite-class IG formula
and source setting are recorded in [PROTOCOL.md](PROTOCOL.md), using the pinned
Orseau et al. author PDF pp3-5. No uncountable prior or predictive surprisal is
silently substituted for that source objective.

The prespecified N/M sensitivity retains every cell. As truncation is refined,
the apparent plateau in a *certified upper bound* tightens; it is not an observed
persistent capability loss of the selected SAFE policy, whose exact loss is zero.

![Truncation certificates](truncation_sensitivity.png)

## What was checked

- [PROTOCOL.md](PROTOCOL.md) and [GRID.json](GRID.json) fixed all primary and sensitivity cells before outcomes.
- [RESULTS.json](RESULTS.json) and [results.csv](results.csv) retain every final result. All 2,448 final cells passed.
- [AUDIT.json](AUDIT.json) replays original rational weights, exact feasible candidate values, and global dual bounds from independently assembled constraint rows. Maximum retained primal/dual gap: {maxgap:.6g}.
- [crosschecks.json](crosschecks.json) compares the compressed 4-flow LP with actual finite full-record decoder LPs; [LITERAL_AUDIT.json](LITERAL_AUDIT.json) replays their witnesses with exact fractions.
- `cells/*.json.gz` stores all primal/dual witnesses. `crosscheck_witnesses/` stores actual full-record experiment matrices and decoders. No saved solver success flag is treated as a proof by itself.
- [RUN_METADATA.json](RUN_METADATA.json) pins the executed sources, relevant Lean declarations and primary information-gain source. No Lean or manuscript file was changed.

The retained master lower bound is B and its candidate feasible upper bound is U.
The full optimum is enclosed by `[B,U+tail]` and full regret by `U+tail-B`.
All-full-optimum q intervals are conservative sublevel-set bounds with explicit
1e-9 slack, not exact optimal faces. Rational replay makes these certificates
independent of floating-point feasibility tolerances. The rich-target reduction
still relies on the written proof and its finite crosschecks; it is not solver
verification in Lean.

## Resources and development history

The final grid took {runtime:.2f} wall seconds with at most four CPU workers pinned
to CPUs 12-15, one solver thread each, and a 4 GiB address-space ceiling per worker.
Peak reported worker RSS was {rss:.2f} MiB. No GPU was used: these are sparse linear
programs, not neural training. Per-cell solver and elapsed times are saved. H is
the number of physical interactions used for scoring; it is not a compute budget.

Two initial development runs exposed sign errors in the manually expanded dual
certificate through exact primal/dual assertions. Both complete runs, their
sources and every failure are preserved in `initial_implementation_failure/`
and `second_implementation_failure/`, explicitly rejected as evidence. The
objective and prospective grid did not change. The corrected full rerun passed
both production checks and a separately implemented generic exact constraint-row
audit. The independent literal-record checks passed before the optimization grid.

This study supplies no unknown-model learning algorithm, general runtime bound,
computable infinite-world acquisition deadline, or single-policy online assembly.
Its known interface admits a special exact compression, so inexpensive solutions
here must not be generalized to arbitrary controlled environments. Existing
fixed-weight and finite-world convergence results remain conditional Lean theorems;
finite experiments neither prove nor refute their asymptotic statements.
'''
(BASE/'README.md').write_text(text)
files=[p for p in BASE.rglob('*') if p.is_file() and p.name!='MANIFEST.json' and '__pycache__' not in p.parts]
manifest={'created_unix':time.time(),'files':len(files),'bytes':sum(p.stat().st_size for p in files),'sha256':{str(p.relative_to(BASE)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}}
(BASE/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('Report, figures, CSV and manifest written',manifest['files'],manifest['bytes'])
