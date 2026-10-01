#!/usr/bin/env python3
"""Summarize every preregistered condition; preserve losses and ties."""
import csv
import json
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

HERE=Path(__file__).resolve().parent
OUT=HERE/'results'
NATIVE='native_weighted'
STRONG=['information','brier']
FRACTIONS=[0.,.01,.05]


def main():
    design=json.loads((OUT/'design.json').read_text())
    cases=[]
    for c in design['cases']:
        p=OUT/c['name']/'results.json'
        if p.exists():
            d=json.loads(p.read_text())
            if d['status']=='complete':cases.append(d)
    if len(cases)!=len(design['cases']):
        raise RuntimeError(f'Incomplete design: {len(cases)}/{len(design["cases"])} cases')
    values={(d['name'],r['objective'],r['fraction'],r['purpose']):r['value']
            for d in cases for r in d['endpoints']}
    families=sorted(set(d['family'] for d in cases))
    result={'status':'complete','scope':'Finite H=3 all-policy float64 comparison; no training or eventual claim.',
            'cases':len(cases),'objective_optima':sum(len(d['optima']) for d in cases),
            'decision_endpoints':sum(len(d['endpoints']) for d in cases),
            'comparisons':[],'family_comparisons':[],'screen_passed':True,
            'case_seconds':sum(d['seconds'] for d in cases)}
    for baseline in design['objectives']:
        if baseline==NATIVE:continue
        for fraction in FRACTIONS:
            diffs=np.array([values[d['name'],NATIVE,fraction,'mean_seven']-
                            values[d['name'],baseline,fraction,'mean_seven'] for d in cases])
            family_means=[]
            for family in families:
                selected=[diffs[i] for i,d in enumerate(cases) if d['family']==family]
                mean=float(np.mean(selected));family_means.append(mean)
                result['family_comparisons'].append(dict(baseline=baseline,fraction=fraction,
                                                         family=family,difference=mean))
            row=dict(baseline=baseline,fraction=fraction,
                     wins=int(np.sum(diffs>1e-6)),ties=int(np.sum(abs(diffs)<=1e-6)),
                     losses=int(np.sum(diffs < -1e-6)),
                     family_balanced_difference=float(np.mean(family_means)),
                     minimum_case_difference=float(diffs.min()),maximum_case_difference=float(diffs.max()))
            result['comparisons'].append(row)
            if baseline in STRONG and fraction in [0.,.01]:
                passed=np.mean(family_means)>1e-6 and min(family_means)>=-.01
                result['screen_passed'] = result['screen_passed'] and bool(passed)
    (HERE/'summary.json').write_text(json.dumps(result,indent=2)+'\n')
    with (HERE/'all_endpoints.csv').open('w') as f:
        writer=csv.DictWriter(f,fieldnames=['case','family','objective','fraction','purpose','value',
                                          'eta','threshold','solver_seconds'])
        writer.writeheader()
        for d in cases:
            for r in d['endpoints']:
                writer.writerow(dict(case=d['name'],family=d['family'],
                                     **{k:r[k] for k in writer.fieldnames[2:]}))
    matrices=[np.array([[100*(values[d['name'],NATIVE,f,'mean_seven']-
                              values[d['name'],baseline,f,'mean_seven']) for f in FRACTIONS]
                       for d in cases]) for baseline in STRONG]
    limit=max(.1,max(float(abs(m).max()) for m in matrices))
    fig,axs=plt.subplots(1,2,figsize=(10,6),sharey=True,layout='constrained')
    labels=[d['name'].replace('sensors_','Sensors ').replace('delayed_','Delayed ').replace('irreversible_','Irreversible ').replace('hmm_','HMM ').replace('_',', ') for d in cases]
    for ax,m,baseline in zip(axs,matrices,STRONG):
        im=ax.imshow(m,cmap='BrBG',vmin=-limit,vmax=limit,aspect='auto')
        ax.set_title('Native weighted minus '+('information gain' if baseline=='information' else 'Brier gain'))
        ax.set_xticks(range(3),['0%','1%','5%']);ax.set_xlabel('Allowed loss (% of feasible objective range)')
        ax.set_yticks(range(len(labels)),labels)
        for i in range(m.shape[0]):
            for j in range(3):
                ax.text(j,i,f'{m[i,j]:+.2f}',ha='center',va='center',fontsize=9,
                        color='white' if abs(m[i,j])>.6*limit else 'black')
    fig.suptitle('Worst selected-policy mean accuracy on seven later decisions\nH = 3; difference in percentage points',fontsize=13)
    fig.colorbar(im,ax=axs,shrink=.7,label='Positive favors native; negative favors baseline')
    fig.savefig(HERE/'strong_baseline_comparison.png',dpi=170)
    fig.savefig(HERE/'strong_baseline_comparison.pdf')
    rows=[]
    for row in result['comparisons']:
        rows.append(f"| {row['baseline']} | {100*row['fraction']:.0f}% | {row['wins']} / {row['ties']} / {row['losses']} | {100*row['family_balanced_difference']:+.3f} |")
    report='''# Fixed native objective across varied environments

15 September 2026. [Frozen protocol](PROTOCOL.md), [all endpoints](all_endpoints.csv),
[machine-readable summary](summary.json), [independent audit](results/audit.json).

[Follow-up analysis: selected policies, task alignment and capability tradeoffs](analysis/README.md).

## Question and result

the lead author asked whether the proposed objective selects better evidence across varied
environments. This first experiment fixes one 16-target weighted native loss and
compares it with information gain, Brier gain, predictive surprisal, first-visit
reward and native minimax. Each objective is optimized over every randomized
history-dependent three-step policy on the same four-world interface.

**The predefined broad-benefit screening rule %s.** This result concerns the
specified finite objective and cases. It neither proves a general reward ranking
nor rules out a better target/weight construction. It is not a learned algorithm
or an experiment optimizing the infinite eventual J_w.

There are %d objective optima and %d complete decision endpoints across ten cases:
three repeatable sensor models, two delayed-access models, two irreversible-choice
models and three recurring controlled hidden-state models. Sensor parameters,
random seeds, target weights, baselines and evaluation tasks were frozen before
these outcomes. Every planned case is included.

## Primary comparison

For a fixed policy, compute the best guessing accuracy for each of the seven
nonconstant binary labels on four worlds (modulo complements), under a uniform
evaluation prior. Average those seven accuracies, then minimize that mean over
every policy within the intrinsic-return tolerance. This is one worst mean across
the selected family, not a mean of independently worst policies. The tasks are
not terms in any intrinsic objective; their informational content can overlap
the scored native targets.

Positive differences favor the weighted native candidate. The family-balanced
mean first averages cases within each of the four structural families, then
averages families equally. Wins/ties/losses use absolute tolerance 1e-6.

| Baseline | Allowed regret | Native wins / ties / losses (10 cases) | Family-balanced change (percentage points) |
|---|---:|---:|---:|
%s

![Every case against the strongest baselines](strong_baseline_comparison.png)

The screening rule required a positive family-balanced change against BOTH
information and Brier gain at zero and one-percent regret, with no structural
family losing over one percentage point at either tolerance. It is a descriptive
decision rule, not a significance test or an estimate over natural environments.
Five-percent results and weaker baselines are retained even when unfavorable.

## What the separate capability results add

The primary average-performance test fails against Brier gain: at nominal zero
regret, native has no wins, five ties and five losses; at one-percent regret it
has no wins, one tie and nine losses. Its positive family-balanced mean against
information gain is driven substantially by a delayed-access case and coexists
with more losing than winning cases. It should not be summarized as broad
superiority over posterior objectives.

The predefined individual-task diagnostics nevertheless expose a useful
protection. In the symmetric irreversible case, at nominal zero regret, native
optimization guarantees approximately .736 for guessing either U or V. Information
and Brier each have separate worst U and worst V accuracies .5. Their mean-seven
scores all agree at about .710286. The two .5 endpoints can come from different
policies: always choose the other bit. This demonstrates balanced capability
protection without an average-score improvement or universal dominance.

In the delayed (.25,.1) case, native and Brier guarantee mean accuracy about
.814286, versus .710286 for information gain. This is a 10.4 percentage-point
improvement against information, with uniform planning and evaluation priors.
The same setting does not establish an advantage over Brier. Both examples are
illustrations within the full published grid, not replacements for the primary
screening result.

## What the candidate is

The objective scores all two one-action words, all four two-action words, all
eight three-action words, a recorded fair choice of L/R, and a recorded fair
choice of LLL/RRR. Weights are .1 for each one-action word and .05 for each
other target, totaling .9. They may be extended by .1 positive mass on a rich
countable native family, but this experiment supplies no uniform finite-time to
eventual approximation bound. The candidate is fixed across every environment.

The uniform planning prior is a strong control: a gain cannot be attributed
solely to making a world artificially rare for the posterior baselines. Full
feasible objective ranges are computed separately and saved; equal normalized
regret still does not mean equal training difficulty. Near-optimal policy sets
use an explicit 1e-8 numerical allowance in addition to the declared gap.

## Verification and boundaries

Every endpoint has a saved full-history policy and LP primal/dual certificate.
The audit independently reconstructs source and target laws from literal
transition/emission products, checks all certificates and decision values,
enumerates the 128 pure observation-contingency trees, and independently solves
every fixed-source decoder problem used to establish the native objective range.
Saved native optimizer pairs have both deficiency directions checked; those are
individual witnesses, not complete pairwise comparisons of selected sets.

Posterior exact optima are admissible under the finite-world/full-support
assumptions. An advantage on this decision suite therefore represents a choice
among capabilities, not strict Blackwell domination of an information optimum.
All computations are float64 rather than interval arithmetic. The audit reports
current residuals and hashes; it does not certify unrelated working-tree changes.

## Reproduce

From this directory, with NumPy, SciPy and Matplotlib installed:

```bash
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 compute.py
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 audit.py
python3 report.py
```

`compute.py --case NAME` runs one registered case. Source-hash matching is required
when resuming. `audit.py --case NAME` audits a completed case. The planner reuses
the preceding noisy-diagnostic LP infrastructure by import; original code and
outputs are preserved. `PROTOCOL.md` records a prospective H=4 extension, which
has not been run as part of this first experiment.
''' % ('passes' if result['screen_passed'] else 'fails',result['objective_optima'],result['decision_endpoints'],'\n'.join(rows))
    (HERE/'README.md').write_text(report)
    print(json.dumps({k:result[k] for k in ['cases','objective_optima','decision_endpoints','screen_passed']},indent=2))
    for row in result['comparisons']:
        if row['baseline'] in STRONG:print(row)


if __name__=='__main__':main()
