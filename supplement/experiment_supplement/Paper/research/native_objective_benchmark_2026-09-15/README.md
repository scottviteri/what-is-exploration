# Fixed native objective across varied environments

Benchmark arrays, certificates, JSON/CSV outputs and figures are versioned
alongside the source scripts, protocol and analysis notes. The saved outputs
include every registered case and endpoint; the NPZ arrays use lossless
compression. The reproduction commands below regenerate and audit the evidence.

15 September 2026. [Frozen protocol](PROTOCOL.md), [all endpoints](all_endpoints.csv),
[machine-readable summary](summary.json), [independent audit](results/audit.json).

[Follow-up analysis: selected policies, task alignment and capability tradeoffs](analysis/README.md).

## Question and result

the lead author asked whether the proposed objective selects better evidence across varied
environments. This first experiment fixes one 16-target weighted native loss and
compares it with information gain, Brier gain, predictive surprisal, first-visit
reward and native minimax. Each objective is optimized over every randomized
history-dependent three-step policy on the same four-world interface.

**The predefined broad-benefit screening rule fails.** This result concerns the
specified finite objective and cases. It neither proves a general reward ranking
nor rules out a better target/weight construction. It is not a learned algorithm
or an experiment optimizing the infinite eventual J_w.

There are 60 objective optima and 720 complete decision endpoints across ten cases:
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
| native_minimax | 0% | 6 / 3 / 1 | +1.113 |
| native_minimax | 1% | 5 / 1 / 4 | +0.787 |
| native_minimax | 5% | 5 / 1 / 4 | -0.141 |
| information | 0% | 2 / 4 / 4 | +1.187 |
| information | 1% | 1 / 1 / 8 | +0.774 |
| information | 5% | 2 / 1 / 7 | -0.170 |
| brier | 0% | 0 / 5 / 5 | -0.278 |
| brier | 1% | 0 / 1 / 9 | -0.684 |
| brier | 5% | 0 / 1 / 9 | -1.651 |
| surprisal | 0% | 6 / 3 / 1 | +4.304 |
| surprisal | 1% | 6 / 1 / 3 | +4.041 |
| surprisal | 5% | 6 / 1 / 3 | +3.439 |
| first_visit | 0% | 7 / 3 / 0 | +5.087 |
| first_visit | 1% | 7 / 1 / 2 | +4.605 |
| first_visit | 5% | 7 / 1 / 2 | +3.336 |

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
