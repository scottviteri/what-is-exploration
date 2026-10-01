# Supplied-model finite-budget quality comparison

Generated {{timestamp}}. Snapshot status: **{{snapshot_status}}**.

This report includes every frozen model, method and applicable checkpoint. It
compares known-model planning at collection length three using held-out native
experiments of depth four. It does not test unknown-model learning, eventual
exploration, or an efficient implementation of the complete native score.

There are {{model_count}} coupled parameter settings and two independent random
seed families, {{seed_families}}. Settings sharing a seed are not independent
replicates. Targets, solver iterations and repeated budgets are not replicates.
No significance test, population confidence interval, or general superiority
claim is made.

## Coverage before outcomes

{{coverage}}

There are {{expected_rows}} expected scientific endpoint rows. Every row, including
missing policies, late evidence, failed validation and unfinished audits, is in
[endpoints.csv](endpoints.csv). {{structural_note}}
The frozen design expects {{expected_bindings}} audit bindings; {{observed_bindings}} are present.
Every observed binding remains in [all_audit_bindings.csv](all_audit_bindings.csv).
Planning failures and later failures are retained even when an earlier checkpoint
has valid evidence.

An exhaustive audit requires all 32,768 depth-four deterministic interventions,
its complete worker status, and independent validation. A valid partial audit
retains its largest attained lower witness and a global full-revelation decoder
upper, or the universal upper one. The maximum of a partial subset's upper bounds
is never used as the full audit upper. These are repaired floating-point witness
intervals, not exact outward-rounded certificates or statistical error bars.

## Primary 40-second comparison

Lower deficiency is better. W/L/U/M means **numerically separated win / loss /
overlap or separation below margin / unavailable**. A win requires the method's
upper bound to be below the baseline's lower bound by more than `1e-6`; a loss
requires the reverse separation. Overlap is unresolved, not evidence of equality.
Each count concerns the twelve fixed model settings; all individual intervals and
paired differences are in [paired_comparisons.csv](paired_comparisons.csv).

{{primary_table}}

Information gain and posterior Brier use their full finite-horizon Bayesian
objectives and the same supplied models and prior. Uniform actions remain an
explicit control. Baseline successes and native-method losses are retained.
The returned reward-optimal baseline representative is distinguished from the
separately computed reward-face controls below.

## Earlier checkpoints

The two- and ten-second endpoints use only policies whose complete selected-target
audit finished by that deadline. Later evidence is never backdated. Different
methods can have different coverage; missingness does not receive a favorable
score and is not removed from denominators.

{{earlier_tables}}

## Adaptive averages are secondary

These average executed realization weights, then replay the induced causal
policy. They do not average conditional action rows. Each average requires its
own in-budget decoder audit. They are secondary endpoints, not replacements
chosen after seeing held-out outcomes, and have no asserted minimax or full-score
regret guarantee.

{{secondary_table}}

## Reward-face controls

Each control minimizes training-library maximum deficiency while retaining the
information or Brier reward within 0%, 1%, or 5% of its attainable reward range.
Selection uses training targets only. These are computed representatives of
numerical near-optimal reward sets, not the complete set of exact reward optima.
The nominal zero face permits `1e-10` numerical reward slack; actual returned
rewards, repair mixtures, threshold shortfalls and planning gaps are retained
per setting in the endpoint table. Solver/decoder errors remain numerical.

{{face_comparisons}}

{{face_diagnostics}}

A nonzero selected planning gap remains an optimization limitation. The paired
CSV retains each method’s planning gap and evidence-availability time alongside
its held-out interval. Neither a
small gap nor one favorable face representative establishes an all-optima claim.

## What the native methods actually score

Fixed weights, inverse-cost adaptation and hard-target adaptation emphasize the
same 131 supplied targets, plus a fixed `1/20` positive rich background. Original
selected background coefficients are retained. The omitted background weight is
exactly `{{omitted_fraction}}`, approximately **{{omitted_float}}**. Thus a small
selected-objective gap does not establish a comparably small full-objective gap.
The CSV retains the gap and omitted mass separately and their numerical sum where
available; no finite-to-eventual guarantee is inferred.

The direct minimax method instead optimizes maximum deficiency on this finite
library. It is a finite-library benchmark, not a rich weighted native score.
The held-out depth-four audit is common to every method and is not used for
planning, weight selection, target selection, checkpoint choice, or face selection.

Adaptive methods change the common target weights after audited rounds. Their
primary endpoint is the last fully audited iterate; fixed/minimax methods retain
the best incumbent under their unchanged training objective. Target-level cuts
can be reused, while aggregate lower bounds must correspond to the current
weights. Cost adaptation includes its computation budget; it does not establish
that inexpensive targets are the right capability preferences.

## Figures and complete records

Each figure has PDF and PNG counterparts. Points locate interval midpoints for
plotting only; comparisons use the endpoints. Hollow symbols indicate partial
audits, and crosses below an axis mark unavailable endpoints rather than zero
loss. Paired plots display all twelve classes, including unfavorable outcomes.

{{plots}}

- [Endpoint records](endpoints.csv): every method, budget, model, bound, availability and failure.
- [Paired comparisons](paired_comparisons.csv): individual differences and interval classifications.
- [Planning processes](planning_processes.csv): wall time, planner status, checks, errors and export time.
- [Audit bindings](all_audit_bindings.csv): all deduplicated-policy aliases and structural placeholders.
- [Machine-readable summary](summary.json): input hashes, scope, all records and integrity state.

## Missing and rejected evidence

{{missing_table}}

{{failure_table}}

## Integrity and timing

Planning time includes supplied-model geometry, target construction and planning;
interpreter import and certificate serialization are reported separately. Audit
cost is additional evaluation cost, not hidden planning work. Audit deduplication
reuses only bit-identical acquired experiment matrices within one model after each
policy independently replays; it never discounts planning time.

The report requires passing planning replay and held-out audit validation before
using an endpoint in a paired comparison. Changed model, policy or planning input
bindings are flagged. A report generated before the final frozen-input check or
while inputs change is provisional. These checks validate this finite numerical
snapshot; they do not prove an efficient solver, a general runtime bound, or a
successful learner for the full native objective.

```json
{{integrity}}
```
