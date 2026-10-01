# Finite computation for native objectives: completed study

23 September 2026. The tests show differences between computable native-objective
approximations and information gain, with substantial sensitivity to computation
budget. They do not establish an efficient general optimizer for eventual J_w.

The primary run contains **132 planning executions, 540 scientific endpoint rows,
and 300 distinct acquired experiments**. Every acquired experiment passed an
exhaustive audit of all 32,768 deterministic depth-four interventions: **9,830,400
intervention checks**, with no partial or failed audits in the completed corrected
run. An independent reporting checker passed 55,013 checks. Repeated baselines,
shared experiment matrices and multiple budgets are accounted for explicitly;
they are not additional independent experiments.

## Capability under finite planning budgets

These are supplied-model problems with three interactions, binary actions and
observations, three hidden physical states, and four or eight possible worlds.
The twelve parameter settings share **two independent seed families**. The
uniform-prior information and posterior Brier baselines optimize their actual
finite-horizon Bayesian rewards by dynamic programming. Native weighted methods
use 131 retained training targets with a fixed positive rich background whose
unretained coefficients are charged separately. Finite-library minimax is a
separate benchmark. Evaluation uses the worst deficiency over every depth-four
deterministic native intervention, without using those held-out outcomes for
planning or selection.

Entries below are **wins / losses / unresolved** against information gain, over
all twelve settings. Lower worst native deficiency is better. A win or loss
requires separation of the independently replayed numerical bounds by more than
1e-6; unresolved is not a tie or proof of equality.

| Method | 2 seconds | 10 seconds | 40 seconds |
| --- | ---: | ---: | ---: |
| Fixed native weights | 7 / 4 / 1 | 10 / 2 / 0 | 10 / 2 / 0 |
| Cost-adaptive weights | 4 / 7 / 1 | 10 / 2 / 0 | 10 / 2 / 0 |
| Hard-target weights | 4 / 7 / 1 | 9 / 3 / 0 | 10 / 2 / 0 |
| Finite-library minimax | 7 / 5 / 0 | 10 / 2 / 0 | 10 / 2 / 0 |

The short-budget failures matter. At two seconds both adaptive methods also lose
to uniform actions in eight settings. At forty seconds all three weighted methods
beat uniform actions in every setting, but each still loses twice to information
gain and twice to Brier. Cost adaptation beats fixed weights in eight settings at
forty seconds and loses four; hard-target adaptation splits six/six. Adaptation
is not uniformly preferable. Information and Brier produce byte-identical
acquired experiments in eight settings, so their similar results are not two
independent confirmations.

The computation costs differ sharply: baseline dynamic programming takes about
5 ms in these small supplied-model problems, excluding startup and output. At
the forty-second endpoint the median evidence-availability times are about 11.2 s
for fixed weights, 6.8 s for minimax, and 38–39 s for the adaptive methods. The
common allowance is a cap, not equal consumed work. Evaluation and supplementary
certificate checks are additional costs, never credited to planning.

[Complete primary report](quality_corrected/summary/REPORT.md) ·
[All endpoint records](quality_corrected/summary/endpoints.csv) ·
[Primary budget plot](quality_corrected/summary/deficiency_budgets_primary.pdf).
Plot intervals are numerical deficiency bounds, not statistical confidence
intervals. No significance or population-superiority claim is made.

## Baseline controls and the actual experimental order

Controls also seek better native capability while permitting 0%, 1%, or 5% loss
of the attainable information/Brier reward range. They use training targets only.
At forty seconds, fixed weights beat the 5% information control in eight settings
and lose four, compared with ten/two against the original information optimizer.
At two seconds the same comparison is four/eight. These controls are returned
policies; they do not characterize every exact or near-optimal reward optimizer.
The nominal zero face allows 1e-10 numerical slack.

Some exported static gaps attach the lower bound from the incumbent's original
iteration even though later in-budget iterations supply stronger bounds for the
same unchanged objective. Aggregating those already independently checked bounds
shows that **all 96 static forty-second endpoints have finite training-objective
gap upper bounds at most 8.1e-7**. The original exports remain visible. A large
original gap alone must not be described as demonstrated optimization failure.
Adaptive objectives are excluded from this aggregation because their weights
change. These bounds concern the training objective, not the held-out optimum
or eventual exploration.

A separate post-design diagnostic compared the records themselves in both
directions: all four native methods versus information, Brier and uniform, on
all twelve settings at forty seconds. **All 288 directional LPs passed independent
witness replay. Every one of the 144 pairs showed numerical same-time
incomparability**; the smallest directed lower bound was 0.00349552. Each record
therefore missed something reproducible from the other, to the stated numerical
precision. This includes all 127 scalar-audit wins and all 17 losses in those
comparisons. A scalar benchmark win is not native-process dominance.

At forty seconds, fixed weights also collect less expected world information
than the information optimizer in every setting: losses range from 0.00244 to
0.1198 bits. All 540 endpoint information and Brier values were independently
replayed. This makes the reward trade-off explicit.

[All reward-face comparisons](quality_corrected/reward_face_comparisons/README.md) ·
[Static certificate aggregation](quality_corrected/static_certificate_aggregation/README.md) ·
[Same-time experiment-order diagnostic](quality_corrected/same_time_order/results/REPORT.md) ·
[Information/Brier diagnostics](quality_corrected/reward_diagnostics/results/REPORT.md).

## What the certificates protect

The selected-target solver gap is not the full-objective regret. The omitted
background weight is approximately 0.04895. A separate replay bounds its actual
contribution more sharply using an identity-experiment decoder and the complete
depth-three deterministic target family. All 108 weighted checkpoints passed.
For fixed weights at forty seconds, the resulting numerical upper bound on regret
for the **full countable target sum at collection time three** ranges from
0.00243 to 0.00616, rather than the generic approximately 0.04895 bound.

That is a finite-prefix certificate. It is not eventual J_w regret, an absolute
zero-deficiency guarantee, a new Lean theorem, or an in-budget computation: this
extra replay took about 34 s in total, after the external audits. A nonzero
finite-prefix optimum and a target's possibly tiny weight still matter when
converting weighted loss to individual capability bounds.

[Certificate derivation and scope](quality_corrected/certificate_refinement/README.md) ·
[All refined bounds](quality_corrected/certificate_refinement/results/certificates.csv).

## Controlled examples and implementation tests

- **SAFE/FAST:** all 2,448 prespecified cells passed exact-rational certificate
  replay, with 356 literal full-record cross-checks. Fixed-emphasis retained
  candidates choose SAFE from horizon three; moving emphasis chooses FAST
  throughout the infinite-world grid through horizon 128. Explicit omitted-tail
  bounds cover all full finite-stage optima. This distinguishes changing the
  objective from insufficient solver computation. Fixed finite-world controls
  preserve information gain's success: once SAFE reveals all unknown bits,
  every information optimizer chooses SAFE initially. Later actions remain
  arbitrary. The special LP compression is a written argument, not new Lean.
  [Report](safe_fast/README.md).
- **Backend:** 276 of 285 endpoints converged; nine monolithic timeouts remain
  visible. All 120 available matched-objective comparisons agree within 1e-6.
  Cached cuts reduce incremental reweighting time in 53/54 comparisons, but cache
  construction is additional work and small cases can be slower.
  [Report](backend_validation/README.md).
- **GPU pilot:** small cases produced valid bounds, but larger batches were
  slower or failed the required accuracy cap. Seventy accuracy rejections among
  468 replayed witnesses are preserved; tolerance was not relaxed. The main
  study therefore used the validated CPU backend.
  [Report](gpu_audit_pilot/README.md).

## Interpretation and limits

Finite computation does not force a native objective to become information gain.
It can nevertheless lose its protections through target truncation, optimization
error, changing weights, or a finite collection deadline. The tests give tractable
positive examples and unfavorable short-budget cases, not a uniform efficiency
guarantee. None of the random-model comparisons proves unknown-model learning,
eventual sufficiency, or stronger performance on every decision problem.

On finite worlds with a full-support prior, complete information gain itself is
strictly monotone in the finitary order. With an actual feasible sufficient policy,
it also has a regret-to-eventual-capability bound. These simulations do not
establish that existence hypothesis or a unique eventual advantage for J_w.
See [the computational scope and exact Lean pointers](COMPUTATIONAL_SCOPE.md).
Collection-length-four quality comparisons, additional independent seed families,
and nested training-library expansion remain untested here; they were deferred
before comparative outcomes. Some backend timing probes use four interactions,
which do not fill that quality-study gap.

## Execution, integrity and preserved failures

The primary directory is `quality_corrected/`. The initial `quality/` execution
is preserved: the container exposes 96 CPUs but its cgroup quota is only 10.2.
All 132 planning jobs were repeated unchanged at eight workers after discovering
that limit. The original proposed seed families 926101/926102 were exposed in the
GPU timing pilot and retained as design data; confirmation uses the next unused
families 926103/926104, chosen without capability outcomes.

The corrected audit coordinator later exited with signal 143. Its 223 completed
audits were retained; all ten orphaned numerical workers completed their witness
files and passed independent validation during explicit recovery. All 67
previously unstarted jobs then ran. Thus there is no failed planning or individual
audit result in the completed corrected snapshot, **but the coordinator
interruption did occur**. Its cause is unknown. Ten original numerical process
exit/wall-time measurements are unavailable and remain null; saved worker elapsed
times are separate telemetry. Queue duration is calendar elapsed including the
interruption, not one uninterrupted monotonic timer. Historical failures,
interrupted attempts and reporting corrections are retained.

The primary summary is a frozen generated report. Its generic “no failed terminal
process” wording refers to its planning-process table, not the recovered
coordinator. Its exported per-incumbent gap table is supplemented by the static
aggregation above. [Recovery record](quality_corrected/exhaustive_audits/coordinator_recovery/RECOVERY.json)
and [corrected resource accounting](quality_corrected/RESOURCE_REPORT.json)
make these boundaries explicit.

[Independent review](INTERPRETATION_REVIEW.md) records the interpretation audit and
a JSON/CSV provenance safeguard added before supplementary execution.
[Delivery inventory](DELIVERY.json) binds the completed local snapshot, including
preserved rejected evidence. All numerical workers are finished and CPU/GPU
allocations released. This pass made no manuscript/Lean changes, commit, or push.
