# Prospective supplied-model finite-budget comparison

Frozen before any confirmation-model objective comparisons on 23 September2026.
This is a bounded execution of the earlier proposed adaptive-weight protocol, not
an assertion that its entire optional grid has been run. The CPU/GPU feasibility
pilot and archived design classes determine resources before confirmation outcomes.

## Queue and common information

Twelve independent model classes: four/eight worlds, three hidden physical states,
binary actions/observations, Dirichlet concentrations0.2/1/5, seeds926103/926104.
Metadata-only repository search found no previous use of these seeds. Both926101
and926102 are excluded because the parent's pilot assignment exposed them. The
replacement is the next unused integer seeds; no capability outcome selected it.
Worlds have a uniform prior for information/Brier. Initial physical state is0.
Every method receives the same exact finite model arrays and full history policy
space. This is numerical supplied-model optimization, not learned exploration.

Collection length is3. All32768 deterministic depth4 interventions form the held-out
worst-native-deficiency metric, evaluated independently after planning. The pilot
put length4 audits at32–100 serial minutes each, so length4 quality comparisons
are deferred for *all* methods before outcomes; backend tests include length4.
Training uses all128 deterministic depth3 trees and the independent uniform-action
policies of depths1/2/3, encoded as literal rational full-history interventions.
This common fixed131-target library isolates weight adaptation from target discovery.
Expansion/library-size experiments are in the separate matched backend study.

## Planning and checkpoints

Native arms: fixed uniform target emphasis; inverse cumulative decoder-cost
emphasis; multiplicative hard-target emphasis; direct maximum deficiency on this
same library. The first three use epsilon=1/20 of the frozen positive rich
background, with exact selected encoding masses and explicit omitted tail. There
is no renormalization of the background truncation. The tail may be large; a small
selected LP gap is never reported as small full-objective regret. Minimax is a
finite-library benchmark, not J_w or a positive rich weighted objective.

All arms retain globally valid target dual cuts, reset aggregate lower bounds
when weights change, and record actual policies and original-probability decoder
witnesses. At each round: solve current master, audit all selected targets, add
cuts. Adaptive arms change weights after each completed round. Hard-target eta=1;
weights are computed using float exp and normalized as exact represented fractions.
No certified multiplicative-weights convergence claim is made. Tractability uses
reference uniform weights divided by1+cumulative target decoder seconds/scale,
where scale is the median first-round target cost. All master/decoder/update/cache
work is charged. One common target-order seed926201 is primary. No seed is chosen
by outcomes; timing replication belongs to the backend study. Additional order
seeds and epsilon/library sweeps remain explicitly deferred.

Checkpoints2/10/40 seconds include model geometry, target construction and planning
work from already supplied model arrays; Python interpreter import and certificate
serialization are reported separately. Evidence arriving after a checkpoint is not
backdated. Fixed/minimax arms use the best training-objective feasible incumbent;
adaptive primary is the most recent fully audited iterate. Their realization-weight
average is a secondary endpoint when its decoder check also finishes in budget.
Conditional policy rows are never averaged. Checkpoints lacking an audited policy
are missing, not assigned a favorable score. Hard external process caps preserve
failures; no tolerance is relaxed to rescue a method.

Baselines: uniform actions; exact full-history dynamic programming for expected
information gain I(world;record) and posterior categorical Brier improvement.
For each reward, add training-minimax selection subject to reward at least its
optimum minus0%,1%,5% of its attainable reward range. The zero face has an explicit
1e-10 numerical slack. Selection uses training targets only, never held-out audits.
Face solves get the same40-second planning cap, including reward range calculation.
These favorable controls preserve genuine baseline successes and distinguish a
returned representative from the complete optimizer face. Numerical face examples
are not claims about all exact optimizers.

## Evidence and decisions

Every accepted master lower bound, policy law, dual cut and decoder upper is
independently replayed. Tolerance2e-7, selected convergence gap1e-6. A complete
held-out audit requires all32768 targets, each with a checked bracket and saved
witness. A timed-out audit reports its attained lower witness and a valid
full-revelation upper; it is not an exhaustive audit. Per-audit hard cap1800seconds.
All failures, late endpoints and numerical rejections remain recorded. Deduplicate
identical policy arrays only for the independent audit, never to discount planning
cost. Report per-class paired results, coverage, CPU timings and uncertainty bands;
model classes, not computational iterations or target count, are the independent
replicates. No significance/superiority or eventual-exploration claim is prespecified.

The controlled SAFE/FAST study tests asymptotic mechanisms; this study tests finite
performance only. Neither can establish efficient optimization of the full J_w.
