# Selecting native targets under finite computation — 23 September 2026

the lead author authorized a large experiment and research run after discussing prefix-order
selection, adaptive hardest-target generation, and target-count sensitivity. The
uncertainty is whether targeted selection makes a finite native objective useful
and computationally practical across environments, and which conclusions survive
more targets, longer collection, longer audits, and favorable baseline selection.
No result is required to favor the native methods.

## Fixed scientific meaning

For each supplied finite class of unknown controlled hidden-state models, the
actual world is unknown to collectors, targets and decoders. Every method receives
the same class, binary action/observation interface and uniform world prior. All
policies may adapt to the full retained history. A singleton class is used only
as a zero-deficiency implementation check.

The primary audit is

    A_(t,n)(pi) = max_sigma min_G max_Q TV(K_(pi,t)(Q) G, K_(sigma,n)(Q)).

Collection length t and target length n are separate. G is randomized,
world-independent and target-specific. All 128 deterministic trees at n=3 or
32,768 at n=4 are evaluated for a complete audit; mixtures cannot exceed their
maximum. A partial sweep supplies a lower witness only; its global upper bound
must come from a valid complete comparison, such as full revelation. No n=5
exhaustive audit is proposed (2,147,483,648 deterministic trees).

The weighted arm optimizes the average deficiency over a finite selected library.
Its declared finite reference is the uniform average over all deterministic
n=3 targets. At each K the selected average uses weights 1/K. Random libraries
are nested permutations without replacement; structured libraries begin with
all fixed action sequences and then use a random permutation of the other trees.
This reference does not represent the paper's full randomized-target profile or
its infinite-rich eventual J_w. Changing K changes the finite approximation;
weighted-score findings are not renamed minimax findings. The original 16-target
weighted and minimax objectives remain separate benchmark anchors.

The minimax arm minimizes the maximum selected-target deficiency. It compares:
random libraries; structured libraries; and adaptive generation starting from the
fixed action sequences and adding omitted targets with largest current error.
Prefix and recorded-mixture pruning justify the initial structured set for the
old minimax library. They do not justify removing terms from its weighted score.
No outcome-based environment selection, reward changes or target weighting.

## Curves and evaluation

The prospective target-count grid is 8,16,32,64,128 for n=3 and 16,32,64,128 for
n=4. Every accepted checkpoint saves its selected targets, objective/dual bounds,
recovered policy, complete current-depth audit, timings and numerical checks.
Adaptive minimax can stop earlier only when a full-audit upper bound minus a
restricted-master lower bound is at most 2e-7. The library bound applies to the
same collector set, including any declared reward constraint. Failure to close
is not certification. Keep every intermediate checkpoint and failure.

Full evaluation does not influence the random/structured target order or the
weighted optimization. For timing, charge master construction/solve/replay and
selection to every method; charge the adaptive method's complete separation
sweep to its training cost. Ordinary offline audits are reported separately.
Also report end-to-end elapsed time including common validation. Selection seeds
are repeated computation on the same case, not independent environments.

Final n=3 collectors receive an n=4 evaluation that is never used for selection,
weights, stopping or hyperparameters. An n=4-trained arm provides a separate
same-loss optimization reference. A full minimax optimum winning its identical
evaluation metric is expected by construction. Compare target selection, time to
certification, held-out target depth and matched acquisition budgets instead.

## Baselines and exact-selection controls

Include finite full-world information gain and posterior Brier gain, exact Bayesian
next-raw-observation surprisal and categorical squared loss, categorical
pseudo-count, empirical observation-label entropy, posterior predictive-coordinate
variance, observation-occupancy entropy, and uniform actions. Include the two old
finite native objectives as anchors. ICM, RND and standalone first visits are not
new campaign methods; their historical results remain untouched. No unimplemented
MOP, empowerment, DIAYN or compression objective is silently substituted.

All baseline returns stop at t. Observation squared loss differs from posterior
Brier gain. The checked complete Bayesian alarm theorem is about a different
countable class and infinite totals; this campaign does not optimize those totals.
The 21-condition startup pilot and its full 25-condition archive remain separate.

For information and Brier, additionally minimize the full target audit over
collectors within 0,1%,5% of the objective's attainable return range below optimum.
The zero row allows at most 1e-10 numerical reward slack, explicitly reported.
These are favorable near-optimal controls, not worst-over-optima envelopes and
not sampled-policy training. Report the actual recovered reward regret.

## Model coverage and feasibility gates

Use all ten prior structural/recurring cases and new prespecified random classes:
4 or 8 candidate worlds, three hidden states, Dirichlet concentrations .2,1,5,
and seeds fixed in the launch manifest before outcomes. Repeated model classes
at different horizons remain paired. Main collection lengths are t=3,4; extend
t=5 and pilot t=6 under measured memory/solver limits. Only timing, memory and
certificate validity may determine which computational tiers are launched.
Preserve all pilot failures and omitted-tier accounting. Retain the September 15
failed broad-benefit screen and all prior baseline successes.

First validate literal target laws, prefix/mixture reduction, native master
certificates, DP baselines, near-optimal constraints, and CPU/GPU parity on small
cases. Use measured representative pilots to freeze a concrete interleaved queue.
No expensive worker starts before its protocol, source hashes and job are frozen.

## Resources and evidence

An isolated directory and copied solvers preserve old studies and shared paper/
Lean edits. Container quota: 10.2 CPU equivalents and about 28.9 GiB memory;
RTX 4090 with 24 GiB VRAM. Bound the main queue to eight hours, at most four
one-core workers, one serialized GPU process, at most 5 GiB worker RSS, a 12 GiB
output cap and 15 GiB free-disk reserve. Individual solves and cells have explicit
caps. Enforce STOP, process-group termination, source refusal and atomic outputs.
Source snapshots, actual models, target IDs, policies, LP vectors/certificates,
per-target bounds and partial checkpoints permit review. Use original input
probabilities for witness checks; never relax numerical tolerances after failure.

Repaired floating-point certificates are not exact arithmetic or Lean proofs.
No main manuscript, shared support/navigation ledger, commit, push or Overleaf
export is part of this campaign. A launch is not a completion claim. Final reports
must include failures, missing checkpoints, coverage and selection bias from
resource limits, as well as objective rankings.

## Launch limits selected from the eight pilots

The main n=3 curves use K=8,16,32,64,128 at collection length three and
K=8,16,32,64 at length four. The four-step weighted pilot solved K=64 but
exhausted the shared 300-second GPU/CPU budget at K=128. That failure and its
four accepted checkpoints remain in `pilot_results/cell_0002`; no tolerance or
scientific criterion was changed. The five-step extension uses K=8,16, keeping
its master size near the successful four-step K=64 tier as each extra binary
action/observation step multiplies source histories by four. The six-step
extension keeps the original 16-target anchors and nine baselines on four
prespecified cases. A successful six-step pilot licenses this bounded trial,
not a promise that all models will solve. Three-step n=4 adaptive training still
uses K=16,32,64,128, with exhaustive 32,768-target separation at each accepted
checkpoint. The main manifest records every launched tier and job.

The primary interleaved grid is 1,188 jobs over 22 model classes. The extensions
add 16 n=4-trained comparisons, 120 five-step jobs and 44 six-step jobs, for
1,368 registered jobs. The eight-hour cap may leave jobs pending or incomplete;
report that coverage rather than extending the time budget silently. A separate,
bounded decomposition study investigates whether dual cuts can replace the
large monolithic LPs. Its source, protocols, failures and timings are retained
under `decomposition_research/`; it does not change this frozen queue.
