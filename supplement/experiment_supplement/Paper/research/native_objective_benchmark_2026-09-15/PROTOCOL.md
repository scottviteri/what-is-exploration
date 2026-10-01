# Does a fixed native objective select more reusable evidence?

Frozen before outcome computation, 15 September 2026. the lead author requested a stronger
objective-selection comparison across varied environments before attempting a
learned algorithm. This study tests that hypothesis; a negative result is retained.

## Claim and scope

Test whether one fixed finite weighted native-deficiency objective gives better
downstream evidence than accurately optimized information gain, Brier gain,
predictive surprisal and first-visit reward, across several controlled interfaces.
Native minimax is a separate aggregation baseline. The world class is supplied.
The comparison is over every randomized history-dependent collector at H=3.
This is the first bounded experiment, not a population claim, a training result,
or optimization of the complete eventual J_w. H=4 is a separate prospective
extension; it must cover the same full case list before making a horizon claim.

Full-support posterior exact optima cannot be strictly Blackwell dominated within
their feasible family. Therefore success here means improved declared decision
performance/guarantees across incomparable evidence, not universal superiority.

## Environments (all four worlds, two actions, two observations)

Worlds are indexed 00, 01, 10, 11 and stay fixed. The following ten cases are
included regardless of result; all matrices will be saved before solving.

1. Independent repeatable bit sensors, errors (.1,.1), (.1,.3), and (.25,.25).
2. Delayed L access, errors (.1,.1) and (.25,.1). First consecutive L returns a
   fair coin; the second and subsequent consecutive L actions measure U. R
   measures V and resets L access. The access state starts locked.
3. Irreversible branch choice, errors (.1,.1) and (.1,.3). The first action locks
   the sensor to U or V; every later action reads the locked sensor.
4. Recurring controlled hidden-state models with three latent states initially
   at zero. Independently Dirichlet transition/emission rows, four worlds:
   (seed, concentration) = (91501,.2), (91502,1), (91503,5).

No case weights, model parameters, target weights or evaluation purposes will be
changed in response to outcomes. Random models are a generator-specific sample.
The four structural families receive equal weight in headline descriptive means.
Per-case results and comparisons within each family remain visible.

## Fixed candidate objective

Minimize sum_j w_j delta(K_pi,H,T_j), using these 16 targets:

- The two one-action words, weight .1 each.
- The four two-action words, weight .05 each.
- The eight three-action words, weight .05 each.
- A fair recorded choice of L or R, weight .05.
- A fair recorded choice of LLL or RRR, weight .05.

Every target retains its entire action-observation record. The weights sum to .9
and can be the initial terms of a positive countable native enumeration with .1
remaining mass. This does not control the finite-time/eventual gap or establish
that this particular target weighting is uniquely justified. There is no tuning.

## Baselines and selected sets

All objectives use full retained histories and the same feasible collector set.
Information gain and category-summed Brier gain use the uniform world prior,
exact posterior and undiscounted terminal gain. Surprisal sums negative log2
predictive observation probability under that same prior. First-visit reward is
one when the observed binary symbol has not previously been observed (no initial
symbol), summed over the run. These are ideal specified objectives, not learned
RND/ICM implementations. Native minimax minimizes max_j delta over the same list.

Regret fractions are 0, .01 and .05 of the full feasible objective range. Both
extrema of each linear reward are optimized. The maximum native loss is computed
over all 128 deterministic observation-contingency trees: full-history policy
mixing yields the usual world-independent conditional seed reconstruction, and
convexity of native loss makes this exhaustive for the maximum. All native
minimum and selected-set programs cover every randomized policy. Numerical
selection uses the saved feasible optimum plus eta plus 1e-8; actual residuals
and gaps are retained. Equal normalized regret is not equal training difficulty.

## Evaluation decided before outcomes

The seven nonconstant binary labels on four worlds, modulo complementation, are
the three balanced partitions and four singleton indicators. Each is evaluated
by optimal zero-one guessing under the uniform world prior. They are absent from
the reward formulas; overlap in informational content is expected, not a
statistically independent task split.

Primary: for each objective/regret/case, minimize the mean of these seven optimal
decision accuracies over all selected collectors. This is one jointly attainable
worst mean, not the mean of seven separately worst policies. Report the value
and its gap to the unconstrained optimum of that SAME mean objective. The latter
convex maximization is evaluated over all 128 pure policies. Include the uniform
random collector as a concrete reference.

Secondary: separately minimize each of the three balanced-label accuracies over
the same selected set, preserving the distinction from a joint worst mean.
Also compare every saved objective optimizer with the native optimizer in both
deficiency directions: these are selected witnesses, not all-policy envelopes.

The primary comparison is against information and Brier gain, separately at each
regret fraction. Publish every cell, wins/ties/losses (tolerance 1e-6), raw mean
differences, and family-balanced means. A broad-benefit hypothesis survives this
screen only if the native weighted objective has positive family-balanced mean
improvement against BOTH strong baselines at zero and one-percent regret, and
has no structural family's mean degradation exceeding .01 at either tolerance.
This is a declared descriptive screening rule, not a significance test. Native
minimax and weaker bonuses do not substitute for passing the strong baselines.

## Computation and verification

Use full-history sequence-form LPs with target-specific decoder allocations.
Reuse the existing noisy-diagnostic LP/certificate infrastructure without editing
its source or outputs. Save every source model, target kernel, recovered policy,
primal/dual certificate, source and protocol hash, runtime, failure and numerical
tolerance. A fresh independent audit reconstructs literal source/target laws,
checks primal/dual certificates and decision values, and compares linear-reward
optima with exhaustive pure-policy calculations. Validate native maxima and
representative native minima by fixed-source decoder LPs. A numerical certificate
is not an interval proof. Do not integrate a stronger main-paper claim unless the
actual result supports its exact scope.
