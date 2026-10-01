# What these computations can resolve

The theoretical distinction is between the objective and its implementation.
Strict monotonicity says that the complete native objective strictly ranks a
strict improvement in the stated native process order. It does not supply a
uniform running-time bound, a way to find an unknown successful policy, or a
robust margin separating every pair of policies.

A finite implementation can introduce several separate errors: incomplete target
coverage, numerical objective-evaluation error, incomplete policy optimization,
and a limited collection horizon. Moving the target weights as the horizon grows
can also change the objective being optimized. These are not interchangeable.
An exact optimizer of a changing objective can fail even when computation is
cheap; a fixed objective can work on a tractable interface with finite computation.

The SAFE/FAST study holds this distinction visible. Here the full finite-stage
loss means `L_H(pi) = sum_j w_j * delta(K_(pi,H), T_j)`, with collection time H
fixed; it is not the eventual score. Its fixed-emphasis and moving-emphasis
problems admit a special finite linear-program reduction. Their retained
problems are solved with independently replayed rational bounds; omitted rich
background mass gives explicit outer bounds for all full-objective optima. The
finite-world information-gain controls retain every optimal tie and eventually
select SAFE. Thus this experiment does not show a universal disadvantage for
information gain, nor an efficient optimizer for arbitrary native objectives.

The backend study checks a different issue: whether reusing target-specific
constraints solves the same finite optimization problem more cheaply. A cached
constraint remains useful when weights change, but an old aggregate lower bound
cannot be reused as a certificate for the new weighted objective. The study
checks both original witnesses and fresh aggregate bounds. Its timing results
are measurements of the specified implementations and configurations.

The random-model quality study is supplied-model planning at collection length
three. Its positive-background native objectives are *truncated* for computation.
The omitted mass is about 0.04895. Consequently a selected-objective gap of 1e-6
is not a full-objective regret certificate of 1e-6: the conservative full finite
regret bound also charges that tail. This study does not send both optimization
and truncation error to zero, does not increase collection time indefinitely,
and does not test the hypotheses of an asymptotic theorem by finite simulation.
Its separate depth-four native audit measures held-out capability, not the
training reward. These are finite hypothesis classes with a uniform prior; a
numerical win on one risk is not a strict process-order comparison. Direct
minimax on the training library is a separate benchmark.

On precisely this finite-world/full-support-prior side of the theory, complete
information gain is itself strictly monotone in the finitary order. Strictness
needs neither attainable full revelation nor an existing sufficient policy;
see `causalInformationObjective_lt_of_strict_finitaryDominates` in
[QuantitativeStrictness.lean](../../../Formal/Formal/QuantitativeStrictness.lean)
and support entry `prop:finite-world-strict-finitary`. If the feasible family
contains a natively sufficient policy, its complete-information regret also
bounds every eventual native error: in nats,
`ell_T <= min(1, sqrt(g_I / (2a)))`, where `a` is the smallest prior atom.
The actual feasible sufficient member is a hypothesis of
`causalBehavior_posterior_regret_bounds` in
[PosteriorCalibrationCorollary.lean](../../../Formal/Formal/PosteriorCalibrationCorollary.lean),
registered under `cor:finite-world-posterior-calibration`. This numerical study
does not establish that hypothesis, optimize the complete information return,
or supply a common acquisition deadline. Its finite-budget wins cannot establish
a unique eventual-consistency advantage for the native objective.

No experiment here establishes that every finite-compute implementation of J_w
has the same behavior as information gain. Nor can these experiments rule out
poor practical behavior: budgets may leave native optimization unfinished, and
a well-solved weighted objective may trade off the separately measured worst
native deficiency. Returned policies, numerical optimization gaps, all-optimum
claims, and the stronger Lean theorems therefore remain separate in the reports.

The quantitative distinction is useful. Write the full weighted loss as
`L = sum_j w_j * delta_j`, with nonnegative losses at most one and positive
summable weights. A certificate `L <= a` gives
`delta_j <= min(1, a / w_j)` for each protected target. If only regret is at most
`eta`, then `a = inf L + eta`; regret alone is not an absolute capability bound
when the optimum loss is nonzero. For a retained finite sum, the candidate upper
bound must also charge the omitted mass. Positivity by itself supplies no useful
finite error margin for a very small target weight.

This is the elementary specialization of the existing
[finite certificate lemmas](../../../Formal/Formal/AdaptiveNativeCertificates.lean),
not a new computational guarantee. The selected-target solver gap, the omitted
weight, the optimum's nonzero loss and the target's own weight play different
roles. A theorem requiring vanishing full regret and increasing collection time
does not say that a fixed positive optimization tolerance, fixed target library
or fixed interaction horizon is enough. It also does not assemble a sequence of
separately planned collectors into one online policy.

A fixed collection deadline can also favor an informative record already acquired
over a better record that would arrive later. Strict monotonicity of the eventual
score does not make a finite-prefix optimization immune to that horizon issue.
The SAFE/FAST horizon grid distinguishes this from the time needed to solve each
finite problem. The positive limit theorem requires increasing collection times
and its stated error conditions; it supplies neither a uniform finite horizon
for every environment nor a single online policy. Numerical advantages over
information gain in the random-model audit do not remove that shared limitation.
