# Target weights, Blackwell monotonicity, and ranking sensitivity

15 September 2026. Follow-up to the lead author's questions about dependence on weights
and weights monotone in the experiment order. [Analysis protocol](PLAN.md),
[code](compute.py), [numerical results](results.json).

## What is independent of the weights?

For a finite target library, write d_j(E)=delta(E,T_j) and
L_w(E)=sum_j w_j d_j(E). If E Blackwell-dominates F, composing its decoder
to F with a decoder from F to T_j gives d_j(E)<=d_j(F). Therefore EVERY
nonnegative weighting makes L_w(E)<=L_w(F). The finite library can still tie
strict source improvements that its targets do not expose.

The rich eventual profile has the stronger representation in the paper:
every positive summable normalized weighting is strictly monotone in the
finitary process order. If zero lies in the closure of feasible profiles,
each such fixed weighting is calibrated. The quantitative implication
ell_j <= (1-J_w)/w_j depends on the weights. None of these statements
identifies a unique preference between incomparable profiles or guarantees
the best finite-budget average decision value.

Sources: [paper objective and assumptions](../../../../draft/exploration_decision.tex),
[full reader](../../../../draft/exploration_long.tex), and
[scalarization proof](../../../../draft/capability_selection_theory.tex).
The new weight analysis below is written algebra and numerical evidence,
not additional Lean coverage or a change to those claims.

## How rankings depend on the weights

For two fixed records define g_j=d_j(E)-d_j(F). Their loss difference is

    L_w(E)-L_w(F) = sum_j w_j g_j.

If every g_j<=0, every nonnegative weighting favors E or ties. If g has both
positive and negative entries, unrestricted strictly positive normalized weights
can favor either record: concentrate most mass on one positive or negative
coordinate while retaining small positive mass elsewhere.

For normalized weights w,v, a useful continuity bound is

    |L_w(E)-L_v(E)| <= ||w-v||_1 / 2,
    |sum_j (w_j-v_j)g_j|
        <= (max_j g_j-min_j g_j) ||w-v||_1 / 2.

Indeed w-v sums to zero, so its positive and negative parts each have mass
||w-v||_1/2. The score varies continuously; which policy minimizes it can
switch at a tie. Large feasible ranking ranges do not establish that arbitrarily
small weight changes cause a reversal.

## What increasing target weights mean

Interpret the proposal as

    T_i Blackwell-dominates T_j  =>  w_i >= w_j.

Equivalent targets then have equal weights. This is a constraint on target
priorities, distinct from monotonicity in the acquired source, which already
holds. The harder target already has at least as large a deficiency for every
source, since target garbling contracts TV. More weight adds another priority.

The original benchmark does not satisfy the proposed increasing-weight rule:
L has weight .1 and LL has weight .05, even though LL retains its first L
reading and therefore dominates L.

### Exact native example: increasing weights still reverse the chosen policy

Take four worlds (U,V), noiseless repeatable actions reading U or V, and a
one-action collection budget. Targets are a U reading, a V reading, and the
two-action joint U,V experiment. The joint target dominates both singles;
the singles are incomparable.

| Collected record | Error to U | Error to V | Error to joint U,V |
|---|---:|---:|---:|
| Read U | 0 | 1/2 | 1/2 |
| Read V | 1/2 | 0 | 1/2 |

Both weight choices below are strictly positive and put more weight on the
strictly more informative joint experiment:

| Weights (U,V,joint) | Loss after reading U | Loss after reading V |
|---|---:|---:|
| (.3,.1,.6) | .35 | .45 |
| (.1,.3,.6) | .45 | .35 |

This also describes optimization over all randomized collectors. If the
recorded initial choice reads U with probability alpha, its errors are
((1-alpha)/2,alpha/2,1/2). For the singles, guessing the missing bit fairly
attains the bound, and the two-world TV bound gives the matching lower bound.
For the joint target, fair missing-bit reconstruction gives error 1/2 in
every world. Under a uniform prior the posterior has two equally likely
worlds after every acquired signal, so even the best world guess succeeds
only half the time, proving the matching uniform lower bound. The weighted
loss is affine in alpha. The first weights uniquely select alpha=1; the
second uniquely select alpha=0. Monotonicity does not choose between U and V.

## Actual benchmark: constrained reweighting of the saved records

For EACH case we held its saved native-weighted and Brier objective-optimum
records fixed, evaluated all 16 deficiencies, and computed the complete
16-by-16 target-deficiency matrix. We then minimized and maximized

    Delta(w) = L_w(saved native record) - L_w(saved Brier record)

subject to sum(w)=1, every w_j>=.01/16, and all increasing-target-weight
constraints. The floor reserves one percent of total weight as a uniform
component. Positive Delta favors Brier; negative favors native. These are
simulation-loss differences, NOT changes in downstream guessing accuracy.

The following ranges cover broad admissible weight changes; they are not local
perturbation estimates. Extremizing weights may differ between environments.
No collector has been reoptimized and no single new weighting rule has been
tested across cases. The original benchmark's seven-task results are unchanged.

| Case | Minimum loss difference | Maximum loss difference |
|---|---:|---:|
| Sensors (.1,.1) | -0.031400 | +0.031361 |
| Sensors (.1,.3) | -0.045890 | +0.063305 |
| Sensors (.25,.25) | -0.038069 | +0.038031 |
| Delayed (.1,.1) | +0.000000 | +0.000000 |
| Delayed (.25,.1) | +0.000000 | +0.000000 |
| Irreversible (.1,.1) | -0.234048 | +0.233233 |
| Irreversible (.1,.3) | -0.042939 | +0.071230 |
| Hidden-state seed 91501 | -0.057220 | +0.020786 |
| Hidden-state seed 91502 | -0.069641 | +0.039579 |
| Hidden-state seed 91503 | -0.061546 | +0.064994 |

In all eight non-equivalent saved record pairs, both rankings occur under the
constraint. The two delayed pairs are tied to numerical tolerance. The original
weights, normalized to sum one, give native no larger loss on these saved pairs,
as expected from its original optimization; that fact does not establish
weight-independent superiority.

### Numerical verification

The study checks 2,560 target-to-target deficiencies, 320 record-to-target
deficiencies, and 20 weight LPs. Target matrices are independently reconstructed
from literal world laws. Decoder feasibility/duality, weight constraints, and
weight-LP primal/dual certificates are checked. The inferred target relation is
unchanged for zero thresholds 1e-9, 1e-8 and 1e-7 and is checked for transitivity.
The run passed 3,300 numerical checks with maximum residual below 3.27e-11.
This is float64 evidence, not an interval or exact proof of the target order.

## Infinite target lists: a summability obstruction

Suppose the library contains infinitely many distinct entries

    T_1 <=_B T_2 <=_B T_3 <=_B ...

and all weights are positive. Increasing target weights imply
w(T_n)>=w(T_1)>0 for every n. Their sum therefore diverges. This contradicts
the positive summable weights required by the paper's J_w construction.

Native extensions supply such chains: longer records retain shorter prefixes.
Quotienting out equivalent experiments does not generally remove the issue.
For a noisy bit sensor with error q in (0,1/2), n readings are strictly less
informative than n+1 readings. To see strictness, put r=(1-q)/q>1. All
likelihood ratios for n readings lie between r^(-n) and r^n; a garbled output's
likelihood ratio is a convex combination of source likelihood ratios. But the
all-one output of n+1 readings has ratio r^(n+1), so it cannot be generated
from n readings. Projection gives the forward dominance.

Thus increasing positive ATOM MASSES are possible on our finite 16-target
library, but cannot be imposed along this full infinite chain. A monotone
priority factor multiplied by a decaying base measure is possible in suitable
constructions; the resulting atom masses need not themselves be monotone, and
the base measure remains an additional choice. Interpreting monotonicity in
the opposite, decreasing direction changes this obstruction, but still leaves
preferences between incomparable targets undetermined.

## Implication for comparison

A useful benchmark can report a target profile and a range over a declared
class of weights. A claim holding for every admissible weighting is stronger
than a claim for one chosen weighting. On a finite library, the two weight LPs
above directly check this robust ranking for fixed records. Comparing complete
objective-selected policy families, or the effect of reoptimizing with new
weights, is a separate optimization problem.
