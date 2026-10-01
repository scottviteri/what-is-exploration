# Sharp adaptive-target error under the repeat objective

Frozen primary protocol, 13 September 2026, before new sharp-bound runs.

## Question

Find and certify the largest deficiency to the parent's adaptive_L target among all H=4 policies minimizing native_repeats, at equal sensor errors e_L=e_R=.1. The primary mathematical set is S(pi)<=.0072 exactly, with the optimum value itself to be proved. The previous .072 saved lower witness and .07907041 upper bound do not establish sharpness. Exact matching upper and lower certificates are the primary success criterion.

The world class, actions including WAIT, complete source records, six scored targets and weights, and adaptive_L intervention are unchanged from the parent protocol. Every behavioral randomized full-history policy is feasible. The adaptive target retains its first L observation and then reads L twice if zero or R twice otherwise; the six-valued sufficient target encoding is allowed by its already-proved exact equivalence.

## Complementary methods and claim boundaries

1. Search for lower witnesses by alternating a fixed-source deficiency dual with a policy best response under the native-loss constraint. Each policy response is an LP because the full-history likelihood factor is independent of the policy. Multiple starts and saved policies are candidate generators only; convergence does not certify a global maximum.
2. Prove the objective minimum using bounded-decision lower bounds and an exact Bellman calculation for the sum of balanced U and V guessing values. The candidate values are .972 for each triple diagnostic, 1.872 for the best four-step sum, and hence .0072 for the weighted loss minimum. Any pruning of policy actions must use exact Bellman equalities, not floating reduced-cost zeros.
3. Seek a common target decoder that works for every policy in a proved superset of the native-optimal set. The first candidate superset is the exact Bellman-optimal action family for the combined guessing purpose. For each world and target event, maximize decoder error over this family by exact dynamic programming. One successful uniform decoder gives a valid upper bound without any minimax exchange. It need not achieve the true worst policy-specific deficiency.
4. If that relaxation is too loose, retain the actual native-loss LP constraints in a policy-separation/robust-decoder program, or derive a more targeted analytic upper bound. Maximizing an upper-bound deficiency epigraph is not a valid substitute. Any unresolved numerical gap is reported explicitly.

For rational certificates, reconstruct stochastic policy/decoder matrices, evaluate exact world laws and target laws, and verify lower decision witnesses and upper inequalities independently. Floating LP search and exact-feasible certificate checks are distinct. A numerical upper/lower gap is not called an exact theorem.

## Secondary tolerance controls

After the primary mathematical extremum is resolved or its remaining obstruction is identified, retain the original numerical outer threshold .00720005 as a separate control. Further bounded controls may use the parent's 1% and 5% full-range gaps (.003432 and .01716) and its absolute gap .005, retaining any numerical enlargement explicitly. These are secondary quantitative extensions, not requirements to claim a complete sharp envelope at every tolerance. A proved regret-dependent uniform decoder bound is useful even when it is not sharp.

Any other noise pair is an explicitly labeled exploratory/generalization control, not a silently expanded primary grid. The main conclusion must distinguish actual freedom of native-optimal policies from a conservative shared-decoder bound.

## Artifacts and verification

Write new search, exact witnesses, certificates, proof note and report under sharp_adaptive/. Preserve all sealed parent and count-extension artifacts. Independently reconstruct the fixed-policy lower witness, Bellman calculations and final all-policy upper certificate. Save source/input hashes and attempted relaxations, including failed candidates. No main-paper or Lean support claim is changed by a successful numerical run alone.
