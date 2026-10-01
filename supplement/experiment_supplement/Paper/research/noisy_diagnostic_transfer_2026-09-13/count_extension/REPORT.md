---
title: "What full repeat counts add to native transfer"
subtitle: "A fixed-collector follow-up to the noisy diagnostic study"
author: "WhatIsExploration research"
date: "13 September 2026"
geometry: margin=0.8in
fontsize: 11pt
colorlinks: true
---

## The question and what changed

The previous study produced guarantees for additional experiments from a small noisy diagnostic objective. Some bounds used the majority bit from a three-reading target. This follow-up asks whether the information discarded by majority voting explains a useful part of the remaining transfer gap.

We hold the collected experiments, objective functions, budgets, target interventions and objective tolerances fixed. The repeat objective already scores the **full** three-reading records. We change only how much of that diagnostic information the transfer proof uses. This is a stronger analysis of the same objectives, not a new reward or another set of trained collectors.

The [frozen extension protocol](PROTOCOL.md) specifies two diagnostic representations, three physical noise pairs, six requested targets and five design losses. The [parent study](../README.md) supplies all 984 returned collectors and its 930 complete purpose envelopes. Its sealed data and report are preserved. The mathematical results below are written proofs with finite rational certificates, not new Lean declarations.

**Full counts explain a useful part of the gap.** They improve the raw majority-based guarantee in all 126 omitted-target cases and improve the strongest previous bound in 94 of those cases. At four steps and sensor error .1, the repeat objective’s adaptive-target upper bound falls from about .093452 to .079070, with acquisition cost retained. The existing numerical lower witness is .072. Other cases show no improvement over an already stronger composition bound, and the remaining gap is not yet characterized sharply.

## Majority can preserve guessing accuracy while losing information

The environment has two fixed hidden bits and repeatable, conditionally independent noisy sensors. A count diagnostic records the number of ones in three readings of one bit. Its four possible values are 0, 1, 2 and 3. A majority diagnostic retains only whether that count is at least two.

The count preserves the entire ordered three-reading experiment. Given a count, sample uniformly among the ordered words with that count. This world-independent decoder exactly reconstructs the full record distribution. Consequently, for every acquired experiment E,

$$
\delta(E,\mathrm{count}_3)=\delta(E,\mathrm{full\ triple}).
$$

Majority is a garbling of count, so its deficiency can be smaller. It is not generally equivalent to count.

There is a precise way to see the lost capability. If a sensor has error $0<e<1/2$, its majority error is $d=3e^2-2e^3$. Both the full count and the majority bit have balanced bit-guessing accuracy $1-d$. Nevertheless,

$$
\delta(\mathrm{majority}_3,\mathrm{count}_3)
=3e^2(1-e)^2(1-2e)>0.
$$

At sensor error .1, both have balanced guessing accuracy .972, but their deficiency is .01944. Change only the subsequent decision prior to $P(U=1)=d=.028$: majority permits best accuracy .972, whereas the full count permits .99144. The full-count decision reports one only after three ones. The majority signal cannot distinguish this strong evidence from a weaker two-to-one result.

This is a decision witness for the loss, not a change to the planning prior or study design. The [proof note](theory/theory.pdf) supplies an exactly matching stochastic decoder, as well as the decision lower bound. It shows why one favorable guessing metric does not establish that a diagnostic summary preserves all later uses.

## A tractable transfer certificate for the larger diagnostic alphabet

Let $a_\theta$ and $b_\theta$ be the two diagnostic marginal laws. A putative joint diagnostic-output distribution $p$ need not have independent coordinates. Its discrepancy cost is

$$
c_\theta(p)=\tfrac12\operatorname{TV}(p_L,a_\theta)
+\tfrac12\operatorname{TV}(p_R,b_\theta).
$$

We seek a single stochastic repair decoder D and nonnegative intercept B and slope k such that

$$
\operatorname{TV}(pD,T_\theta)\le B+k\,c_\theta(p)
\quad\text{for every world and every joint law }p.
$$

The parent composition argument then gives

$$
\delta(E,T)\le B+\frac{k}{2}
[\delta(E,B_L)+\delta(E,B_R)]
$$

for every finite-signal acquired experiment, with the usual cap at one. Different requested targets may use different repair decoders. This is a universal-source upper bound, not an assertion that some budget-feasible collector attains it.

For four-valued count diagnostics, enumerating the vertices of every marginal-discrepancy cell is unnecessary. Total variation is the maximum probability difference over target events. For an event S, the robust support problem has the finite dual

$$
\sup_p\{pD(S)-k c_\theta(p)\}
=\min_{u,v,t}\{t+a_\theta\cdot u+b_\theta\cdot v\},
$$

subject to

$$
t+u_i+v_j\ge D((i,j),S),\qquad |u_i|,|v_j|\le k/4.
$$

Requiring the right side minus $T_\theta(S)$ to be at most B for every world and event gives a linear program jointly in the decoder, intercept, slope and event potentials. The quarter factor comes from the half-weighted sum of total variations, each of which is half an L1 distance. The proof uses finite convex duality; an independent implementation checks it against primal support problems.

The numerical solver proposes a certificate. We then reconstruct a rational stochastic decoder and slope, clip rational potentials to their allowed interval, raise t to its exact required maximum, and raise B to the exact largest event bound. Every saved certificate is therefore exactly feasible. Floating-point objective values and small reconstruction gaps are evidence about search accuracy, not exact optimality proofs.

We also compress target records by sufficient counts. LLL and RRR have four target summaries. LLR and LRR have six, and the adaptive target has six: retain the first observation and the number of ones in its last two readings. Within each summary, the ordered words have equal probability in every world. The uniform reverse decoder has disjoint supports, so it preserves total variation exactly. Optimizing the repair bound for the compressed target is therefore equivalent to optimizing it for the full target. Checking all compressed target events loses no full-target guarantee. This reduces computation without changing any target intervention.

## What diagnostic refinement guarantees mathematically

A majority repair can always be used on counts: first compute the majority bits, then apply that repair. Marginal total variation contracts under this garbling. Thus every feasible majority affine bound is also a feasible count affine bound, and the optimal common-repair objective at any fixed design loss cannot increase when full counts replace majority bits.

That is a statement about the optimum over all repair certificates. A finite saved portfolio contains only five design points, and numerical solvers may choose different slopes among ties. Between the design points, one cannot simply assume a particular saved count certificate beats every majority certificate. Our analysis retains the lifted majority portfolio explicitly, and gives count-specific credit only after also including any improved majority bound from the new solver.

Stronger diagnostics also need not eliminate the residual. For strictly positive diagnostic margins on product worlds $(u,v)$, with the first diagnostic depending only on u and the second only on v, a zero-error common repair would have to work for every coupling with those margins. Perturbing a positive coupling around any transportation cycle forces each repair-output matrix to be additive in its two input coordinates. Its resulting target laws must then have zero mixed world differences:

$$
T_{u,v}(S)-T_{u',v}(S)-T_{u,v'}(S)+T_{u',v'}(S)=0.
$$

The independent noisy joint LR target violates that condition whenever both sensor errors lie strictly between zero and one half. Every finite noisy repeat-count diagnostic has positive margins, so the best common-repair zero-loss residual remains positive. Compactness of the stochastic-decoder set turns impossibility of exact repair into a strictly positive minimum.

This obstruction is specifically about **one repair that must tolerate every coupling**. It does not identify the sharp largest deficiency over arbitrary source experiments, each with its own tailored decoder, and it does not identify the worst collector at H=3 or H=4. Those quantifier orders remain separate.

## Results with acquisition cost and regret retained

We evaluate both diagnostic representations at exactly the same upper bound on diagnostic loss. If S is the parent repeat-weighted loss, then

$$
\tfrac12[\delta(E,\mathrm{count}_L)+\delta(E,\mathrm{count}_R)]\le S/.2.
$$

The same expression is at most the parent six-target minimax loss. For near-optimal policies, S includes its actual finite-budget minimum plus objective regret. In particular, the repeat minimum at H=4 and noise .1 is .0072. It would be incorrect to compare zero-loss residuals alone and present them as the guarantee for those optimizers.

The 42 original horizon/noise/objective/tolerance cases yield 252 target comparisons, including 126 omitted-target comparisons. We retain the parent's numerical cost-sublevel enlargement of $5\times10^{-8}$. Its saved-policy errors are lower witnesses for that enlarged sublevel, not complete worst-error envelopes or exact zero-regret witnesses.

The paired study completed all 180 rational certificates. The same-design count search was no worse in each of the 90 comparisons, within the recorded numerical tolerance. Across the 252 fixed-collector target comparisons, 97 improve on the strongest old bound after including the new majority portfolio. Of the 126 omitted-target cases, 94 improve that baseline; all 126 improve the raw majority-repair bound. These are structured-grid counts, not independent statistical replications.

At H=4, sensor error .1, and nominal zero objective regret:

| Objective | Omitted target | Previous best upper | With counts | Saved lower witness* |
|:--|:--|--:|--:|--:|
| Repeat sum | LLR | 0.079769 | 0.078852 | 0.072000 |
| Repeat sum | LRR | 0.079769 | 0.078852 | 0.072000 |
| Repeat sum | adaptive_L | 0.093452 | 0.079070 | 0.072000 |
| Minimax | LLR | 0.079768 | 0.078852 | 0.036000 |
| Minimax | LRR | 0.079768 | 0.078852 | 0.035956 |
| Minimax | adaptive_L | 0.093452 | 0.079070 | 0.060840 |

*The lower witnesses belong to the same explicitly enlarged numerical cost sublevels as in the parent study. Bounds are rounded for display; full coefficients and values are in the CSV.

For the repeat objective and adaptive target in this table, counts close about 67% of the gap between the previous upper bound and the saved lower witness. This is a reduction in the certified interval, not a 67% improvement in a policy. At asymmetric noise (.1,.3), the corresponding upper falls from .110232 to .080990 against a saved lower witness .072, closing about 76% of that interval.

The cost terms matter. For the .1-noise adaptive target, the zero-diagnostic-loss intercept improves from .030747 to .008643. Once the actual acquisition minimum is included, the relevant upper improves only from .093452 to .079070. Advertising the smaller intercept alone would overstate the optimizer guarantee.

A useful null result also survives: at H=3 and noise (.25,.25), counts do not improve the strongest existing bound in any of the repeat objective’s 12 omitted-target comparisons, despite improving their majority-repair bounds. A composition bound already wins there. Full diagnostic information is helpful, but it is not the limiting factor in every computed guarantee.

![Fixed-collector transfer bounds at H=4 and sensor error .1. The objectives, cost sublevels and lower witnesses are unchanged. The upper comparison retains all previous bounds and the new majority portfolio before adding full-count certificates. Points are computed bounds; connecting segments are visual guides.](count_transfer.pdf)

The interpretation of this comparison is specific: better bounds from full counts concern information the objective was already asking for, but the earlier majority-based proof discarded. They do not show that the collected policies improved, nor that native objectives became universally preferable to information gain. The parent purpose-envelope tradeoffs remain unchanged.

## Verification, cost and remaining work

Both production and independent auditing passed. Production took 27.91 seconds; the full independent production audit took 17.09 seconds. The solver checked 180 certificate problems; the auditor verified all 28,800 rational event/world inequalities, exact target-compression identities, and application of the certificates to all 984 existing collectors and all six requested targets. The exact witnesses include 288,000 corner inequalities and 345,600 potential-box inequalities.

All 90 majority search values agree with the predecessor's different vertex-based formulation within $3.61\times10^{-13}$. Independent distribution-primal/event-dual controls agree to floating-point precision. The maximum production search constraint residual was $6.51\times10^{-10}$, and the largest increase needed when reconstructing an exact feasible certificate was $5.61\times10^{-10}$. Exact feasibility is established by the rational checks, not by treating those numerical residuals as zero. See [production validation](results_validation.json), [independent controls](audit_controls.json), and [independent production audit](audit_results.json), and [independent comparison audit](audit_comparison.json).

Exact target compression and an interior-point LP solver reduce the largest problem to 2,402 variables and 8,448 inequalities. An uncompressed development case took about 22 seconds; the equivalent compressed smoke case took about .32 seconds, with matching values. These implementation changes were made before the production source was frozen and did not alter the scientific grid. The protocol, production source and parent input hashes match throughout.

No parent policy optimization was rerun. The independent audit reconstructs count and target laws, verifies the exact forward and reverse count/record decoders, checks every rational event-dual inequality, compares independently assembled primal support problems, and applies the resulting certificates to the existing saved collectors. The comparison code checks all frozen cases and preserves numerical witness eligibility. A separate [comparison auditor](audit_comparison.py) independently reconstructs all 252 rows, with a largest saved-witness discrepancy of $1.65\times10^{-11}$. All scientific changes are confined to this extension; the selected manuscript and Lean support ledger were not modified.

The follow-up answers the stated question positively: the discarded confidence information accounts for a measurable part of the earlier transfer gap. It also adds a general refinement theorem and an exact obstruction showing that fully retaining each diagnostic does not by itself remove common-repair coupling uncertainty. This makes the combined noisy-diagnostic study a more substantial paper candidate than a reward ranking alone.

The remaining upper/lower gap cannot yet be assigned entirely to conservative repair: the upper is source-universal, while the lower comes from a finite saved set of budget-feasible policies. Either side may be loose. The next bounded question is to seek a sharp, independently certified worst adaptive-target error for the H=4 repeat-objective near-optimal set. This would distinguish actual freedom left by the objective from looseness in our current certificate. We should resolve one such extremum before adding more environments or claiming that the full capability comparison has been computed.

The broader methodological result is an explicit separation of four issues: what the intrinsic objective requires, what information a diagnostic summary discards, what follows uniformly despite unknown dependence between separate diagnostic decoders, and what is attainable under a collection budget. Keeping these separate prevents a tighter theorem from being misreported as a better learned policy or a universal reward ranking.

Sources and reproduction: [extension protocol](PROTOCOL.md), [proofs](theory/theory.pdf), [certificate generator](compute_counts.py), [independent auditor](audit_counts.py), [comparison CSV](comparison.csv), [comparison implementation](compare.py), and the [parent result provenance](../verification.json).
