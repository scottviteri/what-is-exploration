---
title: "What the exact repeat-objective optimizers guarantee"
subtitle: "A policy-restricted adaptive-target envelope at four readings"
author: "WhatIsExploration research"
date: "13 September 2026"
geometry: margin=0.8in
fontsize: 11pt
colorlinks: true
---

## Question and scope

The noisy-diagnostic studies compare intrinsic objectives by the native experiments their optimization makes simulable. The preceding full-count follow-up left a concrete gap: at four collection steps and sensor error .1, a saved repeat-objective collector had adaptive-target error .072, while the general transfer guarantee was approximately .0790704. Was the remaining interval actual freedom among optimal policies, or looseness in the proof?

This study retains the world class, observation mechanism, collection budget, full histories, diagnostics and weights. It restricts the upper-bound calculation to policies optimizing the actual diagnostic objective. The primary set uses **exact zero regret**. The predecessor's nominal-zero-regret numerical set allowed an extra $5\times10^{-8}$ of loss; that slightly larger set is a separate question. The new guarantee must not silently replace its bound.

The current certified result is

$$
0.072\ \le\ \max_{\pi:S(\pi)=S^*}
\delta(E^\pi_4,T_{\rm adaptive})\ \le\ 0.072000001123,
\qquad S^*=0.0072.
$$

The lower endpoint and the objective minimum are exact. The upper endpoint is an outward-rounded rational bound valid for every randomized history-dependent optimizer, including policies absent from our saved collectors. The interval has width $1.123\times10^{-9}$. It is not an exact equality theorem: a common decoder supplies the upper bound, and a policy-specific decoder may do better.

These are written mathematical results supported by independent finite rational certificates. They are not new Lean declarations, an eventual native-sufficiency theorem, or an experiment about training dynamics.

## The experiment and the objective

A world is a pair of fixed hidden bits $(U,V)\in\{0,1\}^2$. Reading L or R observes the respective bit through a binary-symmetric sensor with error $e=.1$. Sensor noise is conditionally independent across readings. WAIT returns zero. A collection policy chooses actions for four steps and retains its complete action--observation history.

For a finite native target T, its deficiency from the collected experiment is

$$
d_T(\pi)=\delta(E^\pi_4,T)
=\min_G\max_\theta\operatorname{TV}(E^\pi_{4,\theta} G,T_\theta).
$$

The stochastic decoder G is independent of the world; it can depend on the policy and requested target. Total variation is half the L1 distance. It measures the worst-world error of replacing the requested experiment by a decoded collected record.

The loss minimized by the repeat objective is

$$
S=.2d_L+.2d_R+.1d_{\rm tagged}+.1d_{LR}
  +.1d_{LLL}+.1d_{RRR}.
$$

The tagged target chooses L or R fairly and retains that choice. LLL and RRR retain their full three-reading records, not just a majority vote. The unscored adaptive target reads L first, then reads L twice if its first observation is zero and R twice if it is one. The target is a separate hypothetical intervention; the decoder simulates its distribution rather than executing its actions in the already-used environment instance.

## An exact acquisition theorem

The minimum and its equality conditions can be proved for every equal sensor error $0<e<1/2$, with the same four-step budget and weights. Write

$$
q=1-e,\qquad A=1-3e^2+2e^3,\qquad
\Delta=A-q=e(1-e)(1-2e).
$$

Here q is the accuracy of balanced bit guessing from one reading, and A is its accuracy from three readings. Let $V_U$ and $V_V$ be optimal guessing probabilities from the collected record under the uniform four-world prior. A finite exact Bellman calculation proves

$$
\max_\pi(V_U+V_V)=q+A.
$$

Decision-value lower bounds on deficiency give $d_{LLL}\ge A-V_U$ and $d_{RRR}\ge A-V_V$. The other scored deficiencies are nonnegative, so

$$
S\ge .1(2A-V_U-V_V)\ge .1\Delta.
$$

Reading one side three times and the other once attains equality. Thus **$S^*=.1\Delta$**, equal to $9/1250=.0072$ at error .1. This does not assume that a numerical solver found the true objective minimum.

Equality also characterizes every optimizer's six scored coordinates:

$$
(d_L,d_R,d_{\rm tagged},d_{LR},d_{LLL},d_{RRR})
=(0,0,0,0,t,\Delta-t),\qquad 0\le t\le\Delta.
$$

Every point on this segment is attainable by a recorded mixture of the fixed schedules LRRR and LLLR. Recording the schedule label does not require expanding the experiment: its conditional law given the complete action--observation history can be regenerated independently of the world.

This is the exact set of **six scored coordinates**, not a characterization of the policies' complete native-deficiency profiles. It leaves the omitted adaptive coordinate undetermined. That is why computing its envelope adds information beyond identifying the argmin of the intrinsic objective.

An optimal scored profile does not identify a canonical experiment. Choose a side fairly; read it, the other side, and the chosen side again; read the chosen side once more only if its two readings disagree, otherwise read the other side. At error .1 this policy has both repeat deficiencies .036 and exact loss .0072. Yet neither signed bit count ever exceeds two, so its output likelihood ratios for either bit are at most $9^2$. Every recorded mixture of LRRR and LLLR retains an output with likelihood ratio $9^3$ for at least one bit. Thus this optimizer cannot simulate any such endpoint mixture exactly. The proof note supplies an explicit repeat decoder. The scored segment describes six losses, not a Blackwell normal form for its policies.

## An exact omitted-target lower witness

The fixed schedule RRRL is a repeat-objective optimizer. It simulates L, R, tagged, LR and RRR exactly, and has LLL deficiency $\Delta=.072$.

Its adaptive-target deficiency is also exactly .072. For an upper decoder, the one L reading can be converted into a synthetic L triple with deficiency $\Delta$, independently retaining the three R readings. Use the first synthetic L bit to choose the target branch: either return the synthetic L triple or its first bit followed by two retained R readings. Contraction under this stochastic transformation preserves the $\Delta$ error bound.

For a matching decision lower bound, fix V=1 and use prior $P(U=0)=.1$. The best source guessing accuracy for U is .9. On the adaptive target, guess zero precisely after the output 000; the resulting accuracy is .972. The gain .072 is a bounded-decision witness for deficiency. Both the decoder and decision calculation have independent rational audits.

Thus optimizing the finite diagnostic objective leaves a real adaptive-target error even at exact zero objective regret. A small intrinsic score gap is not the same quantity as target simulation error.

## Why the broader prediction-optimal family is insufficient

Native optimality implies that $V_U+V_V$ is maximal. The converse fails, even if the four cheaper diagnostics are exactly simulable.

Consider the deterministic policy that reads L first, then completes RRR after observing zero, or completes LLR after observing one. It achieves the same optimal balanced guessing sum, but its two repeat deficiencies are

$$
d_{LLL}=\Delta,\qquad d_{RRR}=q\Delta.
$$

At error .1 its native loss is .01368, strictly above .0072. Its adaptive-target deficiency is at least .1224, by an exact three-action decision witness. Consequently a guarantee proved only from optimal balanced bit prediction cannot yield the desired .072 adaptive bound. The [proof note](theory/theory.pdf) gives the general lower witness $(2-3e)\Delta$ and its explicit prior and payoffs.

We retained this failed relaxation rather than silently discarding it. Exhaustive enumeration of the larger family's 6,728 deterministic contingent plans produces 1,295 distinct experiments after merging proportional likelihood columns. A separate common full-history decoder for that larger family has certified error approximately .1231912. Neither calculation is the desired native-optimal maximum. In particular, a native-optimal randomized policy need not mix only native-optimal deterministic policies: mixing can reduce the convex deficiency loss below the average component loss.

## A finite all-policy upper certificate

The useful restriction is the actual native-optimal set. A policy realization plan assigns world-independent action-prefix weights w. Its terminal experiment has columns

$$
E_\theta(h)=p_\theta(h)w(h),
$$

where $p_\theta(h)$ is the controlled likelihood before multiplying by the policy. Flow constraints encode all behavioral policies. For every diagnostic, joint policy/decoder allocations make its deficiency sublevel linear. The exact Bellman equality removes only actions with strictly positive exact prediction-value regret; the diagnostic constraints remain.

The noisy-bit likelihood columns are proportional whenever their signed L and R observation counts agree. On the necessary Bellman face there are 208 reachable terminal histories and 28 such likelihood rays. For each fixed policy, collecting their weights preserves the experiment exactly. The reverse count-to-history decoder depends on the policy, but is independent of the world. The resulting native feasibility LP has 857 variables, 514 equalities and 73 inequalities. On this face it suffices to impose exact simulation of LR and a sum of repeat deficiencies at most .072; LR itself garbles to L, R and tagged.

We seek one stochastic decoder D from these 28 states to the adaptive target. For each world and each target event B, a linear native-policy oracle maximizes

$$
(E_\theta D)(B)-T_\theta(B)
$$

over the actual optimizer set. A bound on every such event gives a TV bound for every optimizer. We subsequently allow the adaptive decoder to use the full 208-history source alphabet while retaining exactly the same compressed diagnostic constraints. A cutting-plane master proposes D; separation finds policies exposing any violated event constraint. This is an upper-bound method. It does **not** exchange the maximum over policies with the minimum over their individual decoders.

The final count-state certificate uses six sufficient adaptive summaries. Equal noise also permits five likelihood-ray summaries: group the full target words as $\{000\}$, $\{001,010\}$, $\{011,101,110\}$, $\{100\}$ and $\{111\}$. Uniformly splitting each group recovers the full target exactly and preserves total variation. The full-history follow-up search uses this smaller exact representation; the amendment changes neither the intervention nor its information.

Floating-point optimization only proposes certificates. We reconstruct a rational stochastic decoder. For each world/event, the native LP minimizes $c^\top x$ with exact data, subject to $Ax=b$, $Bx\le d$ and $0\le x\le1$. Any rational multipliers $\lambda$ and $\mu\le0$ give the exact lower bound

$$
b^\top\lambda+d^\top\mu+
\sum_i\min\{0,c_i-(A^\top\lambda+B^\top\mu)_i\}.
$$

Negating the bound certifies the event maximization. The box-residual term handles imperfect numerical stationarity; no solver tolerance is declared to be zero. All 256 world/event certificates for the count decoder give a largest exact upper approximately .07383999804959, below the clean rational bound $923/12500=.07384$.

The stabilized full-history search then produced a tighter decoder in 41 iterations and 4,920 policy-oracle calls. Its numerical separation bound was .072000000889. Rational reconstruction and exact dual repair give a largest certified upper approximately .072000001122932, below the displayed rational bound .072000001123. An independent auditor checked all 128 world/events and 109,696 rational residual coordinates. The new upper is established by those exact inequalities, not by the numerical stopping criterion.

| Guarantee used on the exact optimizer set | Certified upper | Exact lower witness |
|:--|--:|--:|
| Previous source-universal full-count transfer | approximately .0790704 | .072 |
| Common count-state decoder over actual optimizers | .07384 | .072 |
| Common full-history decoder over actual optimizers | .072000001123 | .072 |

Why can full histories help a common decoder when signed counts are sufficient? Sufficiency holds separately for each fixed policy: its reverse count-to-history decoder depends on that policy. A single full-history decoder can therefore correspond to different count decoders for different policies. Requiring one count decoder for the entire family imposes a stronger restriction. This distinction concerns uniform decoder construction; it does not mean the count statistic loses information about the world for an individual known policy.

## What this says about objective comparison

The result compares an intrinsic objective through its entire optimizer set, not through one favorable tie-breaking policy. It separates four questions:

1. **Acquisition cost:** the exact finite-budget minimum is .0072.
2. **Scored capability:** all optimal six-coordinate profiles form the explicit segment above.
3. **Unscored capability:** the worst adaptive error lies in [.072,.072000001123].
4. **Proof conservatism:** the upper uses a common decoder, while deficiency permits policy-specific decoders.

The prior full-count analysis bounded every source experiment with suitable diagnostic errors. Restricting sources to policies feasible at this horizon supplies a stronger guarantee. The previous approximately .0790704 upper also applies to our smaller exact optimizer set, so it remains a valid but weaker upper here. The count-state certificate removes about 74% of that upper/lower gap; the full-history certificate leaves a width below two billionths. These reductions concern the guarantee, not an improvement in collected behavior.

This is a useful finite analogue of studying $O(J)$: ask which capability profiles objective-optimal or near-optimal policies can approach, then evaluate a requested target over that set. Here finite compactness gives attained extrema, so no infinite-policy or eventual-profile limit interchange is needed. There is no claim that the finite scored segment is the full eventual frontier, that its policies are completely explorative, or that the repeat objective dominates information gain for every future purpose.

![Left: the exact set of six scored optimal profiles, displayed through its two nonzero coordinates. Right: certified intervals for the same exact optimizer set; these are deterministic mathematical bounds, not statistical confidence intervals. The previous upper is rounded outward for the figure. The full-history interval is too narrow to resolve at this scale.](adaptive_envelope.pdf)

## Verification and remaining uncertainty

The exact minimum, lower witness, compressed native feasible set, and upper certificates are independently checkable artifacts. The production LP's feasible set is reconstructed independently rather than accepted from a solver serialization. The audit checks proportional likelihood columns, policy-dependent reverse garblings, exact target reductions, linear constraints, and rational dual residual corrections.

The original 30-start alternating lower search found no policy worse than .072. A further 300 starts, selected from 460 count-separation witnesses, used 604 actual-native policy-oracle calls and found no larger lower witness. These searches generate candidates only. The larger Bellman-family search is explicitly a failed relaxation, not evidence about the native argmin. An unstabilized full-history search reached its 100-iteration limit without a useful matching certificate; its result is retained separately. The successful stabilized search uses the same feasible policy set and target, with a secondary preference for staying near the count decoder among current best bounds.

One count-search iteration encountered a numerical replay failure when a flow around $10^{-12}$ had all its child flows clipped to zero. The LP itself had small residuals, but the invalid reconstructed policy was rejected. The saved earlier decoder was subsequently certified independently using exact LP bounds. A separate wrapper evaluates the raw linear experiment without that unnecessary policy normalization and preserves the original failed attempt.

A final bounded exact-polishing attempt recovered rational support vertices and projected the decoder onto selected boundary equations. One projection failed stochasticity; a minimum-norm version remained stochastic and improved numerical residuals, but partial exact checks still left a positive gap and did not certify all events. These [development probes](polishing_summary.json) do not replace the independently audited full-history certificate. Their optional temporary solver dependencies are separate from the main audit requirements.

**The primary exact sharpness criterion remains open:** the current rigorous interval is [.072,.072000001123]. The remaining discrepancy may be certificate construction and numerical reconstruction error; it is not evidence that a worse native-optimal policy exists. Exact equality requires an exactly feasible sharp upper certificate or another proof. Positive-regret sublevels, including the predecessor's .00720005 numerical threshold, require their own upper certificates; exact-face pruning cannot be reused for them.

The next mathematical step should seek an exact feasible decoder/dual certificate at .072, while retaining the option of a verified larger lower witness. Broadening the environment grid before resolving it would add cases without settling what the diagnostic objective actually leaves unspecified. The current work can support a paper discussion of objective-induced capability sets and certified bounds, while the claim of a sharp adaptive envelope should wait.

Reproduction and navigation: [frozen protocol](PROTOCOL.md), [proof note](theory/theory.pdf), [exact minimum and lower-witness audit](audit_results.json), [compressed model audit](audit_compressed.json), [rational count-decoder certificates](native_count_certificate.json), [full-history certificate](native_history_certificate.json), [independent full-history audit](audit_native_history_bound.json), and [research README](README.md). The main manuscript, Lean support ledger, and predecessor sealed scientific artifacts are unchanged.
