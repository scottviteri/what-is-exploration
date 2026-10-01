---
title: "Noisy native diagnostics under competing acquisition"
subtitle: "First research tranche: transfer theorem, exact obstruction, and complete finite-purpose envelopes"
author: "WhatIsExploration research"
date: "13 September 2026"
geometry: margin=0.8in
fontsize: 11pt
colorlinks: true
---

## What this study establishes

A small collection of noisy native diagnostics can support a **computable guarantee for additional experiments**, but separately reproducing noisy measurements does not ensure that their joint outcome can be reproduced. The missing information concerns how decoded outcomes depend on one another. This study gives a general finite certificate that controls that uncertainty, an exact counterexample inside a repeatable-sensor environment, and a complete finite-policy comparison of seven intrinsic objectives.

The strongest interpretation is constructive: specify the capabilities an objective scores, calculate what those capabilities guarantee elsewhere, and expose what remains unconstrained. The results do not establish a universal ordering of information gain, quadratic posterior gain, and native diagnostic losses. They contain both improvements and costs. They also show that apparently adequate diagnostic coverage at one acquisition budget need not remain adequate at a larger budget.

This is the first implemented tranche of the project proposed in the [12 September assessment](../intrinsic_objective_project_review_2026-09-12/README.md). The [protocol](PROTOCOL.md) was frozen before production. The selected manuscript and Lean claims have not been changed. New mathematical results are written proofs and exact finite rational certificates; the policy optimization results are independently checked floating-point LP solutions.[^artifacts]

## Model and comparison

The world is a fixed pair of bits, $\theta=(U,V)\in\{0,1\}^2$. At each step, the collector may read the left bit, read the right bit, or WAIT. Reading bit $j$ passes it through a binary symmetric channel with error $e_j$. Sensor noises are independent conditional on the world. WAIT returns a fixed symbol and changes nothing. All actions and observations remain in the record. The feasible class contains every randomized, history-dependent policy at the declared horizon.

We use horizons three and four; noise pairs $(.1,.1)$, $(.25,.25)$, and $(.1,.3)$; and posterior planning priors with independent bits, $P(U=1)\in\{.5,.01\}$ and $P(V=1)=.5$. Native objectives do not depend on that prior, so their computations are explicitly reused across the two prior settings. This is a supplied-model planning experiment, not a learned-agent benchmark.

For source experiment $E$ and target $T$, the native simulation error is

$$
\delta(E,T)=\min_G\max_{\theta}\operatorname{TV}(E_\theta G,T_\theta).
$$

The same stochastic decoder $G$ must work in every world. A different target may use a different decoder. The distance is total variation, not KL divergence.

Seven terminal objectives are compared. Information gain is the expected KL gain from prior to posterior, measured in bits. Quadratic gain is the expected increase in squared posterior norm. The remaining five minimize native losses:

| Objective | Scored native targets |
|:--|:--|
| Singles | One left reading and one right reading, weight .2 each |
| + tagged | Also a fair, recorded choice between those single readings, weight .1 |
| + joint | Also an actual left-then-right experiment, weight .1 |
| + repeats | Also three left readings and three right readings, weight .1 each |
| Minimax | Largest deficiency among all six targets above |

Weights are retained as the library grows; they are not renormalized. The repeat targets retain their whole records, not just majority votes. Three further targets are omitted from every objective: LLR, LRR, and an adaptive experiment that reads L first, then repeats L twice if its first observation is zero and otherwise reads R twice. These omitted targets test transfer.

For each objective, we optimize the **worst best-decoder performance over every near-optimal policy** for five subsequent purposes: guessing U, guessing V, guessing the full world, guessing parity, and guessing U under a different evaluation prior. The first four use the uniform world prior. Each endpoint has its own policy witness; the separate minima need not occur together.

The primary tolerances are 0%, 1%, and 5% of each objective's full feasible return range. WAIT makes the no-information baseline actually feasible, so this normalization is a genuine range. Secondary comparisons use the same absolute weighted-loss gap .005 across the four native sums. Full-range normalization removes positive affine rescaling, not arbitrary monotone transformations. Comparisons at zero gap mean a numerically checked optimum face, with residuals reported below.[^planner]

## The joint-capability obstruction is exact

At equal sensor error $e\in(0,1/2)$, let

$$
 a=1-e,\qquad A=1-3e^2+2e^3,\qquad
 \Delta=A-a=e(1-e)(1-2e),\qquad b=2e(1-e).
$$

Consider a four-step collector. It chooses a side fairly, measures that side three times, and switches to the other side for its final measurement with probability $1-b$. Otherwise it takes a fourth measurement on the original side. All schedule randomization is independent of sensor outcomes.

Majority decoding, with fair ties and a fair guess for a missing bit, reproduces each one-reading BSC experiment exactly. It therefore also reproduces the recorded random choice of a single reading. Nevertheless,

$$
 \delta(E,L)=\delta(E,R)=\delta(E,\mathrm{tagged})=0,
 \qquad \delta(E,LR)=2\Delta^2>0.
$$

The equality has both an explicit decoder upper bound and an exactly matching parity-decision lower bound. At noise .1, the joint deficiency is .010368. At noise .25 it is .017578125. This is a feasible policy in the actual independent-noise interface; it does not obtain correlated sensor noise by adding an unregistered action.

Adding LR to the weighted loss excludes this collector at exact optimality. The enlarged minimum is still zero because the collector can simply run LR and WAIT. At absolute regret $\eta$, its joint-target error is at most $\eta/.1$. This repairs the named failure. It does not certify all native capabilities: LR alone still loses $\Delta$ on the three-left-reading target.

A tagged choice of measurements and their joint execution thus play different roles. A fresh random choice between two existing decoders reproduces the tagged target. It does not supply the independent joint target law. The [proof note](theory/theory.pdf) derives this distinction and the matching certificates without relying on a numerical optimizer.[^theory]

## A transfer guarantee that applies beyond saved policies

Let $B_1,\ldots,B_m$ be finite noisy diagnostic experiments, and let

$$
 L_w(E)=\sum_j w_j\delta(E,B_j),\qquad w_j>0,\quad\sum_jw_j=1.
$$

Suppose we can find one stochastic repair decoder $D$, an intercept $b\ge0$, and a slope $\kappa\ge0$ such that, for every world and every joint diagnostic-output distribution $p$,

$$
 \operatorname{TV}(pD,T_\theta)
 \le b+\kappa\sum_jw_j\operatorname{TV}(p_j,B_{j,\theta}).
$$

Here $p_j$ is the $j$th marginal. Then **every finite-signal acquired experiment** satisfies

$$
 \delta(E,T)\le \min\{1,b+\kappa L_w(E)\}.
$$

The proof combines the individual diagnostic decoders on the acquired record and applies the repair. They may have independent auxiliary randomness conditional on the record, but their outputs can still be dependent after averaging over that record. The pointwise certificate explicitly handles every such coupling.

This certificate is computable as a finite LP. Partition the diagnostic-output simplex by the signs of its marginal discrepancies. On each cell, the right side is affine and the left side is convex; checking the vertices suffices. The optimization depends on diagnostic and target alphabets and the world class, rather than on the collection horizon or the size of the acquired record. It can still grow exponentially with the number of diagnostics.

For a weighted diagnostic objective with budget-dependent optimum $L^*_{w,H}$, the consequence for **all** $\eta$-near-optimal policies is

$$
 \delta(K_{\pi,H},T)\le
 \min\{1,b+\kappa(L^*_{w,H}+\eta)\}.
$$

The three terms have distinct meanings: residual ambiguity $b$, irreducible acquisition loss $L^*_{w,H}$, and optimization error $\eta$. The proof does not require the infimum to be attained. Additional model and evaluation errors can be included under explicit uniform error premises; the proof note states those premises.

We searched for 180 affine certificates and reconstructed exact rational decoders and intercepts. All 9,120 rational vertex checks passed, including an independent reconstruction of the vertices. Search optimality is not inferred from rational feasibility. These are universal-source upper bounds, not necessarily the sharp largest error among feasible four-step collectors.

For equally noisy single diagnostics, the optimal zero-loss **common-repair** residual for LR is $e(1-2e)$ when $e\le1/3$. It is .08 at noise .1. If the diagnostic bits instead have error $0\le d\le\min(e,1/4)$, with $e\le1/2$,, that residual is

$$
 \frac{d(1-2e)^2}{1-2d}.
$$

Majority-of-three diagnostics have $d=3e^2-2e^3$. At physical noise .1, their residual becomes $28/1475\approx.018983$. This is a structural improvement in transfer, before acquisition cost. Majority is only a garbling of the full repeat target, used for the proof.

For the protocol's unnormalized loss $S$, mean single-diagnostic deficiency is at most $S/.4$; for the repeat objective, mean majority-diagnostic deficiency is at most $S/.2$. At four steps and noise .1, the repeat objective has positive minimum .0072. Its actual guarantee must therefore include that cost. It would be incorrect to advertise the .018983 residual alone as its near-optimal transfer bound.

## What the completed envelopes show

| Objective | Planning q | U | V | World | Parity | Asymmetric U |
|:--|--:|--:|--:|--:|--:|--:|
| Information gain | 0.5 | 0.900000 | 0.900000 | 0.874800 | 0.877600 | 0.936900 |
| Quadratic gain | 0.5 | 0.900000 | 0.900000 | 0.874800 | 0.877600 | 0.936900 |
| Information gain | 0.01 | 0.792000 | 0.972000 | 0.777600 | 0.791200 | 0.859500 |
| Quadratic gain | 0.01 | 0.792000 | 0.972000 | 0.777600 | 0.791200 | 0.859500 |
| Singles | any | 0.900000 | 0.900000 | 0.802899 | 0.805797 | 0.900000 |
| + tagged | any | 0.900000 | 0.900000 | 0.802899 | 0.805797 | 0.900000 |
| + joint | any | 0.900000 | 0.900000 | 0.810000 | 0.820000 | 0.900000 |
| + repeats | any | 0.900000 | 0.900000 | 0.874800 | 0.877600 | 0.900000 |
| Minimax | any | 0.936000 | 0.936000 | 0.874800 | 0.877600 | 0.936000 |

The table reports lower guaranteed accuracies over whole optimal policy sets at horizon four and noise .1. In particular:

- **A small native library leaves real freedom.** Singles and + tagged guarantee .9 on each individual bit, yet their worst world and parity guarantees are below the LR experiment's .81 and .82. Adding LR restores those thresholds.
- **Refinement can improve later uses.** Adding repeat targets reaches the uniform-prior posterior objectives' worst world and parity accuracies in this setting. It does not match their asymmetric-U guarantee, so this is not equivalence of optimal capability sets.
- **Posterior priors change what is protected.** With planning prior $P(U=1)=.01$, the posterior objectives allow substantially weaker U and parity capability under the uniform evaluation prior. They give stronger V protection. The interpretation depends on the stated subsequent use.
- **Minimax makes another tradeoff.** It protects both individual bits more strongly here. It is a minimax score on six targets, not an exhaustive native audit or universal dominance result.

Horizon three supplies an additional contrast. At noise .1, every singles-optimal policy has world value at least .81 and parity value at least .82. At horizon four those envelopes fall to approximately .802899 and .805797. More observations have not harmed a particular policy's evidence: a larger feasible policy set has admitted additional weak optimizers of an underspecified objective.

The general reason is simple. WAIT embeds an earlier acquired experiment into a later horizon. If the fixed objective is invariant under uninformative padding and its optimal value is unchanged, the later near-optimal set contains the earlier set at the same absolute tolerance. Its worst purpose value can only decrease. For the first three native sums, the optimum is zero and the no-data loss is unchanged at both budgets, so the statement also applies to their chosen range normalization. A successful small-budget check does not certify that a fixed finite diagnostic library remains sufficient.

The asymmetry controls also prevent a one-sided account. At horizon three and noise $(.1,.3)$, uniform-prior information gain and quadratic gain guarantee world accuracy .648, whereas the first four native sums guarantee .63. Minimax gives .628 while slightly improving the lower guarantee for V. These objectives choose different sacrifices even without a rare-world prior.

![Complete purpose envelopes at horizon four and sensor error .1. Rows change the posterior planning prior; native curves are reused because their objectives are prior independent. Each point is a separate full-policy optimization. Connecting segments guide the eye and are not certified interpolations.](purpose_envelopes.pdf)

## Transfer outcomes and the strength of the evidence

The analysis contains 684 objective/tolerance/target transfer cases, including 342 held-out cases. Every held-out case has an upper bound below its no-data error. In 291 held-out cases, the common-repair certificate improves on both the listed triangle and contraction-improved reconstruction baselines. These are counts across one structured grid, not independent statistical replications.

At H=4, noise .1, and nominal zero regret:

| Objective | Omitted target | Saved-policy lower witness* | Guaranteed upper | Best bound |
|:--|:--|--:|--:|:--|
| Singles | LLR | 0.072000 | 0.080000 | coupling |
| Singles | adaptive_L | 0.098642 | 0.129600 | coupling |
| + joint | LLR | 0.072000 | 0.072001 | triangle |
| + joint | adaptive_L | 0.098642 | 0.124364 | triangle |
| + repeats | LLR | 0.072000 | 0.079769 | coupling |
| + repeats | adaptive_L | 0.072000 | 0.093452 | coupling |
| Minimax | LLR | 0.036000 | 0.079768 | coupling |
| Minimax | adaptive_L | 0.060840 | 0.093452 | coupling |

*Lower witnesses use the explicitly enlarged numerical cost sublevel described below. Upper numbers are rounded for display; the CSV retains the actual values.

The adaptive target illustrates genuine transfer: its upper bound falls from about .129600 for singles to .093452 for repeats, even though this target is absent from both objectives and the repeat minimum is positive. Refinement does not uniformly tighten the generic bounds: for LLR, the + joint certificate is about .072001, whereas the repeat bound is about .079769. A looser upper bound does not prove worse behavior; the saved repeat-optimal LLR witness is .072, leaving a visible gap to resolve.

Three sorts of evidence must remain separate. The purpose endpoints are complete finite-policy LP optimizations for the named purpose. The rational affine transfer certificates bound all eligible acquired experiments, including targets omitted from the objective. Errors of saved policies supply examples and lower witnesses only; maximizing those observations does not compute a complete worst-deficiency envelope.

For numerical transfer tables, pooled witness eligibility uses the feasible optimum estimate plus the raw regret and an explicit $5\times10^{-8}$ enlargement. Upper bounds use that same enlarged cost sublevel. They conservatively apply to the intended near-optimal set; a lower witness for the enlargement is not an exact zero-regret witness. The table records the optimum bracket, witness cost, and enlargement. The exact four-step obstruction above needs no such numerical qualification.

We compare the repair certificates with individual-diagnostic and tagged-mixture deficiency triangle bounds and a world-reconstruction union bound improved by the target's Dobrushin contraction coefficient. The best bound is retained, including the no-data baseline. A repair certificate beating those baselines is evidence that it extracts additional consequences from simultaneous marginal guarantees; it is not proof of a sharp budget-restricted transfer curve.

## Verification and reproducibility

The complete grid contains **54 distinct optima and 930 purpose envelopes** (810 primary and 120 common-absolute-gap controls), with no missing cases and explicit native-prior reuse. Both production stages and both independent audits passed. The auditor checked 984 returned collectors and their full planning certificates, using 7,592 independently assembled decoder LPs. The largest independent-versus-saved deficiency discrepancy was $1.51\times10^{-10}$; the largest residual of any kind was $2.89\times10^{-8}$, from a decoder row normalization. These are float64 numerical checks, not interval proofs.

The four production invocations took a summed 629.25 seconds, with some overlap. Independent H3 and H4 audits took about 25.10 and 37.13 seconds respectively. Exact controls, certificate search, report preparation and development time are additional. Resume-stage `run_seconds` fields alone would undercount production runtime. See [runtime provenance](planner_runs.json), [H3 audit](audit_h3.json), [H4 audit](audit_h4.json), and [exact controls](audit_controls.json).

The independent auditor imports no planner implementation. It reconstructs target laws and policy-induced source rows from literal histories, solves separate fixed-source decoder LPs, checks stored decoder and decision witnesses, checks full planning primal/dual certificates and their binding to the recovered policy, and verifies objective cuts. Posterior and purpose benchmarks are also compared with independent dynamic programming. All 2,187 deterministic three-step observation-tree plans per noise setting are enumerated for additional controls. Additional prescriptions on unreachable histories do not change the induced experiment.

Full-history realization weights represent all behavioral randomized policies, including mixtures whose components individually fail the objective threshold. Decoder allocations keep positive weighted deficiency minimization linear. The purpose envelope minimizes an epigraph of the optimized decision value under the original objective constraint. The implementation does not maximize a loose deficiency epigraph.

Reproduction commands, artifact formats, source hashes, numerical tolerances and runtime records are linked from the [study entry point](README.md) and [planner schema](PLANNER_SCHEMA.md). Every production optimum and envelope retains its policy, full LP certificate, and fixed-source deficiency witnesses. The protocol and production implementation remained unchanged across the grid. No production failure or tolerance amendment occurred.

## How this advances the project

The most useful paper contribution here is a chain of claims: **finite noisy diagnostics can be optimized; their near-optima admit explicit transfer bounds; noisy marginals leave provable joint gaps; and adding capabilities changes the whole allowed set, with costs visible at a binding acquisition budget.** This goes beyond scoring an objective on its own audit or reproducing rare-prior neglect.

It also clarifies the relation to $J_w$ and $O(J)$. These experiments optimize finite terminal diagnostic sums. Their target weights can be extended to a countable family, but a finite sum is not the full eventual $J_w$ and need not be strictly monotone for the full native order or natively calibrated. In the repeatable-sensor model, an exploratory infinite continuation can eventually learn both bits after any fixed finite prefix. Eventual optimal profiles therefore do not resolve the finite-budget differences measured here. The near-optimal capability set indexed by horizon, library, and objective tolerance is the relevant comparison object.

This tranche is a credible candidate for a focused theorem-and-experiment section. It supplies a checked guarantee beyond the scored list and a causal counterexample showing why the guarantee needs a residual. It does not yet supply a practical model-free implementation, broad environmental validation, or sharp target-error envelopes. We should not replace the current main experiment merely because the new one has more computations.

The next bounded research question is **how much looseness comes from discarding repeat-record confidence and how much is unavoidable at the acquisition budget**. Compare the current binary-majority transfer certificate with a certificate using full repeat-count diagnostics, on the same frozen collectors and targets. Each four-valued diagnostic records the number of ones among three observations. It preserves the full triple experiment: conditional on the count, ordered words are uniformly distributed independently of the world. That changes the analysis of existing evidence rather than confounding it with a new reward or a new environment. If it materially narrows the held-out upper/lower gap, then test whether a substantially smaller diagnostic library can retain that guarantee. If it does not, the current residual and acquisition-cost decomposition remain the defensible result.

[^artifacts]: [Frozen protocol](PROTOCOL.md), [analysis](analysis.json), [complete envelope table](envelopes.csv), [transfer bounds](transfer_bounds.csv), and [theoretical proofs](theory/theory.pdf).

[^planner]: [Planner implementation](compute.py), [schema and LP explanation](PLANNER_SCHEMA.md), [three-step output](results/results.json), and [four-step output](results_h4/results.json).

[^theory]: [Proof source](theory/theory.tex), [rational certificate generator](theory/certificates.py), [exact certificate output](theory/certificates.json), and [independent controls](audit_controls.json).
