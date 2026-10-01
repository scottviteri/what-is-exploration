# Adaptive native-target weights: guarantees, counterexamples, and algorithmic boundaries

23 September 2026. Research only. This note develops the authorized adaptive-weight program without modifying the manuscript, support ledger, frozen campaign, or existing experiment code. **Every new proposition below is proved on paper here, not newly Lean-formalized.** Existing declarations are identified separately in Section 1. No Lean build, solver, benchmark or training was run to produce these arguments. The separate solver-free checks in `check.py` subsequently verify tiny exact examples, including the fixed-dual recursion and native nonconcavity witness; they are not proofs of the general propositions.

The useful mathematical freedom is to adapt a probability distribution over targets while preserving a fixed positive background. This keeps the full eventual objective sensitive to every native capability, but gives an implementable finite approximation only after its omitted weight and numerical errors are charged. Adaptive easy-target selection and adversarial hard-target selection solve different problems. Neither inherits a convergence theorem merely from positivity.

## 1. Objects and inspected existing support

Fix a nonempty class of controlled-prefix behaviors and finite nonempty action and observation sets, `A` and `O`. A valid policy uses the recorded history and independent randomization, not the actual world label. Its record after collection time `t` induces the statistical experiment `K_(pi,t)`. A native target `T_j` is the complete action–observation record of another valid policy run for a finite target depth `n_j` through the same interface and world class.

For experiments `E` and `T`, write

\[
 \delta(E,T)=\inf_G\sup_\theta\operatorname{TV}(E_\theta G,T_\theta),
\]

where `G` is a stochastic decoder independent of the unknown world. Different targets may use different decoders. With total variation normalized to lie in `[0,1]`, define

\[
 d_{j,t}(\pi)=\delta(K_{\pi,t},T_j),\qquad
 \ell_j(\pi)=\inf_t d_{j,t}(\pi).
\]

The finite-time errors decrease with `t`, since a longer source record can be projected to its prefix. Thus `ell_j` is their limit. For a normalized nonnegative weight sequence `w`, define losses and the eventual score

\[
 L_{w,t}(\pi)=\sum_jw_jd_{j,t}(\pi),\quad
 L_w(\pi)=\sum_jw_j\ell_j(\pi),\quad J_w=1-L_w.
\]

Bounded convergence gives `L_(w,t)(pi) -> L_w(pi)` for each fixed policy and weighting. This is pointwise convergence, with no policy-uniform rate. Optimizing a finite selected sum at one collection time is a third object; it is not identical to either full sum.

A family is **rich** when every finite native record can be approximated arbitrarily closely in world-uniform row TV, on the same output alphabet, by a target in the family. For a rich countable family, coordinatewise comparison of eventual losses represents the full finitary process order. Write `rho >=_fin pi` when `rho` can eventually simulate every finite prefix of `pi`. Then all `ell_j(rho) <= ell_j(pi)`, and a strict order improvement improves some coordinate strictly.

The following existing support was read, including its actual assumptions and claim-level boundaries:

| Existing result | Inspected declarations and source | Scope retained here |
| --- | --- | --- |
| Rich native order representation and positive scalarization | `causalFinitaryDominates_iff_eventualLoss`, `weightedFinitaryObjective_mono`, `weightedFinitaryObjective_strict` in `Formal/Formal/StrictFinitaryObjective.lean`; `weightedLossObjective_strictlyFinitaryMonotone`, `strictlyFinitary_maximizer_iff_greatest` in `FinitaryObjectiveCore.lean` | Finite nonempty interfaces; arbitrary nonempty world class; valid responses/experiments or their behavior wrapper; rich family; positive summable weights. No effective optimizer or acquisition rate. |
| Literal rational native policies | `causalFiniteExperiment_tv_le_horizon_mul_rowTV`, `rationalNativePolicyFamily_uniform_dense`, `causalBehavior_finitary_iff_rationalNativeLoss` in `RationalNativeTargets.lean` | Uniformity over worlds, randomized action tables, null histories, and retained actions are explicit. The existing enumerator uses `Classical.choose`; executable denominator/rank enumeration below is a separate paper construction. |
| Coordinate bounds and approachable completion | `profile_coordinate_le_weighted_regret`, `weightedProfileScore_sup_eq_one`, `weightedProfileScore_calibration` in `CapabilityProfileScores.lean`; `exists_causalBehavior_weighted_native_calibration` in `NativeCapabilitySelection.lean` | Positive summable weights and zero in the closure of feasible profiles give calibration, even without an attaining sufficient policy. The basic coordinate bound uses `1-J`, not regret relative to a nonzero optimum. |
| Regularity | `continuous_weightedScore`, `tendsto_weightedScore`, `lowerSemicontinuous_weightedScore` in `WeightedObjectiveRegularity.lean` | Continuous finite-stage scores and decreasing bounded losses give a lower-semicontinuous eventual **score**; the eventual **loss** is upper semicontinuous. |
| Policy-limit obstruction | `delayedTest_nativelySufficient`, `alwaysWait_immediate_deficiency`, `tendsto_delayedTest_policyTable`, `no_tableContinuous_strictly_finitary_objective` in `FinitaryContinuityObstruction.lean` | Delaying exact revelation preserves eventual sufficiency while the tables approach never revealing. |

The corresponding ledger entries read were `thm:strict-finitary-objective`, `claim:rational-native-target-density`, `prop:capability-profile-scalarization`, and `thm:capability-selected-profiles`, together with the relevant `Formal/OPEN_PROBLEMS.md` boundary. The selected written proof is `Paper/draft/next_structural_proofs.tex`; current context is `Paper/CURRENT_THEORY_STATE.tex`, the full reader, and the selected `exploration_decision.tex`. These sources record previously checked support; this assignment did **not** freshly revalidate it or extend its registration.

## 2. An explicit rich background, with its arbitrary choices exposed

Fix orders on `A` and `O`, and lexicographic orders on histories and integer compositions. Put `a=|A|`, `o=|O|`. At target depth `n >= 0`, a full behavioral table has

\[
 M_n=\sum_{r=0}^{n-1}(ao)^r
\]

rows, including every syntactic history, whether reachable or not. For a common denominator `d >= 1`, a row is an `a`-tuple of nonnegative integers summing to `d`, divided by `d`. There are `binom(d+a-1,a-1)` such rows, so the number of complete tables at `(n,d)` is

\[
 N_{n,d}=\binom{d+a-1}{a-1}^{M_n}.
\]

When `n=0`, the exponent is zero and there is exactly one empty table. Rank tables lexicographically by `k=0,...,N_(n,d)-1`. Extend each table after depth `n` by one fixed action. Its depth-`n` record is the target `T_(n,d,k)`. Enumerate triples by increasing `n+d`, then the finite ranges of `n,d,k`. This is a syntactic executable enumeration, although some layers are prohibitively large. Computing a target's actual law still requires access to the declared model, and computing its deficiency may be difficult or unavailable.

**Proposition 1 (normalization and richness, paper proof).** The mass assignment

\[
 b_{n,d,k}=\frac{2^{-(n+1)}2^{-d}}{N_{n,d}}
\]

is strictly positive and sums to one. Its native targets are rich.

**Proof.** Summing over `k` leaves `2^-(n+1) 2^-d`; the sums over `n>=0` and `d>=1` are both one. Every rational finite table has a common denominator, so appears. To approximate a real row, round its first `a-1` coordinates down to multiples of `1/d`, and put the remaining probability on the last coordinate. Row TV is at most `(a-1)/d`; the bound is zero when `a=1`. Couple the two policies until their first different action. The chance of any disagreement through `n` rounds is at most `n(a-1)/d`, uniformly over the behavior. The same bound holds for their retained record laws, proving density as `d` grows. ∎

The weights are not canonical. A rational table appears at multiples of its denominator; tables can differ only at histories that the interface never reaches; distinct policies can induce identical experiments; and different horizons can yield equivalent experiments. Keeping these encodings as separate indices is mathematically valid. Their mass adds whenever their losses agree. Deleting duplicate encodings without redistributing their mass changes the objective. Aggregation is safe when experiment equality or mutual exact simulation is established uniformly over worlds; semantic equivalence need not be decidable in a general model class. Relabeling symbols or changing the encoding convention can change the induced preferences between incomparable profiles. Freeze the convention in the objective manifest and vary it explicitly in sensitivity studies.

Depth zero receives background mass `1/2` and has zero loss for every collector. This is harmless for order representation but dilutes quantitative bounds. An alternative background can restrict to positive depths and renormalize; that changes the declared objective. The depth-zero convention is useful below because it exposes cooperative weight selection exactly. Neither convention is scientifically privileged.

For a finite rectangular prefix containing every table with `n<=N` and `d<=D`, the retained background mass is

\[
 (1-2^{-(N+1)})(1-2^{-D}).
\]

This computable tail formula does not make enumeration cheap: even one included layer can contain far too many tables. For arbitrary selected finite index sets, sum their individual exact masses instead.

## 3. Adaptive weights with a persistent positive floor

Fix `0<epsilon<1` and a background `b` as above. At optimization round `r`, choose a probability vector `v^(r)` on the target indices, usually with finite support, and set

\[
 w_j^{(r)}=(1-\epsilon)v_j^{(r)}+\epsilon b_j.
\]

**Proposition 2 (each final objective retains strictness).** Every realized vector `w^(r)` is positive, normalized, and satisfies `w_j^(r)>=epsilon b_j`. Therefore its full eventual score strictly rewards every strict finitary improvement. Every attained maximum in a feasible policy family is undominated there. If the family contains a natively sufficient policy, its maxima are exactly its sufficient members.

**Proof.** Positivity and normalization follow directly. For a strict dominator `rho` of `pi`, every difference `ell_j(pi)-ell_j(rho)` is nonnegative and one is positive. Its positive weighted sum is strictly positive. The optimizer conclusions follow by comparing a proposed maximum with its dominator or with a feasible sufficient policy. ∎

The adaptive procedure may depend on previous optimization attempts or saved training evidence. For any realized output, freeze **one common weighting** and evaluate all compared policies with that weighting. If different worlds induce different optimization histories, this algebraic statement applies pathwise to the realized vector; it does not identify a world-dependent weight rule with a single world-independent objective on experiments. It supplies no common-comparison theorem for scores evaluated using a different vector for each policy, world, or realized record. Objective manifests must identify the final common weighting and selection history; independent evaluation must remain fixed.

Strictness is an exact statement, potentially numerically invisible. Improving target `j` by `Delta` contributes at least `epsilon b_j Delta`, which may be tiny under the explicit rich background. No positive normalized countable weighting can give one positive lower bound on every coordinate weight.

## 4. Finite truncation and certificates

Let `S` be a finite selected index set containing the support of `v`. Define

\[
 P_{w,S,t}(\pi)=\sum_{j\in S}w_jd_{j,t}(\pi),\qquad
 \beta=\sum_{j\notin S}w_j
       =\epsilon\left(1-\sum_{j\in S}b_j\right)\le\epsilon.
\]

**Proposition 3 (finite-time truncation).** For every policy,

\[
 P_{w,S,t}(\pi)\le L_{w,t}(\pi)\le P_{w,S,t}(\pi)+\beta.
\]

The same bounds hold with eventual losses in every term. These are tail bounds, not finite-to-eventual bounds.

**Proof.** Each omitted loss is in `[0,1]`, so its nonnegative weighted contribution is at most the omitted mass. ∎

Suppose retained target decoders/dual witnesses certify `lower_j <= d_(j,t)(pi) <= upper_j`. Their intervals need not be exact arithmetic proofs; their provenance must say what kind of residual-certified or rigorous bound is supplied. Set

\[
 D=\sum_{j\in S}w_j\underline d_j,\qquad
 U=\sum_{j\in S}w_j\overline d_j.
\]

Then `[D,U+beta]`, intersected with `[0,1]`, bounds the candidate's full finite-time loss, and `[1-U-beta,1-D]`, intersected with `[0,1]`, bounds its full finite-time score. Only the lower score bound `J_w(pi)>=1-U-beta` transfers immediately to the eventual score; finite-time dual lower bounds are not eventual-loss lower bounds.

Let `P` be the declared nonempty feasible policy family, and suppose a freshly validated master supplies

\[
 B\le\inf_{\rho\in\mathcal P}P_{w,S,t}(\rho).
\]

**Proposition 4 (full finite-time optimization certificate).** The candidate satisfies

\[
 L_{w,t}(\pi)-\inf_{\rho\in\mathcal P}L_{w,t}(\rho)
 \le U+\beta-B.
\]

If its selected-objective gap is at most `eta`, its full finite-time gap is at most `eta+beta`.

**Proof.** The candidate's full loss is at most `U+beta`, whereas the full optimum is at least the selected optimum and hence at least `B`. ∎

The coefficient `beta` occurs once, not twice, because the omitted losses are nonnegative. If a solver reports only relative error or uncertified objective values, those must first be converted into an appropriate absolute bound; positivity does not perform that conversion.

### What is missing for eventual regret

Write `m_t=inf_P L_(w,t)` and `m=inf_P L_w`. The finite certificate yields only

\[
 L_w(\pi)-m\le U+\beta-B+(m_t-m).
\]

Here `m_t-m>=0` is a finite-to-eventual optimization lag. A sufficient way to bound it is a uniform estimate `0<=L_(w,t)(rho)-L_w(rho)<=r_t` over feasible `rho`, giving an additive `r_t`. A weaker comparator-specific route suffices: if some feasible `rho` has `L_w(rho)<=m+kappa` and finite-to-eventual lag at most `r`, then `m_t-m<=kappa+r`. Neither lag follows from omitted mass.

Indeed, restrict the feasible family in a WAIT/REVEAL interface to policies that all wait through time `t`. One reveals at `t+1`; another waits forever. Their entire finite-time profiles agree, so both exactly minimize every finite-time weighted objective on this family. The first is sufficient, while the second has positive rich eventual loss. Even `beta=eta=0` does not certify eventual optimality.

An independently useful positive conclusion needs no lag: if `U+beta<=zeta`, then

\[
 \ell_j(\pi)\le L_w(\pi)/w_j\le\zeta/(\epsilon b_j).
\]

This is score-near-one calibration, not a conversion of an arbitrary small finite optimization gap. It can be weak even when the finite optimizer is certified precisely.

### A rate-free asymptotic consequence with a fixed feasible family

There is nevertheless a positive asymptotic fact. For fixed `w` and the **same feasible family of full policies at every collection time**,

\[
 \inf_t m_t
 =\inf_t\inf_{\pi\in\mathcal P}L_{w,t}(\pi)
 =\inf_{\pi\in\mathcal P}\inf_t L_{w,t}(\pi)
 =\inf_{\pi\in\mathcal P}L_w(\pi)=m.
\]

Because `m_t` decreases, it converges to `m`. Thus policies with vanishing full finite-time optimization error at times tending to infinity have vanishing eventual regret for a fixed weighting, even without policy-uniform convergence of the losses. This supplies **no computable finite-time rate** and no guarantee for a family that silently changes with the horizon. A finite prefix optimizer can be extended to any valid tail for the comparison, provided the resulting full policies belong to the declared feasible family.

For clarity, the world class, interface, indexed targets, and feasible full-policy family are fixed throughout this limit. The proof uses normalized nonnegative summable weights, bounded target losses, prefix refinement, and therefore pointwise `L_(w,t)(pi) downarrow L_w(pi)`. It requires neither a minimizer nor compactness of the policy family: the two infima commute as infima over the same product set. If `t_r -> infinity` and the full finite-time optimization error is `eta_r`, the explicit comparison is

\[
 0\le L_{w_r}(\pi_r)-m(w_r)
 \le \eta_r+[m_{t_r}(w_r)-m(w_r)].
\]

For fixed weights the bracket vanishes; for varying weights the following uniform argument supplies precisely the additional premise. Merely repeating a fixed finite collection time does not meet it. Restricting a solver to a growing parametric family requires a separate approximation argument to the common feasible family; it is not covered automatically.

The statement extends to changing weights drawn from a fixed totally bounded set in total variation. Both `m_t(w)` and `m(w)` are 1-Lipschitz in weight TV by Proposition 7, so their difference is 2-Lipschitz. For any positive tolerance, cover the weight set by finitely many sufficiently small TV balls. At each center choose a time after which its lag is small; take the maximum of these finitely many times and use the Lipschitz bound inside each ball. The lag then vanishes uniformly on the weight set. In particular, with a fixed background and floor, emphasis distributions on **one fixed finite library** satisfy this condition. Emphasis on arbitrarily moving or expanding finite supports need not do so; fixed positivity alone is not a TV-compactness premise.

Combining this fact with Proposition 6 gives a conditional adaptive calibration result: with approachable zero, fixed positive floor, a TV-totally-bounded set of weights, collection times tending to infinity, and full finite-time optimization errors tending to zero, the eventual target errors tend to zero. A truncated implementation must also make its certified omitted-tail error vanish. These hypotheses describe a possible future convergence theorem, not something demonstrated by the finite campaign or prepared dry run.

## 5. Approximate optimality, capability, and dominance

For a final fixed `w`, let the eventual minimization regret be

\[
 g_w(\pi)=L_w(\pi)-\inf_{\rho\in\mathcal P}L_w(\rho).
\]

For any coordinate,

\[
 \ell_j(\pi)\le\min\{1,L_w(\pi)/w_j\}.
\]

Replacing `L_w` by `g_w` requires the additional premise `inf_P L_w=0`. This holds when the zero profile lies in the closure of feasible rich profiles, in particular when a sufficient feasible policy exists. It need not hold otherwise.

**Proposition 5 (regret limits improvements by a dominator).** If `rho` is feasible and finitarily dominates `pi`, then

\[
 \sum_j w_j[\ell_j(\pi)-\ell_j(\rho)]\le g_w(\pi).
\]

Consequently, for every `j`,

\[
 \ell_j(\pi)-\ell_j(\rho)\le
 \frac{g_w(\pi)}{w_j}\le\frac{g_w(\pi)}{\epsilon b_j}.
\]

**Proof.** The sum is `L_w(pi)-L_w(rho)`, at most `L_w(pi)-inf_P L_w`. Every term is nonnegative, so each is bounded by the sum. ∎

This statement needs no zero optimum and is the appropriate quantitative extension of “no dominated exact optimum.” It does not control an incomparable policy's gain in one coordinate: that gain may be paid for by a loss elsewhere. It also does not assert a uniform positive distance from the dominated region.

**Proposition 6 (adaptive calibration without convergence of weights).** Suppose zero is in the closure of feasible rich profiles, the same `epsilon,b` are used at every round, and

\[
 L_{w^{(r)}}(\pi_r)-\inf_{\rho\in\mathcal P}L_{w^{(r)}}(\rho)
 \le\eta_r\longrightarrow0.
\]

Then every fixed coordinate satisfies

\[
 \ell_j(\pi_r)\le\eta_r/(\epsilon b_j)\longrightarrow0.
\]

Hence the eventual rich profiles converge to zero, and by target density the eventual deficiency to every fixed finite randomized native target also tends to zero.

**Proof.** For each realized positive summable weighting, zero in the feasible-profile closure makes the infimum zero: continuity of a bounded summable weighted sum in the product profile topology gives arbitrarily small loss. Apply the coordinate inequality and the common floor. For an arbitrary finite target, choose one rich approximation within `xi` uniformly over worlds. Target perturbation bounds its eventual error by the chosen rich coordinate plus `xi`; let first `r` grow and then `xi` shrink. ∎

The weights need not converge. The required regret is relative to the **full eventual final-weight objective** at that round; a finite truncated solver does not provide it without Section 4's extra conditions. No common collection deadline, single limiting successful policy, or successful online trajectory is implied.

A varying floor `epsilon_r` is sufficient if `eta_r/epsilon_r -> 0`; merely `eta_r -> 0` is insufficient. To see this with actual native targets, let `v` put all mass on the empty target, use a WAIT/REVEAL class with a sufficient reveal policy, and keep the candidate equal to never revealing. Its regret is `epsilon_r L_b(never) -> 0` when `epsilon_r -> 0`, while its reveal-target deficiency stays `1/2`. Every individual objective still has only sufficient exact maxima. It is approximate optimization under vanishing protection that fails.

## 6. Perturbing or converging weights

For probability sequences `w,w'`, define their total variation distance

\[
 D(w,w')=\tfrac12\sum_j|w_j-w'_j|.
\]

**Proposition 7 (uniform weight perturbation).** For any bounded loss profile in `[0,1]^N`, finite or countable,

\[
 |L_w(\pi)-L_{w'}(\pi)|\le D(w,w').
\]

The same holds at finite collection time. Their infima over any common nonempty feasible family differ by at most `D`. Therefore `eta`-optimality for `w` implies `(eta+2D)`-optimality for `w'`.

**Proof.** The positive and negative parts of `w-w'` both have mass `D`. Maximizing their dot product with numbers in `[0,1]` gives `D`; minimizing gives `-D`. Take infima, and insert the old candidate value and old infimum between the new ones. ∎

With a common background and fixed floor, `D(w,w')=(1-epsilon)D(v,v')`. A total certified weight-movement budget can therefore transport an old bound conservatively. Re-solving the cached master under the new objective generally gives a tighter bound. A common feasible policy and its decoder witnesses can be rescored directly under the new weights.

If `D(w^(r),w*) -> 0` and final-weight eventual regrets tend to zero, the policies are asymptotically optimal for `w*`. Positivity of `w*` is an additional condition for its strictness; fixed positive background ensures it. Coordinatewise convergence of probability weights to a normalized probability limit implies convergence in total variation: choose a finite set holding nearly all limiting mass, use convergence there, and bound both tails. Without normalization of the limit, mass may escape to indices tending to infinity, so coordinatewise convergence alone is insufficient. A summable sequence of total-variation changes makes the weights Cauchy in `l1` and gives a normalized limit, but does not establish vanishing optimization regret.

Even when weights converge and all eventual losses are zero, a limit of **policy tables** can fail. Let `pi_r` wait `r` steps then reveal one hidden bit exactly. All are sufficient; their tablewise limit waits forever and has reveal deficiency `1/2`. The eventual loss is upper semicontinuous, whereas passing a minimizing sequence to an optimal policy limit would require an appropriate lower-semicontinuity premise. In profile space, the loss is continuous and the profile closure is compact, but a limiting profile need not be attained by a policy. Compactness must not be transferred between these two spaces silently.

## 7. Cooperative easy-target selection can change the scientific question

Allow the optimizer to select both its collector `pi` and `v`, minimizing

\[
 (1-\epsilon)\sum_jv_j\ell_j(\pi)+\epsilon L_b(\pi).
\]

For a fixed policy, the infimum over all probability vectors `v` is

\[
 (1-\epsilon)\inf_j\ell_j(\pi)+\epsilon L_b(\pi).
\]

When the empty native target is available, its loss is zero, so this becomes **exactly `epsilon L_b(pi)`**. The same identity holds at finite collection time. Cooperative adaptation then removes all the intended emphasis except the background; it does **not** make every policy exactly optimal. If a sufficient policy is feasible and `epsilon>0`, the exact optima remain sufficient. However, an absolute optimization tolerance of `eta` now permits background-loss regret `eta/epsilon`, and easy selected targets can make a reported score look excellent while hard independent targets remain poor.

A finite restricted library can exhibit a more direct conflict with a worst-target audit. Consider a four-world interface with hidden bits `(u,v)`. The first action is `READ_U` or `READ_V`, returns that bit, and commits permanently to world-independent subsequent observations. The first action is retained. A policy is characterized, for information purposes, by its world-independent probability `x` of reading `u`. Let the two targets be the deterministic one-step reads. Their permanent losses are

\[
 d_U(x)=\ell_U(x)=(1-x)/2,\qquad
 d_V(x)=\ell_V(x)=x/2.
\]

**Proof of these native losses.** To simulate `u`, use the observed `u` on the `READ_U` branch and guess a fair bit on the other; every world has error `(1-x)/2`. For the lower bound, choose two worlds with equal `v` and opposite `u`. Their acquired laws have TV `x`, whereas their `u` targets have TV one. Data processing and the triangle inequality force maximum decoder error at least `(1-x)/2`. The `v` proof is symmetric. Later world-independent padding cannot improve either experiment. ∎

Use the finite background `(1/2,1/2)` and let cooperative `v` range over these two targets. Its optimized loss is

\[
 (1-\epsilon)\min\{x,1-x\}/2+\epsilon/4.
\]

For `0<epsilon<1`, the exact optima are `x=0` and `x=1`, whose worst-target error is `1/2`. Direct minimax uniquely selects `x=1/2`, whose worst-target error is `1/4`. This is a literal native counterexample for cooperative finite selection, not an abstract profile presumed realizable. It uses a finite background; no full-order richness conclusion is drawn from it. In the unrestricted rich family containing the empty target, the preceding collapse-to-background identity is the appropriate conclusion instead.

Tractability-driven weighting can still be useful as a declared way to find a cheaper approximate objective. Its useful outcome would be reduced certified computation for the selected objective with honestly reported independent capability, not a theorem that making targets cheap makes all capabilities better.

## 8. Adversarial weights, minimax, and the role of the background

Let `S` be a nonempty finite target library. For any loss vector,

\[
 \max_{v\in\Delta(S)}\sum_{j\in S}v_jd_j(\pi)
   =\max_{j\in S}d_j(\pi).
\]

The upper bound holds because an average is no larger than its largest term, and a point mass on a maximizing coordinate attains equality. With the rich background, the robust finite-time loss is

\[
 F_t(\pi)=(1-\epsilon)\max_{j\in S}d_{j,t}(\pi)
          +\epsilon L_{b,t}(\pi).
\]

Its eventual counterpart replaces all finite-time errors by `ell_j`. The background sum still includes targets outside `S`; replacing it by a finite normalized background is a different objective. A truncated implementation needs its tail interval exactly as in Section 4.

For full eventual profiles, the robust loss is strictly decreasing under every strict finitary improvement: its maximum term is nonincreasing and its rich-background term strictly decreases. Thus exact attained minimizers are undominated, with the same sufficient-policy conclusion when feasible. With a finite background, the argument proves strictness only for improvements detected by a positively weighted background coordinate; it does not prove strictness for the full process order. At fixed collection time, full rich background instead gives strictness for a strict improvement in that **fixed source experiment**: source-prefix Blackwell dominance is the relevant sufficient comparison. General eventual dominance need not compare finite-time losses at the chosen `t`.

For normalized losses, `|F_t(pi)-max_S d_(j,t)(pi)|<=epsilon`. Consequently an `eta`-optimal robust policy is at most `eta+2epsilon` suboptimal for the finite minimax audit. A sharper statement, useful when `epsilon<1`, is

\[
 \max_{j\in S}d_{j,t}(\pi)
 \le\inf_\rho\max_{j\in S}d_{j,t}(\rho)
       +\frac{\eta+\epsilon}{1-\epsilon},
\]

obtained by comparing with an approximately minimizing minimax policy and using the background difference at most one. Use the smaller bound, capped by the audit's range. These are worst-case tradeoff bounds, not evidence that a particular positive floor improves the minimax optimum.

### Dual-supporting weights do not certify every weighted minimizer

In the two-bit interface above, uniform target weights give

\[
 \tfrac12d_U(x)+\tfrac12d_V(x)=1/4
\]

for **every** `x`. These are optimal dual weights for the minimax problem because the weighted optimum equals its minimax value `1/4`. Nevertheless `x=0` and `x=1` are weighted minimizers with minimax error `1/2`; only `x=1/2` is minimax optimal. Strong duality says that a compatible primal/dual saddle pair exists and that every primal minimax optimum minimizes an optimal dual-supported weighted loss. It does not say every such weighted minimizer is primal minimax optimal. Retain the epigraph constraints, add a certified minimax tie-break, or certify the independent maximum at the selected weighted optimizer.

## 9. Safe target pruning and retained cuts

If target `T_i` can be simulated from `T_j` with deficiency at most `tau_ij`, triangle inequality gives, for every source experiment,

\[
 \delta(E,T_i)\le\delta(E,T_j)+\tau_{ij}.
\]

This remains true for eventual source losses by taking source-time infima. A prefix target is exactly simulated from its continuation by projection, giving `tau=0`. The statement needs a common world-independent stochastic target decoder; an intuitive resemblance or a within-world coupling is insufficient.

If every dropped target maps to a retained one with `tau=0`, dropping them leaves the maximum unchanged. With `tau_i<=tau`, the original maximum lies between the retained maximum and retained maximum plus `tau`. Missing oracle coverage is not such a target-domination proof.

For weighted sums, even exact domination gives only an upper replacement:

\[
 w_i d_i(E)\le w_i[d_{r(i)}(E)+\tau_i].
\]

Moving `w_i` to `r(i)` generally increases the loss and changes the objective. Safe certification keeps the retained weighted terms as a lower bound and adds `sum_dropped w_i min(1,d_(r(i))+tau_i)` as an upper bound. When both directional target-simulation errors are at most `tau_i`, the two loss coordinates differ by at most `tau_i`, so aggregating the weights changes the full objective uniformly by at most `sum w_i tau_i`. Exact mutual simulation allows exact aggregation. A transferred optimizer has at most twice that uniform error in regret, as in Section 6.

The frozen decomposition prototype gives a different reusable object: a **global affine lower cut for one unchanged target**. For finite worlds, let `p_theta(h)` be the controlled-prefix behavior mass and `x_h>=0` the terminal policy realization weight. Then the acquired law is `E_theta,h=p_theta(h)x_h`. A feasible target-decoder dual witness consists of `alpha_theta>=0`, `sum alpha=1`, and `0<=b_theta,y<=alpha_theta`. It yields

\[
 d_j(x)\ge \langle T_j,b\rangle-
 \sum_h x_h\max_y\sum_\theta p_\theta(h)b_{\theta,y}.
\]

This follows from the finite decoder LP dual, first minimizing separately over each decoder row and then factoring the nonnegative `x_h` out of its maximum. Include **every syntactic terminal history**, even those with zero mass under the incumbent. The resulting cut remains valid for every feasible policy and every new nonnegative weight vector under unchanged geometry and target. A change of target kernel, class/interface, horizon, source-variable basis, or dependency semantics requires revalidation or a proved transformation, not just matching a display name.

Changing objective weights preserves individual cuts and feasible per-target decoder witnesses. It does not preserve the aggregate master optimum or its lower-bound witness automatically. Rebuild and certify the new weighted master; replay/rescore a feasible policy and its per-target bounds; carry omitted mass separately. This gives a rigorous route to warm starts without pretending that a previous optimum certificate solved the new problem. The inspected prototype's README supplies the dual derivation and saved numerical validation; the present note neither reruns those certificates nor proves a new numerical speed result.

## 10. A conditional finite convergence theorem

There is a useful finite theorem under explicit oracle assumptions. It does not solve the infinite eventual problem.

Fix finite worlds, finite collection time, and a finite selected target library `S` of size `K`. Let `X` be the compact convex polytope of complete policy realization weights. All policies retain their full action–observation histories. Each target loss `d_j(x)` is convex and continuous on `X`: the finite dual representation above makes it a maximum of finitely many affine functions after restricting to dual vertices, or equivalently gives a finite polyhedral epigraph. The full-history factorization is essential; do not presume the same property for arbitrary parameterized neural policies or for a record that forgets relevant history. Weighted sums of these losses are convex. A countable normalized background is also convex and continuous on this fixed finite source polytope by uniform convergence, although evaluating it still requires an oracle or a certified tail treatment.

At round `r`, let the adversary choose `v_r` on `S`, and let the learner return `x_r` with certified best-response error `gamma_r`:

\[
 f_{v_r}(x_r)\le\inf_{x\in X}f_{v_r}(x)+\gamma_r,\qquad
 f_v(x)=(1-\epsilon)\sum_{j\in S}v_jd_j(x)+\epsilon L_b(x).
\]

Start the adversary uniformly and update

\[
 v_{r+1,j}\propto v_{r,j}\exp(\eta d_j(x_r)),\qquad 0<\eta\le1.
\]

Assume exact target losses for this first statement. For `R` rounds, write `x_bar=R^-1 sum_r x_r`.

**Proposition 8 (finite robust convergence, paper proof).** The averaged realization plan satisfies

\[
 F(x_{\rm bar})-\min_{x\in X}F(x)
 \le (1-\epsilon)\left(\frac{\log K}{\eta R}+\eta\right)
       +\frac1R\sum_{r=1}^R\gamma_r,
\]

where `F(x)=max_v f_v(x)`. The guarantee concerns the averaged realization plan, not necessarily the last policy iterate or the average of conditional action probabilities.

**Proof.** Let unnormalized adversary weights start at one. For `0<=z<=1` and `0<eta<=1`, `exp(eta z)<=1+eta z+eta^2`; hence each potential increment obeys

`log(W_(r+1)/W_r) <= eta <v_r,d(x_r)> + eta^2`.

For each target `j`, the final total potential is at least `exp(eta sum_r d_j(x_r))`. Since `W_1=K`, summing and dividing gives

\[
 \max_j\frac1R\sum_r d_j(x_r)
 \le\frac1R\sum_r\langle v_r,d(x_r)\rangle
       +\frac{\log K}{\eta R}+\eta.
\]

Convexity bounds each loss at `x_bar` by its average, including the background. Thus `F(x_bar)` is at most the mean round payoff plus `(1-epsilon)` times the displayed adversary regret. For any minimizer `x*` of `F`, the learner inequality gives `f_(v_r)(x_r)<=f_(v_r)(x*)+gamma_r<=F(x*)+gamma_r`. Sum over rounds. ∎

For `K=1` the adversary error is actually zero, and its update is unnecessary. For `K>1`, choosing `eta=min(1,sqrt(log K/R))` gives a vanishing bound as `R` grows, provided the mean learner error vanishes. If certified target estimates differ from true losses by at most `zeta_r` in every coordinate, use estimates clipped to `[0,1]`; the true adversary regret adds at most `2 mean(zeta_r)`, multiplied by `1-epsilon`. If only intervals are known, this error is explicit. Missing targets or a stale aggregate certificate are not bounded estimation errors unless separately certified. A selected-tail error can be included in `gamma_r` using Proposition 4, but a fixed omitted mass then leaves a nonvanishing error floor.

Averaging realization plans is feasible because the flow constraints are linear. Convert the averaged plan to conditional action rows by the usual ratios, with any valid action distribution at zero-weight histories. A naive rowwise average of the policies generally does not produce that averaged realization plan. No hidden world-dependent selection of a policy mixture is allowed.

An alternative algorithm is certified target generation: solve a restricted minimax master, query a hardest-target oracle over the full declared finite library, and append any violating target. A valid lower master bound plus an upper bound on the **global** hardest-target error certifies the full minimax gap. Exhaustive enumeration provides a finite oracle in principle; this note provides no efficient general oracle. Approximate separation gives a bound only when its upper error certificate covers all omitted targets. Finding one hard target gives a lower bound on the maximum, not an upper bound.

### A concrete dual route to a hardest-target oracle

There is a legitimate backward dynamic program inside the hardest-target problem, but it does not by itself solve the outer optimization. Fix a finite nonempty world class, a finite source alphabet `X`, a valid source experiment `E`, and one target depth `n`. Use the **same complete output alphabet** `Y=(A x O)^n` for every target policy, retaining actions as well as observations. Let `Sigma_n` include all randomized full-history target policies through depth `n`. Define the finite decoder dual domain

\[
 \mathcal D=\{(\alpha,b):\alpha_\theta\ge0,\quad
 \sum_\theta\alpha_\theta=1,\quad
 0\le b_{\theta,y}\le\alpha_\theta\}.
\]

The finite decoder dual formula from Section 9 gives the exact identity

\[
 \begin{aligned}
 \max_{\sigma\in\Sigma_n}\delta(E,T_\sigma)
 &=\max_{(\alpha,b)\in\mathcal D}
   \left[\max_{\sigma\in\Sigma_n}\langle T_\sigma,b\rangle
      -\sum_{x\in X}\max_{y\in Y}
           \sum_\theta E_{\theta,x}b_{\theta,y}\right].
 \end{aligned}
\]

**Proof.** Substitute the exact dual maximum for each target's deficiency. Both optimizations are maxima over independent compact finite-dimensional domains, with continuous joint payoff, so their order can be exchanged. This exchanges **two maxima**, not a policy maximum with the decoder primal minimum. All policies and dual witnesses remain world independent; summing known candidate-model coefficients does not reveal the actual world. ∎

For fixed `(alpha,b)`, the inner target problem has an explicit solution. Write the target law as `T_(theta,y)=p_theta(y) z_sigma(y)`, where `p_theta(y)` is the known controlled-prefix behavior mass and `z_sigma(y)` is the product of the target policy's action probabilities along the complete trace `y`. Form terminal coefficients

\[
 c_b(y)=\sum_\theta p_\theta(y)b_{\theta,y}.
\]

Then `H(b)=max_sigma <T_sigma,b>` is the maximum of the linear function `sum_y c_b(y) z_sigma(y)` on the target realization-flow polytope. Equivalently, define the backward recursion on full syntactic histories by

\[
 V_b(y)=c_b(y)\quad(|y|=n),\qquad
 V_b(h)=\max_{a\in A}\sum_{o\in O}V_b(h\mathbin{\Vert}(a,o))
       \quad(|h|<n).
\]

Its root value is `H(b)`. At each history choose one maximizing action to obtain a deterministic target policy attaining it; arbitrary ties and null histories do not affect validity. This recursion sums observation branches without inserting an extra transition factor because their full controlled-history probabilities already occur in the terminal coefficients. Inserting those transition factors a second time would compute the wrong value. A restriction on allowable target policies, a memory restriction, or a compressed target record requires a fresh realization/recursion argument.

The recursion avoids enumerating every deterministic contingent tree. Nevertheless, it explicitly handles `|Y|=(|A||O|)^n` terminal histories and `M_n=sum_(r<n)(|A||O|)^r` internal histories. Given their model masses, forming coefficients takes `O(|Theta||Y|)` arithmetic operations and the recursion takes `O(|A||O| M_n)`; naive source-penalty evaluation takes `O(|X||Y||Theta|)`. The dual array itself has `|Theta||Y|` coordinates. These are counts in the explicit full-history representation, with no claim about bit complexity, compressed model access, or polynomial dependence on horizon. No tree scan or implementation of this oracle was executed for this note.

The remaining outer problem is

\[
 \max_{(\alpha,b)\in\mathcal D}\,[H(b)-C_E(b)],\qquad
 C_E(b)=\sum_x\max_y\sum_\theta E_{\theta,x}b_{\theta,y}.
\]

Both `H` and `C_E` are convex piecewise-linear functions of `b`: `H` is a support function of the attainable target experiments, and `C_E` is a sum of maxima of linear functions. Their difference is not generally concave, so this is not automatically a tractable concave maximization merely because its two blocks have exact oracles.

A literal native example confirms nonconcavity. Let two worlds carry a hidden bit `theta`, and let either of two first actions `a` and `a'` reveal that bit. Use the empty source experiment and the four-symbol target alphabet `(action,bit)`. Fix `alpha=(1/2,1/2)`. Let `b^a_(theta,(a,theta))=1/2`, with all other entries zero, and define `b^(a')` analogously. At either endpoint `H=1` and `C_E=1/2`, so the difference is `1/2`. At their midpoint, every correctly matched entry is `1/4`; every target policy gives `H=1/2`, while `C_E=1/4`. The difference is therefore `1/4`, less than the average endpoint value `1/2`. Thus even this one-step native case violates concavity. This is an analytical counterexample, not a complexity lower bound.

Alternating an exact fixed-target decoder-dual optimization with the fixed-dual target dynamic program therefore produces a feasible target/dual pair and its **lower bound** on the global hardest-target value. Exact updates can make that bound nondecreasing, but neither monotonicity nor blockwise stationarity supplies a global upper certificate. A certified global optimization method for this piecewise-linear difference, a special structure collapsing it to a tractable problem, or a separate global upper bound is still needed for a trustworthy hardest-target oracle. The dynamic program is a concrete avenue for generating difficult targets cheaply relative to enumerating every contingent policy; it does not establish a polynomial global oracle or replace the independent audit. The existing depth-four and depth-five tree counts remain relevant to exhaustive validation, even though one fixed-dual target update need not enumerate those trees.

## 11. What the research can and cannot establish next

The strongest defensible next claim is a **conditional computational program**: retain valid per-target cuts; adapt a declared finite emphasis distribution; preserve an explicitly enumerated positive rich background in the mathematical objective; report selected-tail and optimization intervals; and compare the resulting policies on a prespecified independent finite audit. The backend can be useful even when fixed information or Brier policies win that audit.

The following gaps remain separate:

- An executable target encoding is not a computable deficiency evaluator for arbitrary world classes. Even finite model input can make exact rational targets and decoder LPs enormous.
- A positive rich floor preserves exact order sensitivity, but an `epsilon` tail can swamp the tiny weighted improvement associated with a difficult coordinate.
- Vanishing finite solver gaps do not imply vanishing eventual regret without finite-to-eventual control; vanishing eventual regret does not give one common acquisition deadline.
- Finite convex-oracle guarantees do not prove convergence for arbitrary moving weights, neural policy updates, last iterates, or an online collector executing changing policies.
- A full-rich robust objective has the desired strictness, but a finitely implemented approximation inherits that conclusion only to its stated error. No finite selected library is silently promoted to the rich order representation.
- Dual weight selection can leave scientifically important ties. Test the chosen policy's audit and, where feasible, the favorable and unfavorable objective-optimal faces.
- No numerical advantage, new formal support, or new manuscript theorem is established by this note. Its proofs and counterexamples are ready for independent review and possible later Lean formalization under separate authorization.
