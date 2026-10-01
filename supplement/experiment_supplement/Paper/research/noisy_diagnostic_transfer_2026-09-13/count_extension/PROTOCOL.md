# Full repeat-count transfer: fixed-collector extension

Frozen protocol, 13 September 2026, before production certificate runs. This extends the parent noisy diagnostic study without rerunning its objective optimization or changing its collectors, world class, acquisition interface, targets, weights, priors or tolerances.

## Research question

Does retaining the full information in a three-reading diagnostic materially tighten transfer guarantees relative to its majority bit, after retaining the same finite acquisition minimum and objective regret? The primary comparison changes only the diagnostic representation used in a transfer proof. It does not change the native-repeat objective: that objective already scores the full LLL and RRR records.

A count diagnostic is the number of ones among three independent readings of a bit, taking values 0,1,2,3. Its law is Binomial(3,e) if the bit is zero and Binomial(3,1-e) if it is one. Count is Blackwell equivalent to the full ordered record: the reverse decoder samples uniformly among records with that count. Majority is the garbling count>=2 and may discard useful confidence.

## Fixed certificate grid and controls

Use both diagnostic representations, `majority3` and `count3`, for all three existing noise pairs (.1,.1), (.25,.25), (.1,.3). Requested targets are LR, LLL, RRR, LLR, LRR, and the parent's adaptive_L. Design losses are 0,.001,.01,.05,.1, matching the parent certificate grid. This gives 180 production certificates: 90 per representation. Every certificate is valid at all actual loss values; a design loss only chooses the affine bound optimized during search.

The discrepancy cost for each source is one half of each diagnostic's deficiency. Search over a common repair decoder D and nonnegative intercept b and slope k for a pointwise inequality TV(pD,T_theta)<=b+k*[TV(p_L,B_L_theta)+TV(p_R,B_R_theta)]/2 for all joint diagnostic-output laws p and worlds theta. Handle diagnostic-output dependence; do not assume separately decoded marginals are independent.

Use a finite event-dual formulation instead of enumerating all marginal-sign-cell vertices. For each target event S, introduce bounded marginal potentials u,v with absolute values at most k/4 and t satisfying t+u_i+v_j>=D(ij,S). Require t+B_L_theta·u+B_R_theta·v-T_theta(S)<=b. Verify the equivalent robust support-function statement independently before production. Retain every target event, including empty and full events, or prove any exact reduction explicitly.

Search may use float64 LPs. Reconstruct rational stochastic D and nonnegative k, clip rational u,v to their permitted intervals, set t to the exact largest required residual, and increase b to the exact largest event/world bound. Store all witnesses and verify every inequality using rational arithmetic. This certifies feasibility of the affine bound, not search optimality or the true worst source or feasible-policy error.

Controls: independently verify full-count/full-record equivalence and majority garbling; compare new majority optimal values to the parent's binary vertex formulation and analytic zero-loss formulas where available; compare event-dual values against independently assembled primal support problems; confirm that a majority certificate lifts to counts. Mathematically, optimizing over count decoders can do no worse than optimizing over majority decoders at the same design loss. Numerical violations beyond recorded tolerance require investigation, not removal of cases.

## Comparison on existing collectors

Reuse all 984 parent returned collectors, all 54 optima and 930 purpose envelopes, and their audited full-record target deficiencies. Apply each new certificate using an upper bound on the two count deficiencies supplied by the exact equivalence to LLL/RRR; majority uses the corresponding garbling inequality.

For the repeat weighted loss S, mean count deficiency is at most S/.2. For the six-target minimax loss Dmax, it is at most Dmax. At an objective tolerance eta, keep the actual budget-dependent minimum S* or Dmax*, just as in the parent. Compare both diagnostics at exactly the same substituted loss. Do not claim that a lower zero-loss residual alone improves the finite-budget guarantee.

For the primary whole-near-optimal-set comparisons, use all original native_repeats and native_minimax grid entries, including the repeat objective's absolute-gap controls. This gives 42 distinct noise/horizon/objective/tolerance cases and 252 target-bound comparisons, of which 126 concern the three omitted targets. Preserve the parent's common numerical cost-sublevel enlargement (5e-8), optimum bracket, raw regret, and interpretation of pooled lower witnesses. Apply the new upper bounds conservatively to that same sublevel. Other objective collectors remain diagnostics; their posterior objective regret is not converted into native diagnostic loss without a proved bound.

Report separately: count versus majority affine guarantees; improvement over the best parent certificate including all triangle/reconstruction baselines; tightness relative to existing pooled lower witnesses; intercept and slope changes; runtime and formulation size. The count and majority certificate portfolios use the same fixed design grid. If a numerically reconstructed count certificate is weaker by a rounding residual, retain the valid lifted majority certificate as a baseline rather than asserting false numerical monotonicity.

## Success and scope

A positive result requires nontrivial improvement on omitted targets after budget and regret are included. A null result is useful if it shows that majority compression is not responsible for the observed gap under these constraints. No claim of practical learning, full eventual J_w calibration, universal reward superiority, or sharp policy-restricted target-error envelopes follows.

Save original source/output hashes, protocol and new-source hashes, exact and numerical checks, failed attempts, and comparisons in this new directory. Keep the parent's frozen protocol, production outputs, certificate files and completed report unchanged. Navigation may gain a pointer to this follow-up. Any substantive design amendment is a separate dated document. Do not alter the selected manuscript or Lean support based on this computational extension alone.
