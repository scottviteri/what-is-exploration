# Strengthening the empirical ending

This authorized research pass completes missing comparisons and derives new checks for the broader 22-class study. It does not edit the manuscript, commit, push, or export to Overleaf. Prior archives and failed attempts remain unchanged.

The [complete 22-class candidate at manuscript width](CANDIDATE_22_PAPER.pdf) displays all 132 method/class entries, the complete comparison with a minimax control using a 5%-Brier reward allowance, and actual Brier reward sacrifice. A [second candidate](CANDIDATE_22_MATCHED_PAPER.pdf) shows the new reward-matched comparison, which is less favorable to the weighted native objective. Both retain all 22 classes. [Definitions and caption](CAPTION.md), [matched caption](MATCHED_CAPTION.md), and [interpretation](ASSESSMENT.md) distinguish what these comparisons establish. The larger standalone versions remain available for close inspection.

## What is complete

- All 18 originally absent 1%/5% information/Brier controls have been optimized under the original frozen specifications and independently checked. The original registered near-optimal grid is now 88/88, including all five formerly missing Brier5 controls.
- The final uniform-action audit now covers all 32,768 targets. It reuses and rechecks the 28,928 previously saved witnesses, preserving the old timed-out attempt.
- All 19 repaired audits pass a fresh replay of every target decoder and bounded decision-loss witness: 622,592 target checks. Four deliberately corrupted certificates were rejected. The check is numerical float64 arithmetic, not outward-rounded interval arithmetic.
- Actual information/Brier reward and attainable reward ranges are derived for 427 saved policy instances, including all 88 near-optimal controls. Policy and model replay and two reward formulas agree.
- 176 directed finite-record deficiencies cover 88 pairs: weighted native and minimax against ordinary Brier and Brier5 on every class. Selection is fixed to the lexically first verified cell for each method/class, without using the new directed results. Eighty-four pairs have positive bounds in both directions; four are equivalent within numerical tolerance. This is not a statement about every optimizer or later collection.
- [Exact rational support](FORMAL_SCOPE.md) proves concrete bidirectional bounds for the adverse delayed example in Lean. In the stronger archived-table calculation, the two directed deficiencies lie in `[0.08782201, 0.08782202]` and `[0.02766393, 0.02766394]`. Lean checks exactly normalized rational tables and witnesses; archive parsing, physical replay, policy optimality and the complete depth-four audit are separate verification obligations.
- The matched pass is complete: 22 independently checked planners and 44 complete audits, retaining and replaying all 1,441,792 target witnesses. The final result is [MATCHED_COMPARISON.json](MATCHED_COMPARISON.json). The queue and per-reference chain reports retain execution history.

## Completed original-grid outcomes

Positive means a smaller worst-depth-four error for the native method. Intervals include every saved native representative used by the original figure.

| Comparator | Weighted native: wins / ties / losses / mixed | Minimax: wins / ties / losses / mixed |
|---|---:|---:|
| Ordinary posterior Brier | 18 / 2 / 2 / 0 | 19 / 1 / 2 / 0 |
| Favorable 5%-Brier control | 16 / 0 / 6 / 0 | 18 / 1 / 2 / 1 |

The median class-wise audit reduction against Brier5 is about 0.00696 for weighted native and 0.01042 for minimax, using representative-envelope midpoints as descriptive summaries. Midpoints need not be attained, and the separately summarized audit and reward envelopes need not come from the same policy. Neither summary is a population estimate or an all-optima guarantee. The native policies often sacrifice substantially more Brier reward. These counts alone therefore do not establish a matched-reward advantage.

The completed controls preserve important adverse outcomes: weighted native loses to Brier5 in the delayed case, both irreversible cases, one earlier random class, and two fresh random classes. Minimax retains its delayed and sparse-eight-world losses, a tie, and a representative-dependent comparison. Nothing was removed because it favored a baseline.

## Reward matching

[MATCHED_PROTOCOL.md](MATCHED_PROTOCOL.md) fixes one native reference per class lexically, without selecting it by the new held-out scores. The control minimizes the worst training-target deficiency subject to achieving at least that reference's Brier reward, with the original explicit `1e-10` allowance. Selection remains at target depth three; evaluation is at depth four. This is a native minimax planner with a Brier constraint, not ordinary Brier optimization. [MATCHED_COMPARISON.json](MATCHED_COMPARISON.json) passes for all 22 cases; [REFERENCE_QUEUE.json](REFERENCE_QUEUE.json), `reference_chain_*.json`, and `matched_audit_queue.json` record the completed execution.

Weighted native has **6 wins, 1 numerical tie, and 15 losses** on the longer-target audit against this control. The median control-minus-native error is `−0.0030462851`; negative favors the control. All reward floors and training optimality checks pass. The control retains at least the reference's reward up to the explicit allowance; it is not required to have exactly equal reward. The fixed reference and its control are paired throughout this calculation.

The reference is feasible, so an exact constrained optimum cannot do worse on the **training** minimax criterion. Its longer-target result is not guaranteed by that fact. The finding favors the constrained finite maximum over this particular finite mean on most of these classes; it does not establish that ordinary Brier optimization wins, that every native weighting loses, or that eventual `J_w` fails. The separate [record-order diagnostic](MATCHED_ORDER.json) finds 21 pairs numerically incomparable and one equivalent within tolerance. A better worst-target scalar and retained reward usually do not yield dominance of the entire experiment.

Planning the 22 new controls took 49.70 summed worker-seconds (median 0.74, maximum 16.88). Their full audits took 3,255.58 summed seconds; the 22 reference audits took 4,056.60. These are recorded worker wall times under concurrent load, not elapsed campaign time, hardware-independent complexity, or equal-compute comparisons; reference acquisition and its original planning are additional costs. This is a post-design diagnostic on existing cases, not new-model generalization.

## Evidence and reuse

The old 16-target benchmark's failed broad-benefit screen remains in [its original record](../native_objective_benchmark_2026-09-15/README.md). The 22-class archive and all earlier follow-ups remain in their original directories. No rich-background finite-prefix bound, planning-time comparison, or seed-family statistic from the separate 12-setting study is imported into this cohort.

`completion_results/` contains the initial failed launch: the system Python lacked `highspy`. `completion_retry_results/` uses the pre-existing solver virtual environment with exactly the same frozen jobs and source. All eighteen retry jobs pass. This launch failure is operational, and is not reclassified as successful scientific output.

Bulk `control_audits/`, `matched_audits/`, and `reference_audits/` witnesses are local experiment artifacts. Sources, protocols, small reports, standalone figures, and the three `EmpiricalEnding*` Lean modules are the reviewable research package. This pass did not modify the shared formal ledger, module map or root imports. Concurrent integration has now classified all three modules as supporting research with no selected manuscript claim. The isolated proofs, full Lean build and final shared paper-support/axiom audit pass.

## Review and binding boundary

[Commission 03](MISSING_CITATIONS_CHECKS_REVIEW.md) reviewed the pre-completion snapshot at 00:12:37 UTC on 24 September. Its pending matched-result statements describe that boundary. Its nineteen stale checker bindings are repaired in [BINDING_REPAIR.json](BINDING_REPAIR.json): old reports are retained in `binding_history/`, and all scientific records, comparisons and directed jobs were checked unchanged. No optimization was repeated for this repair. The completed matched results and stronger archived-table Lean module are a later evidence boundary.
