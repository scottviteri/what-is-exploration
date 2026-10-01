# Alternate 22-class candidate: caption and evidence boundary

Standalone alternate presentation, 23 September 2026. Neither this figure nor its
caption has been inserted into the manuscript. [PDF](CANDIDATE_22_CLASSES.pdf),
[PNG](CANDIDATE_22_CLASSES.png), [data](figure22_data.csv),
[plotting/verification source](make_candidate22.py), and
[checks and complete source bindings](FIGURE22_CHECK.json).

**Which short collection objective preserves longer experimental capabilities?**
Each row supplies a class of candidate environment models with a common interface;
the actual model is unknown. A policy may choose each action from its complete
preceding action–observation record. It collects three such pairs. Information
gain and posterior Brier improvement concern the entire world label, under a
uniform prior. The categorical count method maximizes the expected sum of
`1/sqrt(1 + N_previous(observation))`, using an add-one categorical observation
predictor. It counts raw observation labels, not physical states. The two finite
native methods minimize, respectively, the uniform mean and the maximum deficiency
over all 128 deterministic three-step target policies. Uniform actions are a
control, not an optimized intrinsic reward.

Holding each collector fixed, the evaluation is

\[
A_{3,4}(\pi)=\max_\sigma\min_G\max_{Q\in\mathcal Q}
\operatorname{TV}\bigl(K_{\pi,3}(Q)G,K_{\sigma,4}(Q)\bigr).
\]

Here `K` is the family of record distributions indexed by the candidate world.
The decoder `G` randomly transforms the collected record into a simulated target
record. It may depend on the target policy, but must be the same in every world.
Thus the direction is collected evidence to target evidence. The outer maximum
finds the target whose evidence is hardest to reproduce, and total variation
measures worst-world distributional mismatch. All 32,768 deterministic four-step
targets are evaluated; the finite-mixture argument covers randomized targets.
These four-step evaluations do not select the collector.

**(a)** Absolute four-step error for all 22 classes in the original manifest order:
ten earlier structured/recurring cases followed by twelve prespecified fresh
random classes. Q4 and Q8 label four- and eight-world classes; alpha labels the
Dirichlet concentration used to generate transition and observation rows. Draw
1/2 distinguish the two generated instances at each parameter setting. There are 131 available method/class entries out of 132. Intervals
extend from the smallest lower bound to the largest upper bound among all saved,
verified representatives of that objective. Symbols locate envelope midpoints for
display; a midpoint need not be the error of any returned policy. A dagger marks
an envelope wider than `2e-6`. Neither the intervals nor the repetitions describe
statistical uncertainty or the complete set of objective optima. The unavailable
uniform entry is explicitly labeled and is not assigned zero error.

**(b)** Brier error minus native error for each native method, using ordinary Brier
(filled circles) and a favorable 5% Brier control (open diamonds). Positive values
favor the native method. A favorable control minimizes the three-step worst-target
error subject to

`R(policy) >= R_max - 0.05 * (R_max - R_min) - 1e-10`.

The percentage refers to the achievable Brier reward range, not to the optimal
reward itself. Control selection uses the three-step targets only. These are saved
constrained-policy representatives, not all near-optimal policies or collectors
chosen using four-step performance. Difference intervals are
`[baseline_lower - native_upper, baseline_upper - native_lower]`, preserving both
representative envelopes. All 22 rows remain visible; five unavailable controls
are labeled, with both native comparisons missing on each such row.

Comparisons use a numerical separation threshold of `1e-6`; a numerical tie is not
proved equality. On the **same 17 cases** with a 5% Brier control, weighted native
has 14 wins / 2 numerical ties / 1 loss against ordinary Brier and 13 / 0 / 4
against the control. Minimax has 15 / 0 / 2 against both. Over all 22 ordinary-Brier
comparisons, the respective counts are 18 / 2 / 2 and 19 / 1 / 2. The full
[nominal-zero, 1%, and information-control table](../target_selection_followups_2026-09-23/FINAL_SUMMARY.md)
and [exact pairs/provenance](../target_selection_followups_2026-09-23/COMBINED_STATUS.json)
remain directly available. Coverage differences must not be interpreted as a
change caused solely by reward tolerance.

The delayed reversal, weighted representative sensitivity in the irreversible
case, missing uniform recovery, and five missing 5% controls are preserved. These
22 heterogeneous classes are not independent identically distributed replications
of a population claim. The figure evaluates supplied-model planning rather than
unknown-model learning. Native losses are deliberately aligned with the audit,
but optimize three-step targets while evaluation uses four-step targets. A lower
scalar audit does not establish experiment dominance or eventual sufficiency.
The separate 12-setting study's 144 same-time incomparability comparisons are
[supporting evidence](../jw_computational_tests_2026-09-23/quality_corrected/same_time_order/results/REPORT.md),
not new order comparisons for these 22 classes. The finite 128-target loss and
finite minimax objective are not eventual infinite-rich `J_w`; the other study's
planning timings and positive-background regret certificates do not apply here.

**Verification boundary.** Original and completion archives were checked by
reconstructing saved master certificates, hardest/revelation decoder witnesses,
and complete profile arithmetic. The old archive did not retain every per-target
decoder, so that check does not independently replay every old solve. Newly
recovered and 5% control evaluations retain and replay all 32,768 target witnesses.
All numerical bounds remain floating-point witness calculations, not exact
outward-rounded or statistical confidence intervals. This plotting pass verifies
frozen hashes, result/check and policy bindings, optimizer flags, coverage, saved
representative envelopes and interval arithmetic; it performs no new LP solve or
numerical witness replay. One failed uniform recovery and unavailable original
controls remain failures/missing evidence, regardless of the completed reporting
pass. The earlier [failed 16-target broad-benefit screen](../native_objective_benchmark_2026-09-15/README.md)
is not withdrawn by this different evaluation.
