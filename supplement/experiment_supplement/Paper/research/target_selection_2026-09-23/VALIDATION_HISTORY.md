# Prelaunch numerical validation history

The first bounded validation attempt passed literal target laws, DP/LP values,
prefix/mixture reduction, and ordinary reward-face feasibility, then failed in
the forced severe-infeasibility repair stress test. Its nearly-unit mixture left
extremely small source probabilities; decoder stationarity residuals reached
2.09e-7, 2.38e-7 and 4.27e-6 across retained/cold/alternate attempts, exceeding the
unchanged 2e-7 acceptance threshold. No campaign had been launched.

The repair now rounds its mixing probability upward to a grid of width 1e-8.
This maintains reward feasibility and changes the policy by at most 1e-8 from
the calculated mixture. A nearly-unit mixture becomes the exact feasible
DP policy. The final policy is independently re-audited, and the original LP
lower bound is retained. No solver tolerance or data exclusion was changed.
The pre-fix source is retained as validation_before_repair_rounding.py.snapshot.

A second attempt exposed the same conditioning issue even in an ordinary
reward-face solution, with stationarity as large as .00116. Its exact log is
preserved in validation_near_unit_failure.log. The nearly-unit rounding is not
claimed to solve source conditioning generally.

The numerical wrapper now merges tiny source columns into an existing large
column under a 1e-8 worldwise mass budget. This is only an internal garbling;
original model, policy, and record probabilities remain unchanged. A lifted
decoder and a feasible dual are re-evaluated on the original source, and the
original 2e-7 bracket tolerance still applies. No coarse-only value is accepted
as an exact value of the original experiment.

The post-pilot replay checker initially compared action probabilities at every
syntactic history, including histories unreachable under the saved policy. The
replay routine fills those rows uniformly, so this overstrict check failed by
0.5 despite equal realization weights and acquired experiments. The failed
checker log remains `pilot_review_null_prefix_checker.log`. The corrected check
compares causal realization weights and acquired experiments, and separately
checks all saved action rows for stochasticity. It passed alongside all 20
reconstructed master certificates and the original-source witnesses. This was a
review-check correction; it changed no pilot policies, objectives or solver data.

Before the main launch, original-source validity checks were added ahead of
zero/tiny-column handling. Final validation rejects malformed, negative, NaN,
infinite and unnormalized original matrices, and brackets three analytically
known binary examples after coarsening. All 281 bounded implementation checks
and 644 saved-pilot replay checks passed at the original tolerances.
