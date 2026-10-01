# Post-design scalar reward diagnostic

This diagnostic was specified after the planning design, while the corrected
primary native audits were still running. It is not a new primary metric,
selection criterion, optimizer, checkpoint rule, or confirmation experiment.
Its formulas are tested only on analytic examples before the primary summary
finishes. Confirmation aggregates are generated only from a completed, unchanged
primary summary, retaining every expected endpoint and all missingness.

For a saved acquired experiment `E[q,x]`, use the uniform prior on its `Q` worlds.
Let `m[x] = sum_q E[q,x]/Q` and, where `m[x]>0`,
`p[q|x] = E[q,x]/(Q*m[x])`. Compute directly:

- World information in bits: `sum_qx E[q,x]/Q * log2(E[q,x]/m[x])`, with zero
  summands omitted. This is `I(world;record)`, not predictive surprisal.
- Posterior categorical Brier improvement: `sum_x m[x]*sum_q p[q|x]^2 - 1/Q`.
  The categorical squared loss is the sum of squared prediction errors against
  the one-hot world label. Its prior loss is `1-1/Q`.

Read the already computed finite-horizon DP maxima from the validated baseline
records. Read minima and attainable ranges from the validated reward-face
metadata, and crosscheck their maxima against the baseline. No optimization or
new model inference is performed. Report raw regret `maximum - actual`, along
with regret divided by the attainable range when that range exceeds the numerical tolerance `2e-7`. Preserve
small negative floating-point residuals in the CSV; plotting can clip values
within `2e-7` of zero. Scores are ordinary floating-point diagnostic values, not
outward-rounded certificates.

For each endpoint, rehash the primary summary's frozen inputs, require its
per-run policy check to have passed, and independently replay the physical-model
policy law before scoring the saved `E`. Preserve the native-audit interval,
original timing and eligibility, including missing, late and rejected evidence.
An available policy may have a scalar diagnostic despite a missing held-out
audit; this never makes that endpoint eligible for a native comparison. Baseline
policy reuse across 2/10/40-second analysis rows remains explicit.

All methods and every expected endpoint are included uniformly. The optional
plot displays every class for the three 40-second primary weighted methods
(fixed, cost-adaptive and hard-target); missing class markers remain visible.
The report also preserves the finite-library minimax, baseline, reward-face and
secondary-average rows. Twelve parameter settings share two seed families;
checkpoint and target repetitions are not independent samples. No significance
or population-level claim is made.

Information and Brier can expose scalar tradeoffs. A scalar win does not prove
Blackwell dominance, the strict native process order, complete exploration,
eventual sufficiency, or practical optimization of the full countable native
score. Data processing constrains a known garbling; these diagnostics do not
establish such a garbling from reward values.

Run after the completed primary summary exists:

```
python quality_corrected/reward_diagnostics/diagnose.py \
  --summary quality_corrected/summary/summary.json
```

`--self-test` exercises only analytic experiment matrices and a synthetic causal
model; it reads no confirmation results and launches no solver.
