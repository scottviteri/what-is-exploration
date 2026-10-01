# Weight sensitivity of fixed records

15 September 2026. the lead author asked how rankings depend on target weights and whether
weights increasing in the Blackwell order resolve that dependence. This is an
exploratory follow-up; the frozen benchmark and its outcomes stay unchanged.

Interpret increasing weights as T_i Blackwell-dominates T_j implies w_i >= w_j.
This is a constraint on target priorities, distinct from source monotonicity of
the weighted deficiency loss, which already holds for all nonnegative weights.

For each of the ten saved environments:

1. Hold the saved native-weighted and Brier objective-optimum records fixed.
2. Independently evaluate all 16 target deficiencies for both records.
3. Compute every directed target-to-target deficiency to identify the finite
   target order numerically; include equality constraints for equivalent targets.
4. Minimize and maximize the difference L_w(native record) - L_w(Brier record)
   over weights summing to one, with w_j >= .01/16 and the order constraints.
   The floor reserves one percent of total weight as a uniform component.
5. Save matrices, extremizing weights, and LP certificates. Check threshold
   stability of the numerical order at 1e-9, 1e-8 and 1e-7.

This measures evaluation sensitivity of fixed evidence. It does not reoptimize
collectors, measure downstream accuracy changes, or test a single new weighting
rule across environments. Extremizing weights can differ between cases. Report
numerical scope separately from written general arguments and a small exact
native example. No stronger main-paper claim or new Lean result is introduced.
