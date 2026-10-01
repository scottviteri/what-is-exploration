# Exact formal support and its numerical boundary

`Formal/Formal/EmpiricalEndingCertificates.lean` proves that rational probability tables, a stochastic decoder and a valid bounded decision-loss witness supply upper and lower bounds on the real decoder infimum. It permits every real stochastic decoder, not just rational decoders or those tried by the optimizer. The lower certificate uses the repository's proved finite dual bound.

`Formal/Formal/EmpiricalEndingDelayed.lean` checks concrete rational tables and certificates for the original delayed case with parameters 0.25 and 0.1. The weighted-native reference is the lexically first saved cell, `cell_0014`; Brier is `cell_0208`. The reference was not chosen for its directed deficiency. Both probability tables are reconstructed by exact rational hidden-state filtering after quantizing policy probabilities to millionths. The physical transition and observation rows are rationalized and normalized. Empty record columns are removed. `exact_diagnostic.py` retains the full rational model and policies in `EXACT_DIAGNOSTIC.json`.

For these **explicit rational finite experiments**, Lean proves:

- Native record to Brier record deficiency lies in `[0.0878, 0.0879]`.
- Brier record to native record deficiency lies in `[0.0276, 0.0277]`.
- Both are strictly positive, so the finite experiments are incomparable.

This is an adverse native case on the original worst-depth-four score, and is retained deliberately. The exact proof explains why a scalar audit loss need not imply experiment dominance. It does not formally verify the complete depth-four audit, an objective optimum, eventual behavior, or all representatives.

The rational reconstruction's largest observed row-TV difference from its archived native experiment is `3.5196e-7` (rounded upward here); the Brier difference is below `7e-18`. These proximity checks are numerical. Lean verifies the explicit rational experiment tables and their certificates; the Python physical-model construction and archive bindings are a separate, inspectable calculation. In particular, the theorem is not silently asserted for the original floating-point policy or every optimizer.

All three isolated modules compile, and the full `lake build` passed. `LEAN_AXIOMS.txt` records only the standard `propext`, `Classical.choice`, and `Quot.sound` axioms; no `sorryAx` or native-computation axiom occurs. Rational checks use `decide +kernel`.

The first shared paper-support audit reported new and concurrent research modules as unclassified; that failed attempt is preserved. Concurrent integration subsequently classified all three modules as supporting research and imported them into the root build. The final paper-support/axiom audit passes. This pass did not edit the shared module map, root imports or ledger. The classification explicitly supplies no selected manuscript claim and does not broaden the exact-table scope.

## Stronger archived-table check

`Formal/Formal/EmpiricalEndingSaved.lean` additionally proves the tighter intervals `[0.08782201, 0.08782202]` and `[0.02766393, 0.02766394]` directly for the archived experiment matrices after exact rational row normalization and removal of globally zero columns. This version does **not** round the policy probabilities to millionths. Each binary64 matrix entry is interpreted as its exact rational value, then the row is normalized. The largest half-l1 correction is exactly `3181/73786976294838206464` for the native matrix and `9/288230376151711744` for Brier, each below `5e-17`. The decoder and dual witness may still be rounded: their rational feasibility and the resulting bounds are checked exactly.

`EXACT_SAVED_DIAGNOSTIC.json`, `exact_saved_diagnostic.py`, and `LEAN_SAVED_AXIOMS.txt` record this stronger calculation. Lean proves the inequalities for those exact finite probability tables; archive-file parsing and the correspondence between those matrices and the physical policy/model execution remain external bindings. Neither normalized floating-point matrices nor quantized policies are silently treated as a Lean formalization of the whole hidden-state simulator. The original rational physical replay is preserved as a separate check. All three modules are now classified as supporting research. FORMAL_CLASSIFICATION_SNAPSHOT.json records the scoped entries read at final validation.
