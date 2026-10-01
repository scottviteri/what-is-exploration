# Handoff: adaptive native weights research

23 September 2026. Writing style, following Introduction Edits' authorized assignment and the lead author's instruction to continue with Ultra reasoning. **The bounded research and implementation-preparation phase is complete.** All writes are confined to `Paper/research/jw_adaptive_weights_2026-09-23/`. The current campaign, source owners, manuscript, ledgers, navigation and release are untouched by this pass. No new commit, push or export was made. No deferred computation will launch automatically.

## Recommendation and new results

Continue two separately evaluated tracks. Retained target cuts and cost-based weights may reduce the cost of approximating a declared member of the native-objective family. Hard-target weighting may improve a fixed worst-target audit. Positivity preserves an order property of each full eventual objective, but neither track inherits a finite empirical superiority claim from it.

THEORY.md supplies written proofs, with all new results labeled paper-only. It fixes a literal enumerable family of rational full-history native policies and a strictly positive normalized background. It derives selected-tail intervals, fresh final-weight optimization bounds, coordinate and dominating-improvement bounds, weight-perturbation bounds, and conditional convergence results. A fixed positive floor can give coordinate convergence even with oscillating emphasis weights when full eventual regret vanishes and zero is approachable. Increasing collection time also gives rate-free finite-to-eventual optimization convergence for a fixed feasible full-policy family, uniformly over TV-totally-bounded weight families; a fixed finite emphasis library is one such family. There is no computable finite-time rate or general moving-policy online guarantee.

The native counterexamples are substantive constraints: cooperative easy-target selection can choose policies with worse maximum deficiency, uniform optimal dual weights can leave non-minimax tied optimizers, and policy-table limits can lose sufficiency. A fixed-dual hardest-target update has an explicit backward recursion, now implemented for bounded exact examples. The remaining outer problem is demonstrably nonconcave, so alternating updates produce lower witnesses, not global upper certificates.

Existing relevant Lean declarations and ledger assumptions were read and identified in THEORY.md. They were not freshly built or extended. None of the new adaptive/convergence/oracle propositions is claimed as newly formalized.

## Completed artifacts

- `README.md`: recommendation, scope, artifact map and small-check commands.
- `THEORY.md`: definitions, proofs, explicit assumptions, counterexamples and open computational issues.
- `EVIDENCE.md` and `EVIDENCE_INPUTS.json`: fourteen hashed compact sources, reconstructed comparison counts, negative cases and partial-coverage limitations.
- `PROTOCOL.md`: separate backend and objective-quality studies with charged weight search, common model access/acquisition budgets, favorable information/Brier controls and independent confirmation.
- `adaptive_weights.py`: exact rational encoding, literal retained-action target-law compiler, positive-floor coefficients, omitted-mass accounting, immutable objective identity, target-specific cache and finite certificates.
- `weight_updates.py`: explicit tractability and hard-target update rules, plus realization averaging. Floating multiplicative updates remain numerically approximate.
- `target_oracle.py`: exact fixed-dual native-target recursion, with explicit expansion caps and no claim of global hardest-target optimization.
- `frozen_adapter.py` and `DEPENDENCIES.json`: prepared bridge using pinned frozen dependencies; fresh-process isolation; reused dual-witness reconstruction; fresh objective bounds; retained witness storage; late-evidence rejection. Numerical execution is disabled by default and has not been exercised.
- `dry_run.py`, `DRY_RUN.json`, `DRY_RUN_CHECK.json`: execution-disabled illustrative objectives and proposed future grid, with measured solver-free dry-run status.
- `check.py`, `CHECKS.json`: sixteen small checks and current source hashes. `CHECK_FIXTURE_FAILURE.json` retains the one failed development fixture, which introduced floating zero into an exact-rational example; the fixture was corrected, and the final checks pass.

Independent reasoning/evidence reviews were completed by two agents without local computational workers. Their reviews caught and led to fixes for kernel/geometry identity binding, metadata expansion limits, persisted witness requirements and deadline accounting. Cache identity alone is not treated as proof of its cuts.

## What passed and what did not run

The final check run passed **16 tests, zero failures/errors**, covering exact target laws, action retention, all-history affine cuts, kernel/geometry and cache identity, target reordering, stale aggregate-bound rejection, omitted mass without renormalization, coefficient transport, native tie/nonconcavity examples, weight rules, syntax and frozen-source hashes. It used 0.021899 seconds wall, 0.021999 seconds CPU and 23120 KiB current-process-image peak RSS. Tests enforce one-thread settings, a 256 MiB address-space cap, a ten-second wall cap and nine-second CPU soft cap. `/proc/self/status` supplies current-image high-water memory; the separately preserved lifetime `ru_maxrss` can include launcher history and is not attributed to these tests.

The dry-run generator used 0.300467 seconds wall, 0.046475 seconds CPU and 19236 KiB reported peak RSS, with no numeric backend imported. The evidence helper used .019603 seconds wall, .004518 seconds CPU and 16,948 KiB peak RSS. Small checks were rerun only after implementation, instrumentation or fixture changes. All new computational helpers were short, serial and within the assignment's per-helper limits and total sixty-second budget; there was no numerical worker, GPU use, solver invocation, dependency installation, training, exhaustive target scan, bulk certificate audit, full test suite, Lean build, PDF build or release gate.

These checks do **not** validate the new solver-backed bridge, empirical performance, numerical convergence of adaptive updates or future reward-face support. The saved prototype's sixteen checked configurations are prior evidence, not new validation of this bridge.

## Safe commands now

From the repository root:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 Paper/research/jw_adaptive_weights_2026-09-23/check.py
PYTHONDONTWRITEBYTECODE=1 python3 Paper/research/jw_adaptive_weights_2026-09-23/dry_run.py --output Paper/research/jw_adaptive_weights_2026-09-23/DRY_RUN.json
```

Both commands remain solver-free. There is deliberately no campaign or solver-launch CLI in this delivery. `load_backend(execution_authorized=False)` and `solve_reweighted(..., execution_authorized=False)` refuse numerical execution by default; changing those flags belongs to a later resource-authorized validation step, not this handoff. Do not import the bridge into the active campaign process: frozen legacy dependencies occupy generic module names, which the loader detects and rejects in an already populated process.

## Next execution stage, after separate resource allocation

First allocate an explicit noncompeting CPU/memory/time window and pin Python/NumPy/SciPy/HiGHS versions. Then validate the new bridge on the frozen sixteen-case finite grid, starting with the tiny cases. Match objective coefficients and feasible regions, reconstruct target laws and complete-history cuts, retain the original dual payloads, check the master cost-rounding correction, and independently replay bounds. Persist both `cache` and `witness_store` together with every master/decoder archive. The prepared bridge uses a conservative `1e-6` selected gap with `2e-7` target-interval padding, while the archived prototype used a `2e-7` aggregate gap; compare all new backends at one prespecified tolerance. New floating results are not exact/Lean certificates.

The bridge's underlying solver time limit is soft. It rejects oracle/master evidence that arrives after the declared endpoint, but a later harness must enforce the process wall cap and charge all validation, selection and export overhead. A successful solve after a budget is a late solve, not a retrospectively successful checkpoint.

Broader equivalence tests remain necessary for changing libraries, zero/tiny weights, target aliases and random native policies. The conversion from frozen deterministic trees to canonical full-history rational encodings still needs an implementation and independent check. The robust-background epigraph and reward-face constraints are not implemented in this bridge. Use a separately pinned, verified existing planner for favorable baseline controls or implement these constraints under a future assignment. The floating multiplicative update also needs a rounding-error budget before receiving the exact theorem's convergence guarantee.

Old measurements justify modest pilots, not a promised schedule: frozen full-library weighted solves took roughly 2.24 seconds at collection three and 9.71/17.93 seconds in two collection-four cases, while a small weighted case was slower than monolithic (.259 versus .163 seconds). Their memory limits were larger than this phase's tiny-helper limit. A forty-second future planner cap does not budget a full depth-four audit. Measure that audit separately before freezing a complete confirmation grid; never infer resource availability merely because the other supervisor's advertised end time has passed.

## Supplemental evidence received after preparation

The supplied [13:43 figure assessment](../target_selection_2026-09-23/interim_reports/2026-09-23_figure_assessment/README.md) has been incorporated through a short EVIDENCE.md supplement and a protocol clarification. Its missing near-optimal depth-four audits require a distinct evaluation extension, and failed decoder audits should reuse saved policies. No source analysis, figure, optimization or validation was duplicated. The original evidence snapshot remains intact; supplementary source hashes are recorded separately. Code and its sixteen-check record are unchanged.

The later [optimum-selection finding](../target_selection_2026-09-23/interim_reports/2026-09-23_optimum_selection/README.md) is also incorporated. Backend equivalence now explicitly compares certified objective bounds separately from the warm start's selected policy and held-out performance. The protocol records future selection provenance and proposes training-only secondary controls for native objectives, charging the first-stage gap. These controls remain unimplemented; registered representatives and code are unchanged.

## Scientific choices for discussion

No unanswered question blocks this completed phase. PROTOCOL.md supplies explicit defaults so discussion can be concrete: prioritize tractability and capability as separate endpoints; use epsilon=1/20 initially; compare 2/10/40-second native budgets with strong posterior baselines; and use new confirmation classes after feasibility and seed-nonoverlap checks. The remaining choices are how much future compute to allocate, whether the next phase should prioritize backend certification or independent capability quality, and whether to authorize Lean integration of selected new propositions. None is silently decided by a favorable archived case.

All already-inspected depth-four outcomes are exploratory for this design. Preserve the failed 16-target Brier screen, the nonmonotone weighted target-count curve, the delayed-depth ranking reversal, favorable Brier ties and missing/failed-case counts. A negative new study is a valid result.
