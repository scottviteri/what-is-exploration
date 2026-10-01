# Uniform decoder shortcut and completed recovery — 24 September 2026

the lead author authorized this fix after the Commission 06 review. The known-decoder
wrapper verifies identity/prefix projections before creating the general LP
backend. It only skips optimization when the original 2e-7 two-sided bracket
closes. Eight bounded tests passed, including rejection/fallback controls. It does
not change policy selection, deficiency, reporting thresholds or solver limits.

**All four historical uniform audit failures are recovered in this separate
package. Combined coverage is 396/396 cells and 2,376 reference comparisons.**
The original campaign remains 392 passed plus four preserved timeout records.
The four uniform self-reference checks now use explicit prefix deletion, with
errors below 1.25e-16 and no solver. Their previously completed twelve witnesses
are copied byte-for-byte and independently rechecked. The remaining eight
native-reference audits used the unchanged 60-second RecoveryDecoder fallback;
all passed. Every recovered cell then passed the original full six-reference
physical/reward/decoder checker. No collector was replanned or retrained.

The entire correction run took about 53.37 seconds on one low-priority CPU thread.
These descriptive timings are from a shared machine, not a benchmark speedup.
The old own-reference calls individually timed out after about 60 seconds.
The new uniform collectors still miss other references: recovery removes missing
checks, not substantive deficiencies. All four newly complete cells fail the
all-six-reference .05 threshold, and therefore also .02 and .01. Do not turn an
own-reference shortcut into an assertion of complete exploration.

## Integration handoff

Use `INTEGRATION.json`: its four records match the current integration compiler's
record shape, use repository-relative source paths, and include result/CHECK
hashes. Append these records to the 392 accepted originals. Preserve the original
four failures as historical attempts, not four remaining missing cells. The
merged `comparisons_with_recovery.csv` has 2,376 unique directional rows; the
original `budget_campaign/comparisons.csv` is untouched. The JSON gives updated
uniform threshold counts with denominator 22 at all three budgets.

`SUMMARY.json` and `INPUT_BINDINGS.json` are the executed runner's provenance;
their path strings are relative to `Paper/`. `INTEGRATION.json` instead explicitly
uses the repository root for its paths. Do not mix those bases. The code and
inputs are SHA-bound in `SOURCES.json` and `INPUT_BINDINGS.json`; result and CHECK
files bind the numerical witnesses. The final check rehashed all 4,735 entries
across the original compact and local-evidence inventories: none changed.

Compatibility findings and all other primary cells are unchanged. Commission 06
remains the original review of the pre-recovery checkpoint; this is its new
correction handoff, not a rewrite of that review or of frozen evidence. No shared
manuscript/ledger edits or Git action occurred here. Research outputs stay local
under the lead author's publication-size preference.

## Reuse

`known_decoder.py` exposes `KnownDecoderFirst(E, outputs, fallback_factory)`.
Call `solve(F, source_to_target=...)` with a documented map from every original
source-column index to a target-column index. For the full binary action/observation
histories here, a length-t to length-3 prefix map is
`np.arange(4**t) // 4**(t-3)`. The class verifies the resulting decoder on E and F;
it never infers success merely from matching dimensions. Identity is also tested
when signal cardinalities agree. General decoder construction is lazy and reused.
The frozen campaign implementation is preserved; this wrapper is the corrected
entry point used by the recovery runner and can be adopted by future campaigns.

A decoder that merely meets .02 while having a larger unknown optimum gap does
not bypass the exact-bracket checker. A future threshold-only mode would need its
own explicit output scope; it was unnecessary to repair these four failures.

## Recovered values

| Original cell | Prefix upper error | Prefix audit seconds | Worst of six reference errors (upper) |
|---|---:|---:|---:|
| `expanded_h4__case_05__uniform` | 6.7029e-17 | 0.0027564 | 0.0916986298 |
| `expanded_h5__case_05__uniform` | 9.6702e-17 | 0.0068175 | 0.05825432763 |
| `expanded_h5__case_10__uniform` | 7.2657e-17 | 0.0065935 | 0.1796328989 |
| `expanded_h5__case_11__uniform` | 1.242e-16 | 0.0065289 | 0.1602768963 |
