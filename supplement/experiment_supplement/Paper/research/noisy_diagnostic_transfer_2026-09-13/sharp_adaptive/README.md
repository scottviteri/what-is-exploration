# The adaptive capability of exact repeat-objective optimizers

[Report](report.pdf) ([source](REPORT.md)) · [Proof note](theory/theory.pdf) · [Frozen protocol](PROTOCOL.md)

At H=4 and equal sensor errors .1, the six-diagnostic repeat objective has exact minimum **.0072**. Its optimal scored profiles are exactly `(0,0,0,0,t,.072−t)`, with every split attainable.

For the omitted adaptive target, an exact optimizer has deficiency **.072**. An all-policy rational certificate using full histories bounds every exact optimizer by **.072000002**. This is an enclosure of width at most two billionths, not an exact equality theorem. The count-only common decoder gives the weaker, independently checked bound .07384. The predecessor's general transfer upper was approximately .0790704.

The full-history certificate retains the actual native-objective constraints and all randomized history-dependent policies. A prediction-optimal superset fails: it contains a policy with adaptive deficiency at least .1224 and native loss .01368. The exact scored profile also does not identify a canonical experiment; the proof note gives an optimal policy that cannot simulate any recorded mixture of the simple three-plus-one endpoint schedules.

These are finite-budget capability guarantees, not complete eventual exploration or training results. The primary set is **exact zero regret**; the parent's enlarged numerical threshold .00720005 requires a separate bound. The main manuscript and Lean ledger are unchanged.

## Evidence and reproduction

- `audit.py`, `audit_results.json`, `audit_bellman.json`: exact objective minimum, fixed-policy lower witness and Bellman-face audit.
- `compressed_oracle.py`, `linear_native_oracle.py`: the 857-variable exact-face policy LP and full-history linear optimization wrapper.
- `audit_compressed.py`, `audit_compressed.json`: independent exact model reconstruction, likelihood-ray compression and decoder equivalence checks.
- `native_count_certificate.json`, `audit_native_count_bound.json`: all 256 rational event/world upper certificates for the .07384 count-decoder guarantee.
- `native_history_stable_bound.py`, `native_history_stable_decoder.json`: stabilized full-history common-decoder search, using five exact adaptive likelihood rays.
- `certify_native_history.py`, `native_history_certificate.json`: rational full-history decoder and exact event upper witnesses; see `audit_native_history.py` and `audit_native_history_bound.json` for the independent audit.
- `numeric_search/`, `count_seed_lower_results.json`: 30 initial and 300 additional local starts. No larger lower witness was found; search convergence is not a global theorem.
- `polishing_summary.json`: bounded exact-polishing attempts and their explicit failure to establish equality; these are development probes, not replacement certificates.
- `theory/AMENDMENTS.md`: exact six-to-five target compression without changing the intervention or its information.

The independent audits run as `python3 audit_compressed.py`, `python3 audit_native_bound.py`, and `python3 audit_native_history.py` from this directory. Run search scripts with `OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1` for reproducible resource use. `bash build_report.sh` rebuilds the report; compile `theory/theory.tex` with `pdflatex` twice for the proof note. The final `verification.json` binds source and result hashes and records which checks ran.

## Remaining task

The near-matching rational certificate strongly localizes the unresolved extremum. Exact equality at .072 still requires an exactly feasible sharp certificate or a proof; it must not be inferred by rounding the interval. Then extend the guarantee to positive objective regret, starting with the predecessor's .00720005 numerical threshold. Preserve the distinction between policy-specific deficiency and a single decoder shared across a family of policies.
