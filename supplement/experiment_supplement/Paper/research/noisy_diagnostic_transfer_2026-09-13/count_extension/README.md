# Full repeat counts and native transfer

[Research report](report.pdf) ([source](REPORT.md)) · [Eight-page proof note](theory/theory.pdf) · [Frozen protocol](PROTOCOL.md)

Completed follow-up, 13 September 2026. Keeping every parent collector and intrinsic objective fixed, using the full three-reading count instead of its majority bit tightens transfer guarantees. The repeat objective already scored the full records; this improves what the proof extracts from them.

- **Useful transfer gains:** counts improve the raw majority bound in all 126 omitted-target cases, and the strongest previous bound in 94. At H=4 and noise .1, the repeat objective's adaptive-target upper falls from .093452 to .079070, retaining acquisition cost and regret. Its saved lower witness is .072.
- **A precise information distinction:** majority and full count have the same balanced bit-guessing accuracy, but their deficiency is `3e²(1−e)²(1−2e)`. At noise .1 it is .01944, witnessed by an asymmetric subsequent decision.
- **General theorems:** exact count and target compression, an event-dual transfer LP, monotonicity under diagnostic refinement, and an obstruction to zero residual for a common repair of strictly positive product-coordinate diagnostics.
- **Boundaries retained:** 32 omitted-target cases gain nothing over an already stronger old bound. Remaining upper/lower gaps are not sharp capability envelopes. Numerical witness sets retain the parent's explicit enlargement; rational certificates establish feasibility, not search optimality.

All 180 production certificates and 28,800 exact event/world checks passed independent audit, including application to all 984 parent collectors. Production took 27.91 seconds; the independent production audit took 17.09 seconds. No policy optimization, manuscript revision, or Lean update was performed.

## Evidence and reproduction

- [Certificate index](results.json), linking exact decoders and event potentials in `certificates/`; [production validation](results_validation.json).
- [Independent controls](audit_controls.json), [full production audit](audit_results.json), and [audit implementation](audit_counts.py); [independent comparison audit](audit_comparison.json) and [its source](audit_comparison.py).
- [All 252 target comparisons](comparison.csv), [summary](comparison.json), and [figure](count_transfer.pdf).
- [Certificate generator](compute_counts.py), [comparison code](compare.py), and [theory sources](theory/README.md).
- [Verification manifest](verification.json) and [parent study and original objective results](../README.md).

From this directory, `python3 compare.py` regenerates the comparison CSV, summary and plot using the saved certificates. `bash build_report.sh` rebuilds the report from its editable Markdown; review narrative tables if inputs change. The proof note uses its own authored LaTeX and build instructions.

`python3 compute_counts.py --mode production` regenerates the extension's certificate index and `certificates/` files from the frozen model; it does not rerun or alter parent policy optimization. Development-only mode is the default. Numerical search uses SciPy/HiGHS, with exact rational reconstruction in Python. `python3 audit_counts.py --controls` checks independent controls; `python3 audit_counts.py` audits the production certificates and saved collectors; `python3 audit_comparison.py` independently audits all 252 comparison rows. Recorded solver versions and hashes are in the output files.

The [policy-restricted follow-up](../sharp_adaptive/README.md) now proves the exact acquisition minimum and encloses the worst adaptive error among exact optimizers within two billionths of .072. Exact equality and positive-regret extensions remain separate open tasks; the sealed results of this count study are unchanged.
