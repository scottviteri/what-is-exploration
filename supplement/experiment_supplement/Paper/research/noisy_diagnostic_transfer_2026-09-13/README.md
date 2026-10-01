# Noisy native diagnostics under competing acquisition

[Research report](report.pdf) ([editable source](REPORT.md)) · [Exact proofs](theory/theory.pdf) · [Frozen protocol](PROTOCOL.md)

First completed research tranche, 13 September 2026. A finite diagnostic objective supports computable guarantees for omitted native targets, but exact noisy marginal simulation can miss joint capability. The study combines a general transfer certificate, an exact four-step native counterexample, and complete purpose envelopes for seven objectives.

- **Exact theory:** a finite common-decoder LP gives `δ(E,T) ≤ b + κL(E)` for every finite-signal source. Its near-optimal consequence retains diagnostic residual, acquisition minimum and objective regret. All 180 rational certificates passed 9,120 independently reconstructed vertex checks.
- **Completed experiment:** 54 optima and 930 complete purpose envelopes across H=3/4, three noise pairs, two planning priors and the specified objective/tolerance grid. Both independent audits passed. All 342 omitted-target transfer cases have a bound below the no-data error; 291 improve on the declared composition/reconstruction baselines.
- **Capability differences:** at H=4 and sensor error .1, the worst parity accuracy among singles-optimal policies is .805797; adding the joint target restores .82, and adding repeat targets gives .8776. Uniform-prior information gain also guarantees .8776. There is no universal native-objective win.
- **Budget warning:** singles-optimal parity protection was .82 at H=3. More budget admits additional bad optimizers when the finite target loss leaves a capability unconstrained. This does not mean an individual collector loses information by observing more.

No selected-paper or Lean claim was changed. The proofs and finite rational certificates are distinct from the float64 policy LP evidence. Pooled saved-policy errors are lower witnesses for explicitly enlarged numerical cost sublevels, not complete worst-deficiency envelopes. Read the report for acquisition costs, tradeoffs and the remaining gaps.

## Results and provenance

- [Complete envelope CSV](envelopes.csv) and [figure](purpose_envelopes.pdf).
- [Transfer-bound CSV](transfer_bounds.csv), [analysis summary](analysis.json), and [analysis implementation](analyze.py).
- [Three-step outputs](results/results.json) and [four-step outputs](results_h4/results.json), each linking every policy and LP/decoder/decision certificate.
- [Independent H3 audit](audit_h3.json), [H4 audit](audit_h4.json), [exact/enumeration controls](audit_controls.json), and [auditor](audit.py).
- [Verification manifest](verification.json), including current source/output hashes and repository checks.
- [Certificate proofs and generator](theory/README.md), [planner schema](PLANNER_SCHEMA.md), [planner](compute.py), and [invocation runtimes](planner_runs.json).
- [Preceding assessment](../intrinsic_objective_project_review_2026-09-12/README.md) and [deterministic-diagnostic predecessor](../native_diagnostic_basis_2026-09-12/README.md).

The [completed full-count follow-up](count_extension/README.md) keeps these collectors fixed and tightens 94 of 126 omitted-target bounds using confidence information discarded by majority voting. Its separate report and proofs preserve this first study’s frozen artifacts and retain the remaining uncertainty about sharp policy-restricted error envelopes.

The [policy-restricted adaptive follow-up](sharp_adaptive/README.md) proves the exact H=4 repeat-objective minimum and characterizes its six scored optimal profiles. It adds an exact .072 lower witness and a rational all-optimizer upper within two billionths of it, while keeping exact sharpness and positive-regret extensions separate. This uses the actual native-optimal policy set; the preceding sealed studies remain unchanged.

## Reproduction

Run from this directory with Python, NumPy, SciPy, and Matplotlib installed. The following writes fresh `rerun_*` outputs; it preserves the recorded production evidence. The two horizon stages may run independently. The source hashes must match when resuming.

```bash
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 compute.py --mode production --horizons 3 --output rerun_h3
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 compute.py --mode production --horizons 3 --output rerun_h3 --tolerances secondary --resume
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 compute.py --mode production --horizons 4 --output rerun_h4
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 compute.py --mode production --horizons 4 --output rerun_h4 --tolerances secondary --resume
python3 audit.py --input rerun_h3/results.json --output audit_rerun_h3.json
python3 audit.py --input rerun_h4/results.json --output audit_rerun_h4.json
python3 audit.py --controls --output audit_rerun_controls.json
```

`python3 analyze.py` regenerates CSVs, the figure and analysis from the original recorded production results. `--inputs rerun_h3/results.json rerun_h4/results.json` selects new inputs. Theory reconstruction commands are in its README. `bash build_report.sh` rebuilds this report from `REPORT.md`; the proof note has its own authored LaTeX source. Narrative tables in the report should be reviewed if computation inputs change.
