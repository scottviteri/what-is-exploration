# Exact polishing status — 13 September 2026

The bounded polishing investigation stopped without proving exact equality at
`9/125 = .072`. The main result remains the independently audited enclosure

`9/125 ≤ worst adaptive deficiency ≤ 72000001123/10^12`.

The upper is `.072000001123`. Its complete artifact is
`native_history_certificate.json`; `audit_native_history_bound.json` independently
checks the decoder, target lifts, all 128 world/event objectives, and exact dual
bounds. No production certificate was replaced by a polishing candidate.

## What the probes established

- `polish_history_probe.py` recovered exact feasible native-LP points and tried
  an arbitrary-coordinate projection onto their active target constraints.
  This worsened other event bounds and eventually produced a negative decoder
  coordinate. It stopped after 24.55 seconds. The failure is preserved in
  `history_polish_probe_results.json`.
- `polish_history_minnorm.py` instead projected in the direction of least squared
  coordinate change, starting from `native_history_refine_checkpoint.npz`.
  After 9 iterations, 54 recovered boundary cuts, and 48.65 seconds, it produced
  the rational stochastic candidate `native_history_minnorm_candidate.json`.
  Numerical separation reported `.07200000000947744`. This is a candidate,
  not an exact all-event upper. Intermediate exact primal point vectors were
  not exported, so the development log is not an independent proof artifact.
- `exact_basis_probe.py` reconstructed exact native-LP duals from HiGHS bases
  for three critical events. Their resulting upper bounds still exceeded
  `.072`: approximately `.0720000001940`, `.0720000000339`, and
  `.0720000000206`. The first required clipping a positive inequality
  multiplier and applying an exact residual correction. These partial bounds
  do not establish a global upper. Full rational multipliers and residuals are
  in `exact_basis_probe_results.json`.

`polishing_summary.json` records the status, limitations, remaining obligation,
artifact sizes, and SHA256 hashes. Candidate inputs and producer hashes are
also recorded in the candidate and probe outputs.

## Reproducing the development probes

These probes used temporary dependencies in `/tmp/native_exact_polish`, not a
change to the repository environment. The production certificate and its audit
use the preexisting environment and do not require these packages.

From the repository root, install the two packages actually used by the probes:

```sh
python3 -m pip install --target /tmp/native_exact_polish python-flint==0.9.0 highspy==1.15.1 numpy==2.5.3
```

`swiglpk==5.0.13` was also installed during investigation but was not used by any
saved probe. The scripts add `/tmp/native_exact_polish` to their import path.
To reproduce candidate generation, run in order:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 Paper/research/noisy_diagnostic_transfer_2026-09-13/sharp_adaptive/polish_history_probe.py
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 Paper/research/noisy_diagnostic_transfer_2026-09-13/sharp_adaptive/polish_history_minnorm.py
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 Paper/research/noisy_diagnostic_transfer_2026-09-13/sharp_adaptive/exact_basis_probe.py
```

These commands overwrite only their development outputs; preserve a copy before
rerunning if comparing against the recorded hashes. The last probe checks the
current minimum-norm candidate if present. Solver basis choice can change with
package versions, so a successful run is not a substitute for checking a newly
produced certificate.

The remaining mathematical obligation is an exact stochastic decoder whose
128 event bounds are all at most `target_mass + 9/125`, or an exact policy
witness with deficiency above `9/125`. Neither was established here.
