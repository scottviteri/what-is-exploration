# Exhaustive audit worker validation

This directory validates the reusable `../audit_worker.py` and independently
implemented `../validate_audits.py` on **archived design seed 2026096900**, four
worlds, three hidden states, concentration 1. No confirmation model or reward
comparison was used.

Two full 32,768-target depth-four audits test collection length three:

- Uniform independent actions. Input E/rows/leaf were produced by the frozen
  existing realization replay; the worker reconstructs them independently.
- A fixed seeded nonuniform history policy, with explicit zero/one action rows
  and consequently null source columns. This tests canonical row order and
  world-independent decoder completion on null histories.

Every completed target saves its entire decoder and decision-dual witness.
The separate validator reconstructs model/policy E through direct per-world
matrix products, and target F through recursive tree execution. It imports
neither the producer nor the solver. It then replays all witnesses on original
probabilities and checks global coverage and bounds.

The negative checks are retained:

1. A three-second run must return a partial audit whose upper bound comes from
   the full-revelation decoder, not from its incomplete target sweep.
2. A stochastic E with permuted columns, inconsistent with its unchanged
   conditional policy, must be rejected before target solves.
3. An explicitly negative saved decoder entry must be rejected even after
   updating the chunk hash to match the tampered file.

The first timeout test revealed a reporting issue: the old backend caught the
whole-job `TimeoutError` and rethrew a generic failure. Its valid partial numerical
witnesses were retained. The released worker uses a dedicated deadline signal
that bypasses backend retry catches and correctly reports `partial_timeout`.
`partial_adaptive/` is that initial reporting-failure record;
`partial_adaptive_v2/` is the corrected passing control. No numerical tolerance
changed. The initial uniform full audit began before this reporting-only repair;
its exact executing source is preserved as
`worker_before_timeout_classification.py` and matches its provenance hash.
The second full audit uses the exact released worker revision and saved source
snapshots.

Both complete audits passed independent validation: uniform took **216.50 s**
on one CPU (largest target bracket `6.75e-10`), and the nonuniform policy took
**134.24 s** (largest target bracket `9.47e-10`). Independent validation took
22.32 s and 21.45 s respectively, reconstructing every target and every witness.
The corrected timeout retained 664 certified targets and the valid global upper.
Both inconsistent-input and hash-consistent decoder-tampering controls were
rejected as intended. All worker/validator processes have finished.

`CHECKS.json` records final run/validation statuses and source hashes.
`FILES_SHA256.json` binds this completed validation package. Expected negative
controls are explicitly marked as expected failures, not omitted or counted as
successful audits. The evidence is floating-point, with original-probability
feasible decoder/dual witnesses; it is not an exact-arithmetic or Lean proof.
