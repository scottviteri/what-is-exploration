# Fixed-source GPU audit feasibility pilot

The persistent CPU decoder is the usable backend for this study. The tested GPU
formulation produced valid numerical bounds on tiny controls and small batches,
but was slower and did not reliably close the required `2e-7` bracket. GPU memory
capacity was not the limiting factor. No reward objectives, optimized collectors,
or adaptive-versus-baseline outcomes were compared.

## Design and correction

This is a pre-outcome feasibility test with uniform independent action collectors,
three hidden states, binary actions and observations, Dirichlet concentration 1,
collection lengths 3/4 and all deterministic depth-four targets as the intended
audit. The GPU was an RTX 4090; at most four CPU cores were used. All GPU work is
complete; `GPU_RELEASED.json` records the release boundary.

The parent's initial task named seeds 926101/926102. The parent then corrected
that timing pilots must use existing design classes. The initial run was stopped
and its artifacts retained in place (`SEED_CORRECTION.json`); it produced models
for 926101 with 4/8 worlds and lengths 3/4, and 926102 with 4 worlds and lengths
3/4 (the last numerical case was interrupted). Both seeds must be treated as
design/exposed, not future confirmation seeds. No outcome comparison was made.
The corrected run uses archived manifest seeds 2026096900 (4 worlds) and
2026100900 (8 worlds), with unchanged parameters.

## Numerical method and checks

For original experiment matrices E and F, the deficiency dual maximizes

`sum(F*b) - sum_x max_y (E.T*b)[x,y]`

subject to `alpha >= 0`, `sum(alpha)=1`, and `0 <= b[q,y] <= alpha[q]`.
Its epigraph variables `s[x]` can be restricted to `[0,1]` without changing the
optimum: the maximum is nonnegative and at most `max_q E[q,x] <= 1`.
The new GPU adapter therefore batches exact finite-box LP formulations, without
rounding or modifying E/F. It uses the existing cuOpt PDLP installation.

The GPU primal variables give a feasible lower witness after alpha normalization
and b clipping. Its row multipliers propose a decoder, which is made nonnegative
and row-normalized; an empty row is filled uniformly. Every resulting decoder is
re-evaluated on the **original** E/F for an upper bound. Null columns are lifted
back explicitly. A repaired decoder alone is not a successful solve: the
original-probability upper-minus-lower bracket must be at most `2e-7`.

Four controls cover null columns, a perfect experiment with zero deficiency,
source probabilities near `1e-12`, and deficiency near `1e-12`. The controls pass.
Each corrected 16-target batch is compared to persistent CPU dual solves and to
three independently assembled direct-primal LPs. Every small-batch CPU/GPU
bracket overlaps. An additional CPU-only script independently replays saved
arrays. These are repaired floating-point certificates, not exact arithmetic or
outward-rounded rigorous interval proofs.

## Measured feasibility

The following times cover a 16-target batch, excluding setup. CPU totals include
witness replay. The extrapolations are rough serial CPU throughput estimates,
not completed audits or runtime guarantees.

| Archived design | Collection length | GPU seconds | GPU bracket accepted | CPU seconds | Estimated serial full audit |
|---|---:|---:|---|---:|---:|
| 4 worlds | 3 | 4.28 | yes | 0.143 | 4.9 min |
| 4 worlds | 4 | 20.03 | no; time limit | 0.944 | 32.2 min |
| 8 worlds | 3 | 14.65 | yes | 0.375 | 12.8 min |
| 8 worlds | 4 | 20.03 | no; time limit | 2.940 | 100.4 min |

Increasing the GPU batch to 128 at collection length three did not fix the
problem: both design batches hit the 20-second solve cap. The 4-world batch
closed 127/128 brackets and the 8-world batch 74/128. Maximum remaining gaps were
`5.14e-6` and `4.44e-5`. The two 16-target length-four gaps reached `1.59e-5` and
`9.53e-5`. All rejected attempts, raw outputs, repaired witnesses and logs remain
available. No numerical tolerance was relaxed.

`VALIDATION.json` independently replays 468 saved small/large-batch GPU and CPU
witnesses; all are feasible within recorded floating-point tolerances, with 70
accuracy rejections retained. Feasible-but-loose bounds are not accepted exact
finite audits. The archived source hashes remain unchanged.

A single predeclared 4-world, length-three complete CPU audit was subsequently
split into four fixed target ranges, with a separate 180-second hard wall cap,
after the serial throughput estimate showed that this fit the original bounded
pilot. This tests throughput, not an objective ranking. It completed all **32,768 targets in 52.52 seconds** across four CPU workers.
The largest per-target bracket was `2.66e-10`; all 32,768 saved witnesses passed
independent CPU replay, with maximum feasibility residual `4.45e-16`. These are
actual full-sweep measurements, replacing the small-batch extrapolation for this
one design case. `CPU_FULL_RESULTS.json` and `CPU_FULL_VALIDATION.json` record the
details. All per-target decoder and dual witnesses are retained
in `cpu_full_chunks/`; a partial run must never be presented as a complete audit.

## Reproduction and scope

`pilot.py` is the initial interrupted seed run and shared GPU/CPU implementation.
`design_pilot.py` is the corrected archived-design pilot.
`full_cpu_parallel.py` is the one full CPU audit.
`validate_saved.py` and `validate_full_cpu.py` only replay saved arrays on CPU.
They use `/tmp/exploration-lp-gpu-venv/bin/python`; environment versions and source
hashes are recorded in the protocols. Running the writers in this directory would
overwrite this snapshot; use a fresh output copy for a later run.

The recommendation is to keep the persistent CPU decoder for the main finite
study, parallelizing independent audits under the agreed resource budget. This
pilot does not establish GPU infeasibility in general, a practical evaluator of
complete eventual J_w, objective superiority, or a learning algorithm.
