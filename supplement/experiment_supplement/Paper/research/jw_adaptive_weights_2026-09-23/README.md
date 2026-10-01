# Adaptive native weights: research and prepared implementation

23 September 2026. **The bounded research/preparation phase is complete. No new experimental policy optimization, solver benchmark, training, Lean build or manuscript change was performed.** The backend bridge is prepared, not numerically validated. This directory is isolated from the frozen campaign and other owners' work.

The recommendation is to pursue two separate tracks: use adaptive weights and retained decoder cuts to make a declared native objective cheaper to approximate; use hard-target weights to approach a declared worst-target criterion. Both can retain a fixed strictly positive background on a rich native target family. Neither automatically improves an independent capability audit, and the saved evidence contains substantial negative cases.

The strongest new mathematical conclusions are written proofs in [THEORY.md](THEORY.md), not new Lean results:

- **Positivity survives adaptation.** Each final `w=(1-epsilon)v+epsilon b` still defines a strictly order-sensitive full eventual objective. Comparisons must use one common final weighting; old aggregate optimum bounds do not survive a weight change automatically.
- **Finite approximation can be reported honestly.** If the selected terms have certified candidate upper bound `U`, omitted weight `beta`, and a fresh master lower bound `B`, full finite-time regret is at most `U+beta-B`. This is not an eventual-regret certificate. A small weight gives a weak coordinate guarantee: `ell_j <= (1-J_w)/(epsilon b_j)`.
- **There is a conditional convergence result.** If zero loss is approachable, a fixed positive background and vanishing full eventual final-weight regret force every fixed target error to zero even if weights oscillate. Moreover, increasing collection time converts vanishing full finite-time optimization error into eventual regret convergence for fixed weights, uniformly for weights varying over a fixed finite emphasis library. This gives no finite-time rate, online execution guarantee, or successful limit of policy tables; truncation errors must also vanish.
- **Hard-target weighting has a finite minimax interpretation.** Under explicit convexity, oracle and error assumptions, multiplicative weights with averaged realization plans has a quantitative finite robust-loss guarantee. Cooperatively selecting easy targets and taking arbitrary minimizers of dual-supported weighted losses can fail badly. Literal native counterexamples show both failures.

A fixed-dual hardest-target search admits a backward recursion, but its remaining outer optimization is nonconcave even in a tiny native example. This is useful structure, not an efficient general separation oracle.

The [evidence synthesis](EVIDENCE.md) preserves the failed September-15 broad-benefit screen, the partial campaign's coverage and favorable information/Brier controls, the delayed-case reversal at longer target depth, and worse worst-case error after adding targets. The frozen small-LP prototype was faster on some large cases and slower on a small one. No new speed or objective-quality result is claimed here.

## Artifacts

| File | What is ready |
| --- | --- |
| [THEORY.md](THEORY.md) | Definitions, explicit rational rich background, proofs, native counterexamples, finite-to-eventual boundary, oracle analysis, existing Lean scope |
| [EVIDENCE.md](EVIDENCE.md), [EVIDENCE_INPUTS.json](EVIDENCE_INPUTS.json) | Compact saved-evidence synthesis, fourteen input hashes, reconstructed comparison counts and failures |
| [PROTOCOL.md](PROTOCOL.md) | Falsifiable backend and objective studies, charged adaptation, independent confirmation, favorable baselines and feasibility gates |
| [adaptive_weights.py](adaptive_weights.py) | Exact rational target encodings/laws, positive-background truncation, objective identity, cut cache, fresh-bound bookkeeping |
| [target_oracle.py](target_oracle.py) | Exact fixed-dual native-target recursion with explicit expansion cap; produces a lower witness, not a global oracle |
| [weight_updates.py](weight_updates.py) | Declared tractability heuristic, finite hard-target update, realization-plan averaging; floating-update limitation explicit |
| [frozen_adapter.py](frozen_adapter.py), [DEPENDENCIES.json](DEPENDENCIES.json) | Pinned source bridge, fresh-process import isolation, retained-cut witness reconstruction and new aggregate bounds; numerical path unrun |
| [dry_run.py](dry_run.py), [DRY_RUN.json](DRY_RUN.json) | Synthetic illustrative objectives and proposed job specification; execution disabled |
| [check.py](check.py), [CHECKS.json](CHECKS.json) | Sixteen tiny solver-free checks, source hashes and measured resource use |
| [HANDOFF.md](HANDOFF.md) | Completion record, safe commands, remaining validation and execution boundaries |

## Run only the small checks or dry run

From the repository root:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 Paper/research/jw_adaptive_weights_2026-09-23/check.py
PYTHONDONTWRITEBYTECODE=1 python3 Paper/research/jw_adaptive_weights_2026-09-23/dry_run.py --output Paper/research/jw_adaptive_weights_2026-09-23/DRY_RUN.json
```

Neither command imports NumPy/SciPy/HiGHS or runs a solver. The check command enforces a ten-second wall cap, nine-second CPU soft cap, 256 MiB address-space cap and single-thread settings. Metadata expansion in the prepared target encoder is deliberately bounded; its mathematical infinite enumeration is defined in THEORY.md. A cached coefficient digest is not a proof: numerical execution additionally requires the saved dual witness, source lock verification, reconstruction of each cut and independent validation.

The prepared bridge supports finite weighted loss and the selected part of a rich-background objective. It does not yet implement the robust-background epigraph, reward-face constraints, a general hard-target oracle, rigorous floating update errors, or an arbitrary-world-class evaluator. New numerical paths require the separate resource allocation and validation described in the protocol. There is no automatic launch or delayed campaign.
