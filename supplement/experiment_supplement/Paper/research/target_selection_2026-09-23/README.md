# Target selection and finite computation

the lead author authorized this larger experiment on 23 September 2026. It compares
structured, random and adaptive native-target selection, finite weighted scores,
favorable near-optimal information/Brier policies, and longer collection/audit
horizons. Read [PROTOCOL.md](PROTOCOL.md) for the frozen scientific choices and
[RESEARCH.md](RESEARCH.md) for the mathematics, prior failures and interpretation.

[VALIDATION.json](VALIDATION.json) records the bounded prelaunch checks.
[VALIDATION_HISTORY.md](VALIDATION_HISTORY.md) preserves the numerical failures
and their resolutions. [DECODER_STRESS.json](DECODER_STRESS.json) independently
checks original-source bounds after tiny-column coarsening. These are numerical
checks, not new Lean results.

The main run started at **08:37:59 UTC on 23 September**, with an eight-hour cap
(ending by about 16:38 UTC). Its [frozen manifest](main_manifest.json) registers
**1,368 jobs over 22 model classes**. Follow [live status](main_results/STATUS.md),
[checkpoint data](main_results/CHECKPOINTS.csv), or `main_results/queue.json` for
actual coverage. [LAUNCH.json](LAUNCH.json) records the supervisor PID and command.
Three CPU workers and one serialized GPU worker share four one-core slots.
Completed checkpoints survive timeout, interruption or a later cell failure.

The [eight pilots](pilot_manifest.json) finished with seven complete jobs and one
K=128/four-step timeout that preserved its K=8,16,32,64 checkpoints. The
[pilot review](PILOT_REVIEW.json) passed 644 checks: it reconstructed 20 saved LP
certificates, replayed all 21 accepted policies, verified 44 original-source
witnesses and 100,736 profile entries, and checked paired CPU/GPU objectives.
The final bounded implementation validation passed 281 checks. The main four-step
curves therefore stop at 64 targets; five-step curves stop at 16. Three-step
curves reach 128, and the longer target audit enumerates all 32,768 four-step trees.
Full minimax certification is reported separately from completion of a curve.

The separate [decomposition study](decomposition_research/README.md) completed
16 independently checked configurations for smaller master LPs with decoder
cuts. It solved the pilot's difficult 128-target/four-step problem in 17.93 seconds;
one small case was slower than the existing solver. Its timings, preserved
failures and interpretation remain separate from the objective comparison.

Completed checkpoint directories preserve literal models, policies, target IDs,
compact LP vectors and matrix hashes, target-by-target original-source bounds,
hardest-target witnesses and timings. Incomplete sweeps are named `*_partial.npz`
and never count as complete audits. Full matrices are deterministically rebuilt
from the frozen source/model/target list for certificate checking. CPU/GPU source
snapshots and imported model-generator hashes accompany each queue.

The finite native objectives are not eventual infinite-rich J_w. The complete
Bayesian alarm results remain separate from these finite-return optimizations.
ICM/RND/first-visit archives and the 21-condition selected startup study are
unchanged. No manuscript, shared support ledger, commit, push or export is part
of this run.
