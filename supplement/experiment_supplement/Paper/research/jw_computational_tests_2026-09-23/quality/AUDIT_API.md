# Exhaustive fixed-policy audit API

Stable CLI (one process/CPU per policy):

```sh
/tmp/exploration-lp-gpu-venv/bin/python audit_worker.py \
  --model /absolute/model.npz --policy /absolute/policy.npz \
  --out /absolute/new_audit_directory --cpu 16 --hard-seconds 1800

/tmp/exploration-lp-gpu-venv/bin/python validate_audits.py \
  --audit /absolute/new_audit_directory --cpu 16
```

`--out` must be absent or empty: the worker refuses to overwrite an earlier run.
The caller may launch independent policies concurrently on separately allocated
CPUs. Every numerical library is limited to one thread; this worker uses no GPU.
Input files are copied, hashed, and never modified. Planning/objective selection
is outside this API.

## Required input

`model.npz`: nonnegative stochastic arrays `T` of shape `(Q,2,S,S)` and `Z` of
shape `(Q,2,S,2)`. Each world starts in physical state 0; actions transition through
T before producing an observation through Z.

`policy.npz`: `E` of shape `(Q,64)`, `rows` of shape `(21,2)`, and `leaf` of shape
`(64,)`. Collection length is exactly three. Conditional action rows are in
breadth-first full-history order: root, four length-one histories, sixteen
length-two histories. Each expansion orders action 0/1, then observation 0/1.
`leaf` is the product of policy action probabilities, excluding environment
likelihoods. Columns of E follow the corresponding 64 length-three histories.
The worker reconstructs E/leaf directly from rows and the physical model and
rejects disagreement above `1e-10`; it does not trust archived E alone.

The target set is all **32,768** deterministic observation-adaptive binary
policies of depth four, not merely fixed action sequences. Integer target IDs
encode the 15 breadth-first action bits, most significant bit at the root.
Target columns follow observation words in lexicographic order. Original
physical T/Z probabilities are retained without rounding.

## Output and interpretation

- `result.json`: status, completion count, global bounds, timing, replay residuals,
  chunk hashes, hardest IDs and failure information. A complete audit requires
  `status="complete"`, `complete=true`, and exactly 32,768 unique target IDs.
- `checkpoint.json`: updated every 256 targets and on normal/failure exit.
- `bounds.npz`: all completed target IDs and original-probability lower/upper bounds.
- `chunks/*.npz`: every completed target's F, stochastic decoder G, feasible
  decision-dual alpha/b, and reported bounds, compressed in chunks of at most256.
- `hardest_witness.npz`: largest certified lower bound; `largest_upper_witness.npz`
  retains the separately largest upper bound. Ties select the first ID.
- `full_revelation_witness.npz`: decoder/dual certificate for the identity world
  target. Its upper bound is a global upper for **every** native target: compose
  the full-revelation decoder with that target's known kernel.
- `model.npz`, `policy.npz`, `provenance.json`: copied inputs, original input paths
  and hashes, execution-source hashes, package versions and command.
- `failure.json`: retained timeout/solver/input failure, when applicable.
- `validation.json`: independent checker result, created by the second command.

For a partial sweep, the global lower bound is the largest completed target lower
bound; the global upper is the full-revelation decoder upper, or the universal
TV upper 1 if that solve was not completed. A partial maximum of per-target uppers
is **never** substituted for a global upper. A complete sweep may tighten the
upper with the maximum over all target uppers.

Every accepted target is checked at unchanged tolerance `2e-7`. The solver's
coarsened numerical LP may assist stability, but lifted decoder and dual bounds
are evaluated on original E/F. Nonnegative normalized decoder rows yield the
upper bound; normalized alpha and `0 <= b[q,y] <= alpha[q]` yield the lower.
These are repaired floating-point witnesses, **not exact arithmetic or formally
outward-rounded intervals**.

Exit codes: 0 complete; 3 partial timeout; 2 other recorded failure. An output-path
refusal raises an error without modifying that directory. `--hard-seconds` bounds
numerical execution; final atomic checkpoint flush may add a small amount of
I/O time. The caller should allow a cleanup grace period before external kill.
An external uncatchable kill can leave only the last completed checkpoint, which
must be treated as partial and not as a completed result.

`validate_audits.py` imports neither the producer nor the solver. It independently
reconstructs policy E by explicit per-history/per-world matrix products and target
F by recursive tree execution; it replays every saved decoder/dual witness,
checks input/chunk hashes, target coverage, compact bounds, hardest witnesses and
global upper logic. It can validate honest partial runs. A malformed input is
rejected by the worker before certificates exist; it is not a valid partial audit.

Archived-design validation lives in `audit_design_check/`. No prospective quality
or confirmation outcome is used to select this backend.
