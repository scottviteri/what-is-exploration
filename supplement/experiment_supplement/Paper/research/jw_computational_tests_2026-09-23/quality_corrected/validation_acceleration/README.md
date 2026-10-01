# Independent target-cache acceleration

The corrected validator passes the same checks and is **1.65–1.67 times faster**
on the two selected completed old audits. Frozen `quality/` files and evidence
were not changed. The corrected worker also caches its native target kernels;
all 32,768 producer and validator kernels are bit-identical to their respective
original implementations on the archived design model.

| Full validation | Original wall time | Cached wall time | Speedup |
|---|---:|---:|---:|
| First completed q4/concentration0.2 audit | 22.43 s | 13.62 s | 1.65x |
| First completed q4/concentration5.0 audit | 22.87 s | 13.71 s | 1.67x |

Both comparisons independently replay **32,768 saved decoder/dual witnesses**.
Every returned field except timing matches exactly: completion, global bounds,
all reported residual maxima, checked chunk hashes, scope and input replay.
CPU time closely matches wall time under the corrected allocation; these timings
are not extrapolated from the earlier 36-worker throttled run.

## What changed

A deterministic depth-four target selects sixteen of the 256 controlled
length-four action/observation paths. Each path has code
`sum_d (2*a_d+o_d)*4^(3-d)`. The action at depth d is selected by tree bit
`14-((2^d-1)+observation_prefix_d)`. Thus caching the 256 literal path laws and
selecting their compatible columns is the same finite target kernel; no
probability, target, action, objective, or policy changes.

The validator constructs the controlled laws by shared-prefix expansion using
explicit per-world matrix products, then finds compatible columns recursively.
The producer independently propagates each complete path with its original
einsum operations and uses the closed-form node index. Neither calls the other's
target generator or the planner. The old direct functions remain available as
references, and the exhaustive equivalence test compares every target ID.

The validator also decompresses each checked NPZ field once. Every field length,
shape, finiteness, stochasticity, target equality, input/source/chunk hash, global
bound and hardest-witness check remains. **Both witness-check functions are
byte-for-byte unchanged**, including all numerical thresholds and arithmetic.

Caching reduces target-generation time alone from 13.64 to 0.12 seconds for the
producer, and from 8.04 to 0.12 seconds for the validator, with cache setup below
0.02 seconds. These are target-generation timings, not whole-solver speedups.
The two-second corrected-producer smoke run retained 441
valid targets, correctly reported a timeout, and passed independent cached
validation using the full-revelation global upper.

## Provenance and reproduction

`PROTOCOL.json` fixes the two old audit paths and archived model without looking
at capability scores. `SOURCE_CHANGES.json`, the preserved before files and
`SOURCE_DIFF.patch` record the exact change. `check_acceleration.py` reproduces
all-kernel equivalence (`--mode kernels`) or either full validation comparison
(`--mode case0` / `case1`), with explicit `--cpu`. It writes new reports here and
never writes to the original audit folders. Use a fresh report directory for a
later benchmark rather than overwriting this snapshot.

`CHECKS.json` and `FILES_SHA256.json` bind the completed delivery. All checks used
CPUs8/9 with at most two concurrent processes alongside the root's eight corrected
planning workers, respecting the actual cgroup-v1 10.2-CPU quota. No full audit
queue was launched. The evidence remains floating-point numerical validation,
not an exact-arithmetic, Lean, learning, or eventual-exploration result.
