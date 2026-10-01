# Post-design same-time experiment-order diagnostic

This supplementary analysis was requested after the study design and while the
primary analysis was unfinished. It changes no primary endpoint, policy, target,
optimizer, budget, or claim. Its source and complete queue are frozen in PLAN.json
before any diagnostic LP runs. Numerical execution requires the primary
ANALYSIS_EXECUTION.json state `passed` and a bound, independently checked summary.

The fixed grid is all 12 original model classes × four primary native methods
(fixed, tractability, hard, minimax) × three baselines (information, brier,
uniform) × both directed deficiencies, at the 40-second planning checkpoint:
288 requested LPs and 144 paired comparisons. There is no outcome selection,
deduplication, extra seed, retry by this driver, or expansion after failure.
Both acquired experiments are the saved complete length-three action-observation
records on the same ordered world class. No policy is optimized here.

For experiments E and F, the direction E→F means
`min_G max_q TV(E[q] G, F[q])` over world-independent stochastic decoders G.
Thus a small E→F upper says E approximately simulates F. It does not say that F
simulates E. The experiment includes actions, retains the full record, and is
checked by propagation through the original T and Z physical-state arrays,
starting from state zero. The worker and checker use separate pathwise and
shared-prefix propagation implementations.

The existing StableDecoder backend is used without modification, with its
default simplex algorithm and existing bounded internal fallback sequence.
There is a 30-second wall cap on each worker process, including its import,
setup, solve, witness extraction, and export. The backend receives a time limit
of at most 30 seconds; internal fallback attempts share that budget. The driver
runs sequentially on CPU25, niceness at least 10, BLAS/OpenMP threads one, using
the CPU virtual environment and no GPU. A timeout or error stays in the results;
no parameter, tolerance, algorithm sequence, or cap is retuned to rescue it.

Each successful solve saves the full decoder G, dual alpha/b, source E and
target F, and raw lower/upper values. The checker imports no solver. It verifies
the saved experiments against the original policies and physical model; checks
stochastic G, alpha≥0 with sum one, and 0≤b[q,y]≤alpha[q]; and independently
evaluates `upper=max_q sum_y |(EG)[q,y]-F[q,y]|/2` and
`lower=sum_qy F[q,y]b[q,y]-sum_x max_y sum_q E[q,x]b[q,y]`.
Gap tolerance is 2e-7, witness feasibility
and saved-value replay tolerance 1e-12, and policy replay tolerance 1e-10.
These are floating-point numerical brackets, not exact or outward-rounded proofs.

Every timely policy with a passing planning check is eligible for an order LP,
even if its separate native audit is missing. Missing, late, invalid, and failed
endpoints retain their full planned rows. Primary native-audit comparisons are
joined only when both original endpoints were comparison-eligible, using their
original 1e-6 separation rule. This join is descriptive, never an LP-selection rule.

If both directed lower bounds exceed 1e-6, report numerical evidence of same-time
incomparability. A directional upper at most 2e-7 reports approximate simulation
only. If both uppers meet that tolerance, report mutual approximate simulation;
if just one does and the reverse lower exceeds 1e-6, report approximate simulation
with reverse separation. All remaining checked pairs are unresolved; any missing
direction makes the pair unavailable. Tiny numerical uppers never establish
exact zero, exact Blackwell dominance, strict native-process dominance, eventual
exploration, or a continuation theorem. The 12 settings share two seed families;
the counts support no population or significance inference.

Run `tests.py` for analytic witnesses and synthetic causal records, without any
solver or confirmation inputs. Then `run.py --prepare` freezes this protocol,
the sources and metadata-only grid. `run.py --run --wait` waits for the primary
check, executes the fixed queue once, and produces saved witnesses, all 288
direction rows, all 144 pair rows, an independent CHECKS.json, and a report.
