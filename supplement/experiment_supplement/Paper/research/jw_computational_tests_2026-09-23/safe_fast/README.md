# SAFE/FAST computational study

All **2,448 prospectively specified optimization cells** passed independent exact-rational
certificate replay. The compressed solver also agreed with literal full-record
decoder LPs in **356 cases**, including observation-dependent randomized later
actions. Their saved literal decoders and dual bounds were independently replayed
with exact fractions; the largest literal primal/dual gap was 1.32e-16.

The controlled example distinguishes **changing the finite-time objective** from
**having insufficient time to solve a fixed objective**. With the frozen target
emphasis, the certified near-optimal retained candidate chooses SAFE initially
from H=3 onward. In the infinite-world version, the corresponding candidates
with emphasis moving to FAST_H choose FAST initially through H=128. These small
optimization problems have tightly certified global bounds. This is not
a general efficiency result or a benchmark showing a practical advantage over
information gain.

## Results, including uncertainty about the omitted targets

Both schedules use a fixed positive rich background. Fixed weighting is
`epsilon*b+(1-epsilon)*FAST_1`; moving weighting is
`epsilon*b+(1-epsilon)*FAST_H`. They agree at H=1. Target weighting is a declared
preference, not a canonical choice. The full dyadic-policy background and the
special-environment compression are explained in [DERIVATION.md](DERIVATION.md).
The latter is a new written argument, **not an additional Lean theorem**.

For the infinite-world primary grid, the following are outer bounds covering every
optimizer of the full countable objective, with the omitted tail and 1e-9 range
slack charged. “Candidate first SAFE” describes the retained-LP candidate, not an
exact characterization of the infinite sum's optimizer.

| Background epsilon | Candidate first SAFE horizon | Largest certified SAFE_1 loss upper bound, fixed weights, H>=3 | Smallest certified SAFE_1 loss lower bound, moving weights, all H |
|---|---:|---:|---:|
| 0.01 | 3 | 0.0124918 | 0.499988 |
| 0.05 | 3 | 0.0124783 | 0.499935 |
| 0.25 | 3 | 0.012478 | 0.499577 |

The exact SAFE_1 capability error is `(1-q)/2`. On the infinite-world primary grid,
all retained candidates have q=0 for moving emphasis and q=1 for fixed emphasis from H=3; the table's
intervals show what the certified tail still permits for full-objective optima.
The existing Lean theorem proves persistent all-horizon loss for moving weights;
the numerical grid does not extend that theorem or prove an asymptotic limit.

![All primary curves](optimizer_curves.png)

The finite controls keep d fixed within each curve. For H>=2d-1, SAFE knows all d
unknown bits. Consequently every full native optimum has q=1 by the written
zero-loss/positive-SAFE-target argument; the numeric certificates include that
point. Exact finite-world information gain also selects SAFE by that horizon.
Earlier information-gain ties are shown as full endpoint intervals; a convenient
member of a tie is never substituted for all optima. The finite-class IG formula
and source setting are recorded in [PROTOCOL.md](PROTOCOL.md), using the pinned
Orseau et al. author PDF pp3-5. No uncountable prior or predictive surprisal is
silently substituted for that source objective.

The prespecified N/M sensitivity retains every cell. As truncation is refined,
the apparent plateau in a *certified upper bound* tightens; it is not an observed
persistent capability loss of the selected SAFE policy, whose exact loss is zero.

![Truncation certificates](truncation_sensitivity.png)

## What was checked

- [PROTOCOL.md](PROTOCOL.md) and [GRID.json](GRID.json) fixed all primary and sensitivity cells before outcomes.
- [RESULTS.json](RESULTS.json) and [results.csv](results.csv) retain every final result. All 2,448 final cells passed.
- [AUDIT.json](AUDIT.json) replays original rational weights, exact feasible candidate values, and global dual bounds from independently assembled constraint rows. Maximum retained primal/dual gap: 1.63467e-07.
- [crosschecks.json](crosschecks.json) compares the compressed 4-flow LP with actual finite full-record decoder LPs; [LITERAL_AUDIT.json](LITERAL_AUDIT.json) replays their witnesses with exact fractions.
- `cells/*.json.gz` stores all primal/dual witnesses. `crosscheck_witnesses/` stores actual full-record experiment matrices and decoders. No saved solver success flag is treated as a proof by itself.
- [RUN_METADATA.json](RUN_METADATA.json) pins the executed sources, relevant Lean declarations and primary information-gain source. No Lean or manuscript file was changed.

The retained master lower bound is B and its candidate feasible upper bound is U.
The full optimum is enclosed by `[B,U+tail]` and full regret by `U+tail-B`.
All-full-optimum q intervals are conservative sublevel-set bounds with explicit
1e-9 slack, not exact optimal faces. Rational replay makes these certificates
independent of floating-point feasibility tolerances. The rich-target reduction
still relies on the written proof and its finite crosschecks; it is not solver
verification in Lean.

## Resources and development history

The final grid took 80.58 wall seconds with at most four CPU workers pinned
to CPUs 12-15, one solver thread each, and a 4 GiB address-space ceiling per worker.
Peak reported worker RSS was 65.60 MiB. No GPU was used: these are sparse linear
programs, not neural training. Per-cell solver and elapsed times are saved. H is
the number of physical interactions used for scoring; it is not a compute budget.

Two initial development runs exposed sign errors in the manually expanded dual
certificate through exact primal/dual assertions. Both complete runs, their
sources and every failure are preserved in `initial_implementation_failure/`
and `second_implementation_failure/`, explicitly rejected as evidence. The
objective and prospective grid did not change. The corrected full rerun passed
both production checks and a separately implemented generic exact constraint-row
audit. The independent literal-record checks passed before the optimization grid.

This study supplies no unknown-model learning algorithm, general runtime bound,
computable infinite-world acquisition deadline, or single-policy online assembly.
Its known interface admits a special exact compression, so inexpensive solutions
here must not be generalized to arbitrary controlled environments. Existing
fixed-weight and finite-world convergence results remain conditional Lean theorems;
finite experiments neither prove nor refute their asymptotic statements.
