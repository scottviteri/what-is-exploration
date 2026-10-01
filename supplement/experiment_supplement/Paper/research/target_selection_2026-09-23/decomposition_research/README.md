# A smaller finite native-objective planner

Research and bounded implementation pilot, 23 September 2026. This directory is
independent of the running target-selection campaign. No campaign source,
manuscript, existing evidence archive, or launch configuration was changed.

The dual-cut planner is mathematically valid for the supplied finite model and
explicit target library. All 16 distinct tested configurations converged with
independently checked numerical bounds. Thirteen have matching monolithic LP
certificates; the monolithic comparator timed out in two configurations, and the
last configuration deliberately tested decomposition alone. The method is a
promising alternative for larger selected libraries, but it was slower on one
small weighted HMM problem. These are implementation comparisons, not evidence
that a native objective outperforms an intrinsic-reward baseline.

## Exact optimization problem and cut derivation

Fix a finite hypothesis class Q, a collection horizon t, and explicit target
experiments F_j. Every source and target kernel uses the same Q. A policy retains
its full action-observation history, and its acquired experiment has columns

    E_Q,h = p_Q(h) w(h),

where p is the supplied controlled-prefix behavior and nonnegative w is the
policy realization weight. Compact action-flow variables enforce a valid,
world-independent, randomized history-adaptive policy, including at histories
that have probability zero under the incumbent. The actual Q is not supplied to
the policy or decoder. The planner receives the candidate models.

For a fixed target F, the one-sided deficiency is

    delta(E,F) = min_G max_Q (1/2) sum_y |(E G)_Q,y - F_Q,y|,

where every row of G is a probability vector. Its finite LP dual, after
eliminating the source-column variables, is

    max_{alpha,b}  sum_Q,y F_Q,y b_Q,y
                  - sum_h max_y sum_Q E_Q,h b_Q,y,

subject to alpha >= 0, sum_Q alpha_Q = 1, and 0 <= b_Q,y <= alpha_Q.
The orientation is source E to target F: the decoder transforms acquired data
into the target's output distribution. This dual follows by taking a convex
mixture of the world-specific TV tests and minimizing the resulting linear form
over each stochastic decoder row. Equivalently, it is the existing decoder LP
with its free s variables eliminated. No interchange of policy minimization and
an adversarial maximum is needed.

For any feasible alpha,b, nonnegativity of w gives the globally valid cut

    delta(p w,F) >= <F,b> - sum_h w(h) c_h(b),
    c_h(b) = max_y sum_Q p_Q(h) b_Q,y.

The maximum's argument depends on the supplied behavior p, not on the policy.
Each w(h) is one terminal action-flow variable, so collecting coefficients of
repeated terminal variables gives an affine inequality in the compact master.
**The coefficient must be computed for every syntactic terminal history.**
Dropping columns with zero mass under the incumbent would make the cut invalid
for another collector that reaches those histories. The decoder may omit zero
columns internally; `make_cut` reconstructs its coefficients from the complete
raw behavior array.

For a nonnegative weighted objective, the master has one epigraph d_j per target
and minimizes sum_j lambda_j d_j. For minimax, one common epigraph d bounds every
target's cuts. The source-flow variables and epigraphs have bounds [0,1]. The
latter bounds are harmless because a deficiency is at most one. Empty libraries
and negative or nonfinite weights are rejected.

Every master optimum supplies a global lower bound for this **fixed library**.
Replaying its policy and independently solving the target decoders supplies a
feasible upper bound. We add violated dual cuts and stop when the best upper
minus best certified lower is at most 2e-7. A timeout, unsuccessful LP, or
nonclosing gap remains incomplete or failed; it is not relabeled optimal.
The cuts are valid regardless of whether they separate the incumbent exactly.
Exact optimal separation and an appropriate finite polyhedral implementation
support the standard finite LP cutting-plane argument; this pilot does not
claim a favorable worst-case iteration bound.

This is a finite optimization derivation and new implementation. It is not a
new manuscript theorem or a Lean formalization. Certificates use floating-point
arithmetic with explicit residual checks and repaired witnesses, not rational
proof objects.

## What the pilots measured

The first fixed grid uses three existing families: asymmetric sensors
`sensors_0.1_0.3`, symmetric irreversible choice
`irreversible_0.1_0.1`, and `hmm_91501_0.2`. Collection always has t=3. The target
libraries have (n=2,K=8), all deterministic depth-two trees, and (n=3,K=16), the
eight fixed action sequences followed by a prespecified permutation with seed
923230. Both the weighted average and minimax objective are tested. Two extra
cells use all 128 depth-three trees on the HMM. Libraries and uniform weights
are frozen before each grid executes.

Following that grid, two authorized probes use t=4,n=3,K=128: HMM91501 with both
planners and HMM91502 concentration 1.0 with decomposition alone. The latter's
supplied T/Z arrays match the failed campaign pilot's model exactly. All 128
equal-weight trees constitute the same objective as its complete structured
library with seed 923101. Our complete-library enumeration is ascending target
ID rather than that pilot's structured order; this cannot change the objective,
but solver timing should not be described as using an identical iteration order.

For each decomposition, the timed interval includes master matrix construction,
LP solving and certificate checks, policy replay, decoder construction, every
selected-target decode, cut construction/checking, and cut insertion. For the
monolithic planner it includes construction, solving, certificate checks, replay,
and a new independent decode of all selected targets. Shared model geometry and
library construction are recorded separately. Certificate serialization is
measured separately and excluded from both comparison times.

The initial `results/` attempt accidentally included monolithic certificate
export in its comparison time while excluding decomposition export. It is
preserved with its exact source snapshot. **Use `results_fair_timing/` and
`results_extra_t4/` for timing comparisons**, not that preliminary ratio.

Each planner has a 40-second solver/iteration budget. The monolithic limit is its
solver time limit, so surrounding construction/verification can extend wall
time; failed attempts retain their wall time. One CPU is pinned for planning,
BLAS/OpenMP threads are set to one, and each pilot process enforces a 2GiB address
space limit. Arithmetic auditing uses one other pinned CPU at most. The three
pilot executions, including the preserved preliminary run, took about 247 seconds
in total; no further probes were launched. Peak process RSS was below 965MiB in
all three runs. This is process-level high-water memory, not isolated memory per
planner. One timing repeat is not a statistical performance benchmark, and the
shared machine was also running other work.

## Results and unfavorable cases

The complete 16-row comparison is in `SUMMARY.csv`. Representative corrected
times below exclude certificate export and include selected-target verification.
Every row uses n=3 except the explicitly marked small counterexample.

| Case, objective | t / K | Decomposition seconds | Monolithic seconds | Master variables | Iterations | Final gap |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| HMM91501, weighted, n=2 | 3 / 8 | 0.259 | 0.163 | 50 | 13 | 1.97e-7 |
| HMM91501, weighted | 3 / 16 | 0.336 | 1.467 | 58 | 8 | 9.68e-14 |
| HMM91501, minimax | 3 / 16 | 0.487 | 1.175 | 43 | 10 | 3.68e-14 |
| HMM91501, weighted | 3 / 128 | 2.239 | timed out at 40 s | 170 | 10 | 1.37e-12 |
| HMM91501, minimax | 3 / 128 | 2.004 | 31.388 | 43 | 9 | 8.56e-14 |
| HMM91501, weighted | 4 / 128 | 9.710 | timed out at 40 s | 298 | 11 | 9.62e-9 |
| HMM91502, weighted | 4 / 128 | 17.933 | not run | 298 | 13 | 1.60e-7 |

The n=2 HMM weighted case is slower under decomposition, and its minimax case is
essentially tied (0.190 versus 0.189 seconds). Preserve those results. Across the
six K=16 cells, decomposition takes 0.074–0.487 seconds versus 0.784–1.692 for the
monolithic comparator. These are matched objective solves, not a change of
optimization target.

At t=3,K=128, the minimax master uses 43 variables versus 69,803 in the monolithic
LP; weighted uses 170 versus 69,802. At t=4,K=128, weighted uses 298 master variables
rather than the monolithic formulation's 266,538. The separate decoder LPs still
exist and their costs are charged; the reduction is in the *joint planning*
problem. Final cut counts are 499 and 910 for the t=3 full-library minimax and
weighted cases, and 968/1173 for the t=4 weighted probes.

The t=4 numerical objective intervals are:

- HMM91501: [0.030071928787009736, 0.030071938398982777].
- HMM91502: [0.015187220739322396, 0.015187379769563760].

A monolithic timeout does not establish a different optimum. The decomposition
is independently bounded by its master and feasible decoders even where that
comparison is unavailable. It also does not imply that either HMM is a useful
paper experiment; this pilot addresses computation alone.

## Independent verification and source provenance

`audit.py` imports neither planner nor decoder. For all 16 corrected/extra cells,
it independently:

1. Computes controlled-history probabilities from the archived T/Z arrays and
   reconstructs every selected target tree's law.
2. Replays the full source policy, checking row normalization and acquired laws.
3. Rebuilds every saved cut from its alpha,b witness, including all histories,
   and checks it on a different deterministic policy.
4. Binds the saved master matrices to the actual flow constraints and cut prefix,
   then recomputes primal residuals and the finite-box Lagrangian lower bound.
5. Recomputes original-source TV errors and dual values from every saved decoder,
   checks closed optimization gaps, and checks available monolithic certificates
   and overlap with the decomposition interval.

Both independent audit reports pass. Maximum saved-arithmetic residual is
8.69e-11 for the 14 t=3 cells and 3.02e-10 for the two t=4 cells. The stopping gap is
a separate quantity; its largest accepted value is about 1.97e-7. No solver
failure or timeout was discarded.

`DEPENDENCIES.json` records the exact frozen copies under `deps/` of
`scaling_core.py`, `fast_decoder.py`, and `certified_decoder.py`. The parent later
added input guards to its active decoder; that file is not imported here.
`experiment.py` supplies its own original-E/F validity guards. The copied core's
old model-loading helper is deliberately unused because its relative path would
change on relocation; archived arrays are loaded explicitly instead.

Each result directory's `design.json` binds source hashes, dependency hashes,
input case selection, horizons, target IDs/seeds, resource limits, and package
versions. Input NPZ hashes are in each comparison. The preliminary implementation
is retained as `experiment_initial.py.snapshot`; the corrected implementation
is also frozen as `experiment_fair_timing.py.snapshot`. Their hashes match the
recorded launch hashes, and current `experiment.py` matches both corrected runs.
All changed sources and newly written artifacts remain inside this directory.

## Implementation interface and reproduction

`decomposed_plan(g, targets, kind, time_limit=40, max_iterations=200, gap=2e-7)`
returns `(best, report, cuts, master_arrays)`. `best` contains the replayed source
kernel, conditional policy rows, leaf weights and selected-target decoder
witnesses. `kind` is `native_weighted` or `native_minimax`; each target supplies a
kernel and nonnegative weight. The geometry is the frozen core's binary-action,
binary-observation, full-history geometry. A near-optimal reward constraint is
not implemented in this bounded prototype.

Reproduce from the repository root with the existing CPU environment:

```bash
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 \
  /tmp/exploration-lp-cpu-venv/bin/python \
  Paper/research/target_selection_2026-09-23/decomposition_research/experiment.py \
  --pilot --output /tmp/decomposition_reproduction

OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 \
  /tmp/exploration-lp-cpu-venv/bin/python \
  Paper/research/target_selection_2026-09-23/decomposition_research/audit.py \
  /tmp/decomposition_reproduction
```

`--extra-t4` runs only the two explicitly listed additional probes. Use a fresh
output directory to preserve these evidence artifacts. Importing the prototype
inside an already running worker with a different `scaling_core` in
`sys.modules` would not establish the frozen dependency binding; a separately
launched process or an explicit dependency-injected integration is required.

## Recommended next scaling tier

Keep the live monolithic campaign frozen. A separately authorized next tier can
compare this backend with that frozen implementation on identical classes,
policies, target IDs/weights, tolerances and acquisition horizons. Include the
small cases where decomposition loses, not only the promising full-library HMM.
Use the existing 22 classes and K grid at t=3 for paired objective/certificate
checks, then the already selected four-step classes at K=128. Add the fresh
larger-world classes before claiming that the improvement transfers beyond the
four-world examples. Prespecify per-cell time/RSS caps and preserve all failures.

Measure total time to a certified selected-library optimum separately from total
time to the full evaluation audit. Persistent master updates, reuse across
nested libraries, and cut pruning are potential implementation improvements,
not tested claims. A reward-face constraint is linear in the same flow and can
be added, but its numerical tolerance and certificate need independent tests
before substituting this implementation for the campaign's favorable-selection
arms.

Decomposition does **not** supply a new hardest-target oracle. Every iteration
here visits the explicit K targets. For n=4 there are 32,768 deterministic trees;
full separation or held-out evaluation still incurs that target search. Extending
collection t also grows the complete source history tree and the decoder LPs.
Thus a t=5 or n=4 tier should follow the paired validation, retain bounded partial
outcomes, and report acquisition and computation budgets separately.

The all 128 minimax objective covers the finite depth-three worst deterministic
target audit, with the existing recorded-mixture reduction interpreting adaptive
randomized targets. The equally weighted all 128 objective is a different finite
scalar tradeoff. Neither is the eventual infinite-rich J_w, and neither finite
result establishes Blackwell dominance or complete exploration.
