# Adaptive native-objective backend validation

23 September 2026. This executes the previously prepared numerical bridge in a
new directory, preserving the frozen adaptive-weight package, model archives and
all older failures. The study compares implementations of finite objectives. It
does not test sampled-policy learning or establish efficient optimization of the
full eventual native objective.

## Completed result

All 285 registered endpoints are recorded. There are **276 converged numerical
optima and nine preserved monolithic solver timeouts**; no endpoint is missing.
The complete run took 614.5 seconds on four pinned CPU workers. All 120 available
matched-objective comparisons agree within 1e-6. The independent arithmetic
checks pass; their largest residual is 2.64e-9. Timeout input files also pass their
geometry checks, which do not turn those failures into optima.

The smaller LP is useful but not uniformly faster. On the small HMM weighted
case (t=3,n=2,K=8), median monolithic/decomposition/cold-bridge times are
0.338/0.560/0.870 seconds. On its full depth-three minimax case, medians are
31.967/2.493 seconds. All three monolithic repeats time out on each of the three
large weighted configurations; both decomposition implementations converge.

Returning to the final uniform objective after retaining cuts is faster than its
cold bridge solve in 53 of 54 paired runs. This is **incremental** reweight cost;
it excludes the earlier cache-creation solves, which are recorded and must be
charged before making an amortized application claim. No depth-four capability
ranking is inferred from these implementation comparisons.

[CHECKS.json](CHECKS.json) records completed validation and integrity checks.
The full witness archive is approximately 1.60 GB; no files were committed or
pushed. Raw outcomes remain separate from compact analysis and code.

## Registered study

[QUEUE.json](QUEUE.json) freezes the source hashes and all 48 case/repetition
records before substantive timing outcomes. The cases are the complete 16-cell
archived decomposition grid, including its slower small HMM case and both
four-interaction probes. Each is run three times. Method order rotates across
repetitions, with the core comparisons completed before the retained-cache paths.
Four workers are pinned to CPUs 4–7 with one solver/BLAS thread and a 4 GiB address
space limit each. Every solver gets 40 seconds; a process watchdog caps each
planning/selected-decoder attempt at 65 seconds. The selected convergence gap is
1e-6 for all methods. Numerical witness residual tolerance remains 2e-7.

All 16 configurations compare the original simultaneous LP and original
cut-decomposition LP. The nine weighted configurations additionally use the new
bridge from an empty cache, and two retained-cache sequences:

- uniform coefficients, increasing coefficients proportional to 1,...,K, uniform;
- uniform coefficients, decreasing coefficients proportional to K,...,1, uniform.

Weights are exactly normalized rational numbers; target identities never change.
There are 177 method processes and 285 planned endpoints. Returned policies and
all objective witnesses are saved, including every intermediate master and decoder
round. Failed solves remain failures, even when their input-geometry audit passes.

The bridge's intermediate nonuniform solves have independent numerical bounds.
There is no matched cold nonuniform solve in this queue, so this study compares
final uniform-objective reweight cost, not a complete cold-versus-warm path timing.
Nested target-library expansion, secondary selection and favorable reward-face
constraints are outside this backend study. The archived K=8/16/128 configurations
are not a nested adaptive library-expansion experiment.

## Independent verification

[backend_api.py](backend_api.py) exports actual model arrays, source and target
laws, policy rows, every master matrix/primal/dual, each master cut prefix, all
original cut witnesses, the selected decoders, objective and cache identities, and
timing records. [independent_audit.py](independent_audit.py) imports no planner,
decoder or adapter code and performs no optimization. It reconstructs controlled
history probabilities, target laws, policy flow and replay, cached cuts including
unreachable incumbent histories, every master matrix, and numerical LP bounds.
[monolithic_structure.py](monolithic_structure.py) independently rebuilds the
simultaneous policy/decoder formulation. Every checked decoder is evaluated on
the original source probabilities.

The analytic read-bit tests exercise zero/tiny weights, reordered targets,
duplicate-encoding rejection, and missing/corrupt cached witnesses. Literal
rational randomized full-history targets are separately checked, including exact
selected-background coefficients and omitted mass in [rich_audit.py](rich_audit.py).
Four deliberately corrupted artifacts must be rejected: controlled probability,
master cost, decoder normalization and cached dual. These checks and the frozen
package's 16 solver-free tests are preserved alongside their reports.

All numerical bounds retain their floating-point scope. Rational coefficient
bookkeeping and explicit residual checks are not exact rational optimization
certificates or Lean proofs. No finite objective gap is converted into eventual
regret or sufficiency.

## Results and reproduction

[RESULTS.csv](RESULTS.csv) contains every endpoint; [ANALYSIS.json](ANALYSIS.json)
contains complete accounting, paired objective comparisons, timing medians and
missing/failure lists. [RUN_COMPLETE.json](RUN_COMPLETE.json), when present,
records the completion boundary. Per-process and per-endpoint logs preserve all
attempts. Numerical comparison uses 1e-6, and a timeout is not a runtime to optimum.

Internal computation times include solving, replay, selected-target decoding and
cut operations. Geometry construction, artifact export, independent scientific
checking and process startup are also saved separately. The bridge's internal
timer begins after its source-lock/context checks; per-process wall times retain
that overhead. Consequently internal timings alone should not be described as
complete end-to-end application time. Cache creation and preceding reweighting
cost are retained in each path's selection provenance.

An identified metadata issue is corrected explicitly in
[OBJECTIVE_ID_CORRECTION.json](OBJECTIVE_ID_CORRECTION.json): the initial worker
assigned a weighted-objective identity to original minimax metadata. Its actual
minimax objective, LP matrices and audit were correct. Raw files remain unchanged;
derived analysis uses a kind-bound scientific identity for every method. This
correction changes no policy or computed value.

The exact queue can be rerun only into a separately named result directory; the
current runner paths identify this completed evidence. Do not overwrite them.
To use the validated helpers in another directory, import `backend_api`, call
`bootstrap()` before importing NumPy-dependent auditors, and then use
`export(backend, folder, geometry, targets, model, metadata, result)` followed by
`independent_audit.audit(folder)`. Metadata specifies collection time, objective
kind and exact weights, target bindings, and either deterministic target indices
or literal rational target encodings. For a rich truncation also call
`rich_audit.check_rich(folder)` with its epsilon and adaptive weights. Reward-face
or other extra master constraints need a separate audited extension.
