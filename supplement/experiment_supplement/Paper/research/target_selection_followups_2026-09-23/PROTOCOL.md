# Authorized follow-ups after the capped target-selection run

the lead author authorized these follow-ups on 23 September 2026. The original run and its frozen report remain immutable. This directory holds new evidence and original-job recovery; it does not change the manuscript, formal ledgers, intrinsic formulas, original numerical tolerances, or original outcomes.

## Scope and current source decisions

1. Independently reconstruct all retained original policy/master certificates and saved hardest/revelation decoder witnesses, including accepted checkpoints in failed/interrupted cells. Do not imply that an unsaved decoder witness has been independently reconstructed. Audit archived objectives regardless of their outcomes or current paper inclusion.
2. Complete the six missing information/Brier jobs, seven not-yet-run nominal favorable-face jobs, two uniform jobs and two categorical-count jobs. These seventeen jobs retain the original manifest's definitions, models, priors, policies, horizons and target sets. The remaining nominal-face failure and two interrupted uniform audits are handled by policy reuse.
3. Recover ten failed/interrupted held-out audits from their original saved policies. Six are byte-identical acquired experiments in the same byte-identical model, so five distinct evaluations suffice. Bind every alias's policy/model/experiment hashes. Retain EVERY newly calculated decoder and decision-loss witness so the complete new audit can be independently replayed.
4. Separately evaluate all available certified 1%/5% information/Brier control policies at n=4, keeping their original t=3 policies fixed. This is an evaluation extension absent from the original queue. Selection is by availability/certification, not outcome. Missing original control policies remain missing; this extension does not silently retrain them.

The current selected paper removed the predictive surprisal, categorical next-observation square loss, and predictive-coordinate variance comparisons. See `../predictive_source_fidelity_2026-09-23/README.md`. The new completion queue therefore omits the seven pending predictive-loss jobs in the older plan. Archived data/proofs stay intact, and source correspondence is not repaired by renaming an objective. Neither empirical label entropy nor observation occupancy is presented as physical-state entropy. Full-world information and posterior Brier remain the core comparisons; Brier is a declared posterior reference score, not Brier's RL algorithm.

The retained categorical density/count bonus is the original add-one categorical predictor with reward 1/sqrt(1+N(o)), on raw observation labels. Bellemare et al.'s original Sections 3.1 and 4 explicitly supply Dirichlet pseudo-counts and inverse-square-root bonuses; it is not their CTS implementation or the stabilizer used in that Atari implementation. The original finite return and density-update timing are unchanged.

## Numerical recovery change

The original decoder required a small LP KKT residual as well as a tight original-source interval. One retained failure has a marginal stationarity residual just above tolerance despite a much tighter feasible deficiency interval. Other retained attempts exhausted their simplex call limit.

The new recovery backend records LP diagnostics but accepts an interval only from two explicit objects: a nonnegative row-stochastic decoder G, giving max_Q TV(E_Q G,F_Q), and alpha >= 0 with sum alpha=1 and 0 <= b_Qy <= alpha_Q, giving

    sum_Qy F_Qy b_Qy - sum_x max_y sum_Q E_Qx b_Qy.

Both quantities are computed on the ORIGINAL acquired experiment. Their difference must be at most 2e-7. This does not infer accuracy from a solver's success flag or silently raise the deficiency tolerance. It changes the numerical certification route and is labeled as a new backend; the old failures remain failures. Floating-point checks are not exact-arithmetic or Lean proofs.

Retained simplex, cold simplex, then cold interior-point attempts share a 30-second call budget, with one/three-second limits on the first two attempts. Tiny-column merging follows the original bounded garbling and lifts the decoder back to every original positive-probability column. Failed attempts and stationarity diagnostics remain in each result.

The small recovery probe checked the affected policies and completed all 128 n=3 targets for the favorable Brier failure. The independent checker recomputed every new decoder/decision bound using the original source and a separate target-generation route. Full n=4 sweeps are verified after completion; a probe is not their verification.

## Resources and provenance

The saved-certificate audit used one CPU, a 5-GiB process cap and a 90-minute wall cap; it finished in approximately five minutes. Completion uses two CPU cores with 4 GiB per worker and a two-hour cap. Recovery uses two other CPU cores, 4 GiB per process, a one-hour queue cap and at most 25 minutes per policy. No GPU is used. The near-optimal extension reuses the recovery cores only after that queue and its workers have stopped, with a separately recorded manifest and budget.

Source hashes bind the original code and each new recovery executable. The first completion launch failed argument parsing before starting any job; `completion_supervisor.log` and `COMPLETION_LAUNCH.json` preserve it, and the positional-argument correction is recorded in `COMPLETION_LAUNCH_RETRY.json`.

A new result does not overwrite an old result or quietly replace its selected optimum. Comparisons must retain original versus recovered/new provenance, all losses, the delayed-horizon reversal, tied-optimum sensitivity, remaining coverage, and computation costs. New source/summary files are confined to this directory. No commit, push or Overleaf export is authorized by this follow-up task.

### Near-optimal extension registration

`near_optimal_manifest.json` selects all seventy available, numerically certified information/Brier policies at normalized objective regret .01 or .05 from the capped snapshot. All have t=n=3 and no original n=4 audit. The other eighteen originally registered policies are unavailable. There are seventy distinct acquired experiments, so no duplicate-policy saving is assumed for this extension. Evaluation begins automatically only after the recovery queue releases CPUs 3 and 4, with a four-hour cap, 4 GiB per worker, a 6-GiB output cap and a 15-GiB disk reserve. Each result is independently checked before entering the live combined comparison. No future publication, full-grid completion, or favorable outcome is presumed.

### Timing-only diagnostic after the main comparisons completed

One uniform-policy recovery (`cell_1009`) became substantially slower on later target trees. `TIMING_PROBE_UNIFORM.json` records a bounded CPU-4 timing probe of eight preselected target indices, using the unchanged source experiment and the same original-source interval checks. Retained simplex took 4.197 seconds in total and cold interior point took 1.989 seconds (2.11 times faster on this small probe); every interval passed. This is not an all-target runtime estimate or a general solver speedup. The probe did not alter active workers, their source hashes, target coverage, policies, or declared time limits. It is a candidate for a later explicitly recorded recovery backend if needed.
