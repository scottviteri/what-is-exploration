# Target-selection follow-ups — 23 September 2026

the lead author authorized these follow-ups after the eight-hour campaign. This directory preserves the original run and handles its missing comparisons, failed evaluations, and the separately recorded near-optimal evaluation extension. [PROTOCOL.md](PROTOCOL.md) states the scope, current objective-source decisions, numerical recovery change, and resource limits.

**Completed primary comparison:** [PRIMARY_COMPARISON.md](PRIMARY_COMPARISON.md) records the full 22-class main comparison and its exceptions; the separate near-optimal extension is not folded into that checkpoint.

**Current results:** [STATUS.md](STATUS.md) and [COMBINED_STATUS.json](COMBINED_STATUS.json) are maintained automatically. Only results with completed numerical-certificate checks enter the combined comparisons. The six current figure methods are uniform, full-world information, posterior Brier, categorical pseudo-count, finite weighted native, and finite minimax. Historical predictive and label-entropy results remain in the original archive.

## Completed independent archive audit

[original_audit/SUMMARY.json](original_audit/SUMMARY.json) passed all **976 recorded runs**, including accepted checkpoints from failed and interrupted runs. It checked:

- 2,495 acquired-policy checkpoints, with an independent latent-state recursion;
- 2,160 compact master LP certificates, rebuilding their matrices and checking feasibility, dual signs, stationarity and the bounded-domain dual correction;
- 5,968 retained original-source decoder/decision-loss witnesses;
- arithmetic and coverage for 16,342,912 per-target profile entries;
- Bellman-optimal reward values and allowed objective regret where applicable.

The audit invoked no optimizers and took approximately five minutes on one CPU. Every cell has a separate verification record. These are floating-point checks. The original archive saved only the hardest-target and full-revelation decoder witnesses, not the decoder for every profile entry, so this is not a fresh independent reconstruction of every old target solve.

## Follow-up execution

- **17 original registered jobs:** six missing information/Brier cases; seven nominal favorable-face controls; two uniform cases; two categorical-count cases. Two CPU workers, four GiB each, two-hour cap. The completion script and objective definitions are unchanged. Results are independently checked by `audit_completion.py` after this queue ends.
- **Ten interrupted/failed held-out audits:** five distinct exact acquired experiments, with all alias hashes recorded. Policies are reused unchanged. The new decoder saves and independently checks every one of the 32,768 target witnesses. Two other CPU cores, four GiB each, one-hour queue cap. The original failed attempts remain unchanged.
- **70 existing near-optimal controls:** the separately recorded n=4 evaluation of all available certified t=3 policies at 1%/5% information/Brier regret. No policy reoptimization. These jobs reuse the recovery cores only when recovery has finished, with a four-hour cap and six-GiB output limit. Eighteen of the 88 originally registered control policies were not available at the cutoff; they are not silently filled or selected by outcome.

The recovery probe passed on the affected policies and on all 128 depth-three targets of the saved favorable-Brier policy. Completed recovery/extension sweeps require `INDEPENDENT_CHECK.json`, which recomputes every upper and lower bound from the stored decoder and bounded decision-loss witness using the original experiment. The tolerance remains 2e-7. LP diagnostics and failed solver attempts remain recorded separately from this direct certificate.

## Files and ownership

- `completion_manifest.json`, `recovery_manifest.json`, `near_optimal_manifest.json`: precise job and source bindings.
- `COMPLETION_LAUNCH_RETRY.json`, `RECOVERY_LAUNCH.json`, `EXTENSION_DISPATCH.json`, and `EXTENSION_EXECUTION.json`: process/resource provenance and actual stage state.
- `MONITOR.json`: the lightweight validation/summary process. It launches no extra optimization beyond the registered queues.
- `completion_results/`, `recovery_results/`, `near_optimal_results/`: separate new output trees. The latter two retain complete per-target witness batches.
- `original_audit/`, `completion_audit/`: verification records.
- `combined_figure_data.csv`: current verified values for the six-method comparison, with original cell IDs.
- `FOLLOWUP_FIGURE.pdf` and `FIGURE_CAPTION.md`: a candidate empirical comparison and its exact interpretation; these are research outputs, not manuscript edits.
- `FINAL_SUMMARY.md` and `FINAL_SUMMARY_HASHES.json`: produced automatically after all registered queues stop, including any failures or gaps.
- `REPORTING_RESTART.json`: provenance for a reporting-only restart to make the figure read one consistent summary snapshot; numerical jobs were unchanged.

The first completion supervisor attempt rejected a command-line option before starting any jobs. Its command and log remain visible; the corrected launch uses the required positional manifest.

No original result, manuscript, shared formal ledger, Git history, or Overleaf project is modified by this work. Live queues, reports and witness batches should not be staged as an immutable release package while writers remain active. The small source files and manifests describe ongoing research, not a claim that every queued job has finished.

## Runtime CPU-affinity coordination

At 19:58 UTC on 23 September, owned workers moved from logical CPUs 3/4 to 10/11 at the request of the concurrent exhaustive-audit task. `AFFINITY_OVERRIDE_2026-09-23_195815.json` records the initial thread changes. `CPU_AFFINITY_GUARD.json` and `CPU_AFFINITY_EVENTS.jsonl` record the lightweight watcher that also moves future queue workers after their original taskset commands execute (up to a brief startup interval before the next 0.1-second scan). Supervisors and verification/report children use 10/11 as well. Frozen sources, manifest, wall caps and numerical tolerances stay unchanged; process.json retains the original launch affinity, and the override log gives the actual later affinity.

The container has a shared cgroup-v1 quota of **10.2 CPU-equivalents**, irrespective of its 96 visible logical CPUs. These two evaluation workers request **two CPU-equivalents** within that shared budget. Moving their affinity prevents sustained overlap on CPUs 0–9 but does not remove aggregate quota contention; eight concurrent audit workers plus these two workers fit the nominal quota with little headroom. Timing comparisons remain measurements on a shared container.
