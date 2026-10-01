# What the saved evidence supports for adaptive native weights

23 September 2026. This is a synthesis of compact saved reports for the adaptive-weight research assignment. It introduces no new optimization run, policy audit, benchmark, training result, or formalization. The [input manifest](EVIDENCE_INPUTS.json) records SHA-256 hashes, byte counts and arithmetic summaries for the fourteen inspected assignment/evidence sources. The prior reports' numerical certification claims are attributed to those reports; their original certificates were not rerun here.

The evidence supports testing adaptive weighting and a smaller optimization backend as separate research questions. It does not establish that changing weights improves exploration. The smaller backend has already solved some large finite problems much faster, while fixed native objectives have both beaten and lost to strong posterior objectives. The next study should preserve that distinction and explicitly allow either track to fail.

## The evaluated quantities

Collection length `t` is the number of interactions made by the collector. Target depth `n` is the length of a hypothetical native intervention that its record should simulate. Every decoder is randomized, target-specific and independent of the actual world; collector, target and decoder share the same supplied hypothesis class and controlled interface. The planner knows the candidate models, not which model generated the record.

The September 23 weighted objective is a finite average over a chosen library of deterministic target trees. Its complete depth-three reference has 128 targets. The worst-target audit is the maximum deficiency over all trees at the specified evaluation depth; there are 32,768 trees at depth four. Neither finite quantity evaluates the eventual rich score `J_w`. The latter includes a rich countable family, including rational randomized target policies, and takes an eventual collection-time limit in each coordinate. Finite target coverage, finite optimization error and eventual error are separate questions.

## Earlier results that remain constraints on the hypothesis

The [15 September benchmark](../native_objective_benchmark_2026-09-15/README.md) optimized one fixed 16-target weighted loss over all randomized history-dependent three-step collectors in ten prespecified cases. Its primary metric was the worst mean of seven decision accuracies over the near-optimal policy set, rather than the worst-target deficiency now proposed. The prespecified broad-benefit screen failed.

| Comparison with Brier | Native wins / ties / losses | Family-balanced change in decision accuracy |
| --- | ---: | ---: |
| Nominal zero regret | 0 / 5 / 5 | −0.278 percentage points |
| One-percent normalized regret | 0 / 1 / 9 | −0.684 percentage points |
| Five-percent normalized regret | 0 / 1 / 9 | −1.651 percentage points |

The corresponding zero-regret comparison with information gain was 2 wins, 4 ties and 4 losses. Its positive family-balanced mean does not erase the unfavorable case counts. These outcomes concern complete selected-policy envelopes under that study's tolerances, not arbitrary representatives. Changing the primary metric in a new study must be stated openly; a favorable new worst-target result would not retrospectively pass this decision-performance screen.

The [13 September noisy-diagnostic study](../noisy_diagnostic_transfer_2026-09-13/README.md) supplies a complementary warning. At four reads with sensor error .1, the worst parity accuracy among policies optimal for the single-sensor diagnostics was .805797; adding a joint target raised it to .82, and adding repeat targets raised it to .8776. Uniform-prior information gain also guaranteed .8776. The single-diagnostic value had been .82 at three reads: a larger feasible collector set admitted additional bad optimizers. This is not a loss of information when one fixed collector retains more observations. Its 54 optima and 930 purpose-envelope endpoints are finite acquisition evidence; the saved rational transfer certificates are a different evidence object from the floating-point policy programs.

These results justify retaining information and Brier, favorable near-optimal controls, omitted-target evaluation, and optimization-tolerance analysis. They do not justify selecting weights solely to defeat those controls.

## Partial target-selection campaign: positive and negative findings

The [12:09 UTC report](../target_selection_2026-09-23/interim_reports/2026-09-23_120905.md) observed 414 complete jobs, 14 failed and four running out of 1,368 registered jobs. Thus only 30.3% were complete, with 936 other jobs outside those three statuses. This is a frozen interim snapshot, not a current liveness or final-completion report. Resource-dependent completion may favor easier cases. The completed tiers were `(t,n)=(3,3)` and `(4,3)`; the reported four-step-target comparisons used three-step collectors. The longer-collection and depth-four-training extensions had not completed at that snapshot.

The following counts were recomputed from the compact JSON's saved interval pairs. Each environment is counted once within a comparison. A win requires the entire available arm interval to beat the entire baseline interval by more than `1e-6`; otherwise the saved tie convention applies. Different rows have different matched coverage. These are numerical comparisons, not significance tests or independent samples of natural environments.

| Arm versus baseline | Depth-three audit: wins / ties / losses | Depth-four audit: wins / ties / losses | Matched cases |
| --- | ---: | ---: | ---: |
| Uniform 128-target weighted versus Brier | 6 / 0 / 2 | 6 / 0 / 2 | 8 |
| Uniform 128-target weighted versus information | 9 / 0 / 0 | 9 / 0 / 0 | 9 |
| Full depth-three minimax versus Brier | 8 / 1 / 0 | 7 / 1 / 1 | 9 |
| Full depth-three minimax versus information | 10 / 0 / 0 | 10 / 0 / 0 | 10 |
| Uniform 128-target weighted versus old 16-target weighted | 6 / 2 / 3 | 5 / 0 / 6 | 11 |
| Full depth-three minimax versus favorable Brier optimum | 4 / 1 / 0 | 5 / 0 / 0 | 5 |
| Full depth-three minimax versus favorable information optimum | 5 / 0 / 0 | 5 / 0 / 0 | 5 |

The smaller coverage of favorable-optimum controls matters: those rows cannot replace a common-case comparison with default representatives. The controls minimize the depth-three native audit subject to the actual intrinsic-return threshold. Their four-step-target performance is then evaluated without having optimized that depth-four audit. Nominal exact-optimum rows include a separately reported `1e-10` reward slack; the registered near-optimal grid also includes one- and five-percent return-range regret. Favorable selection is neither a worst-over-optima envelope nor a training result.

Three concrete qualifications should survive every summary:

- **The ranking reverses with target depth.** In `delayed_0.25_0.1`, minimax has three-step error .085657516 versus Brier's .09375, but four-step error .166216724 versus Brier's .143238462. The first ordering follows the optimized criterion; it does not ensure longer-target superiority.
- **More targets can worsen worst-case capability.** In one symmetric irreversible structured-weighted curve, the worst error rises from .24072 at 16 targets to .472 at 32 and 64, then falls to .245689 at 128. Brier and minimax attain .236. Increasing a uniformly weighted library changes its priorities; it need not produce monotone improvement in a different audit. The full 128-target weighting loses to the old 16-target weighting in six of eleven available depth-four comparisons.
- **A default intrinsic optimizer can be unrepresentative.** On `sensors_0.1_0.1`, default Brier has error .084711758, while favorable Brier-optimal selection reaches .072, equal to minimax. A representative-policy gap cannot be presented as an all-optima gap.

Structured target selection closed the finite minimax certificate with fewer targets in 16 of 22 matched curves, with the same number in five, and in one case where random selection did not close. These curves span 14 model classes and repeat horizons/seeds within classes. Among the 21 pairs where both closed, median first-certified library size was eight structured versus 64 random. The saved planning time was nevertheless larger for structured selection in two of those 21 pairs. Target count is therefore not a substitute for charged wall time.

The fourteen failed jobs comprise ten GPU/CPU planner failures, three decoder-budget failures, and one CPU planner timeout. They are computation failures rather than unfavorable objective values. Earlier accepted checkpoints remain evidence, but failure to reach a planned endpoint must remain visible. The saved prelaunch review reports seven complete pilots and one failure, with 644 checks; its separate validation file reports 281 passed checks. This pass checked that saved accounting, not the underlying numerical witnesses.

All depth-four outcomes just inspected are **exploratory evidence for the new adaptive design**. Their original held-out status within the frozen campaign does not make them untouched confirmation for a method now designed from their results. Confirmation needs newly prespecified classes, targets or horizons, or a split whose outcomes genuinely remain unseen.

## Smaller linear programs: computation evidence only

The [frozen decomposition prototype](../target_selection_2026-09-23/decomposition_research/README.md) replaces one large joint linear program with a smaller policy program and repeated target-specific decoder programs. A decoder dual witness supplies an affine lower bound valid for every policy realization weight, including weights at histories unreachable under the current collector. Reusing those target bounds is the relevant computational opportunity when weights change. A new weighting still requires a fresh aggregate objective bound and a newly evaluated feasible-policy upper bound.

All sixteen configurations in `SUMMARY.csv` have saved optimization gaps at most `2e-7`; the largest is `1.9643884311901227e-7`. Thirteen have matching monolithic comparisons, two monolithic comparisons timed out, and one configuration used decomposition alone. The prototype's independent arithmetic reports are described by its README; this pass did not replay them. Floating-point residual checks are not exact rational certificates or Lean proofs.

| Case and finite objective | `t,n,K` | Decomposition | Monolithic | Interpretation |
| --- | --- | ---: | ---: | --- |
| HMM91501, weighted | 3,2,8 | .259481 s | .163398 s | Decomposition takes about 1.59 times as long. |
| HMM91501, minimax | 3,2,8 | .189722 s | .189364 s | Essentially tied; decomposition is slightly slower. |
| HMM91501, minimax | 3,3,128 | 2.003634 s | 31.388249 s | Saved monolithic/decomposition ratio 15.67. |
| HMM91501, weighted | 3,3,128 | 2.238848 s | 40 s solver timeout | No matched completed runtime ratio. |
| HMM91501, weighted | 4,3,128 | 9.709756 s | 40 s solver timeout | No matched completed runtime ratio. |
| HMM91502, weighted | 4,3,128 | 17.933270 s | Not run | No monolithic comparison in this probe. |

Times include policy-program construction, solving, witness checks, replay and all selected-target decoder work. Export is excluded consistently from the corrected comparisons. The initial unfair timing attempt remains archived and is not used here. These are one-repeat measurements on a shared machine; timeout budgets are not successful runtimes and process high-water memory is not planner-isolated memory.

At `t=3,K=128`, the weighted policy program has 170 variables versus 69,802 jointly, and minimax has 43 versus 69,803. At `t=4,K=128`, weighted uses 298 versus 266,538. The separate decoder work remains, as does exhaustive auditing over omitted targets. These dimensions justify a controlled backend comparison, not a claim that eventual `J_w` has become efficiently computable. The prototype does not implement the favorable reward-face constraints; posterior information and Brier already have finite-history dynamic programs.

## Consequences for the next protocol

The evidence supports a two-part protocol. First compare solvers on exactly the same finite objective, including the small slower case, all attempted cases, repeated timings and total certification cost. Then hold the implementation and acquisition budget fixed while comparing fixed weights, tractability-driven weights, difficult-target weights and direct minimax. The old weighted objective and information/Brier controls should remain common anchors. Adaptation and hardest-target search consume part of the method's computational budget.

Retain a fixed independent audit even when the training weights move. Publish both the final-weight objective interval and that audit; neither can replace the other. Use a common case list, explicit failed/incomplete endpoints and paired case coverage before aggregation. Weight adaptation should be allowed to show cheaper certification with unchanged or worse capability, and hard-target adaptation should be allowed to lose on longer targets or to favorable posterior controls. Those are distinguishable, scientifically useful outcomes.

No removed ICM/RND condition should return through this protocol. The campaign's empirical observation-label entropy is also not the paper's genuine discounted state-occupancy entropy. Exact Bayesian raw-observation loss and posterior Brier gain remain different objectives, and the finite campaign returns do not optimize the complete Bayesian alarm returns.

## Supplement: 13:43 UTC figure assessment

The later [figure assessment](../target_selection_2026-09-23/interim_reports/2026-09-23_figure_assessment/ASSESSMENT.md) was supplied after this note's original analysis. Its compact README, assessment, results and recovery plan were read; its analysis, plots and certificate checks were **not** rerun here. Their hashes are recorded separately in EVIDENCE_INPUTS.json, preserving the original 12:09 snapshot and derived summaries above.

The newer evidence supports the same two-track recommendation. At its 13:43:37 snapshot, depth-three minimax beat default Brier on eleven of thirteen available depth-four pairs, with one tie and one loss; weighted128 had ten wins, one tie and two losses. Only seven classes had all four core methods, so these differing pair counts do not constitute a complete common-cohort comparison. The larger weighting still lost to the old 16-target weighting on seven of thirteen cases. The report also preserves the delayed reversal, baseline successes and favorable optimal-face controls. These outcomes remain exploratory evidence for adaptive methods designed after seeing them.

Three operational qualifications matter for the next protocol. First, the frozen queue intentionally gives the 1%/5% information/Brier controls **no depth-four audit**; waiting for completion will not supply that evidence. A future audit extension should evaluate their saved policies and retain their training-horizon selection rule. Second, all four held-out decoder failures have their original K=128 selected policies saved; recovery should reuse those policies and diagnose the decoder failure, without reoptimizing or counting the recovered policy twice. Third, the reported native planning times cover target-selection curves, whereas Brier uses a much cheaper dynamic program. They reinforce charging computation separately from acquisition length; the smaller-LP prototype has not yet established those campaign-wide savings.

The detailed comparison and recovery work remain owned by the originating session. This supplement imports their scientific implications without duplicating that analysis, changing the frozen queue, or recommending manuscript adoption before its independent validation.

## Supplement: selection among native objective optima

The subsequently supplied [all-case saved-policy check](../target_selection_2026-09-23/interim_reports/2026-09-23_optimum_selection/README.md) changes the interpretation of some representative-policy losses, without changing the registered outcomes. In the symmetric irreversible case, the saved Brier and minimax policies have full weighted-objective regret upper bounds below `9e-15`, yet held-out worst error `.236` rather than the weighted representative's `.2456890466`. Thus this example does not establish a necessary conflict between weighted and minimax optima. The equality is numerical to the saved tolerances, not an exact proof or a characterization of the whole optimal face.

The source checked all 695 available candidate/objective pairs and found four minimax classes with analogous better-transfer alternatives. Those are correlated saved candidates, not a search over every optimum; unflagged cases may also be selection-sensitive. The delayed-case Brier alternative is different: its saved native training regret is materially positive, so that particular alternative is not an equal-optimum explanation. Neither observation resolves all possible optima in that case.

For adaptive weights and backend reuse, the implication is precise: matching certified objective values can establish numerical formulation agreement while warm-start paths select different approximate optima. Held-out changes must therefore be reported separately from objective-equivalence checks. Prospective training-only secondary selection for native weighted and minimax objectives is now specified in PROTOCOL.md, with its first-stage certification error charged and untouched evaluation required. The source README was read and hashed; its analysis and certificates were not rerun here, and no saved policy or result was substituted.

## Work performed in this pass

One serial Python-standard-library helper hashed the fourteen compact sources, counted the sixteen prototype configurations, recomputed all fourteen saved comparison-group classifications without disagreement, and summarized coverage, target selection and saved validation metadata. It consumed **0.019603 seconds wall time, 0.004518 seconds CPU, and 16,948 KiB peak RSS**, under five-second CPU/wall and 256 MiB address-space limits. Manual review subsequently distinguished the three decoder timeouts from the one planner timeout in the manifest. No NumPy/SciPy import, solver call, bulk-certificate scan, active-source modification, audit rerun, training, or build occurred. All numerical equivalence and fresh-performance validation for a new adapter remain deferred.
