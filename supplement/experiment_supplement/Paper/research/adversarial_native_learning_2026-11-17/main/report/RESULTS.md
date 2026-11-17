# Finite adversarial target-search pilot

Run phase: **frozen paired pilot; main results**.

Input status: complete; complete analyzed runs: 72/72.

This report retains every registered seed and lists missing or invalid records explicitly. All three environments were chosen during design. This is model-based training from labelled, resettable-world samples, with no out-of-class validation. The numerical audits are finite LP evaluations, not formal proofs.

The collector's per-action probability floor is **0.005**. Both unrestricted and floor-matched reference optima are reported. Main methods have matching candidate and collector budgets; wall time is measured rather than matched. The all-targets diagnostic fits more decoders and is not an equal-compute competitor.

## References

| Environment | Unrestricted lower–upper | Action-floor lower–upper |
| --- | ---: | ---: |
| Compatible readings | 0.000000000–0.000000000 | 0.007481247–0.007481250 |
| Irreversible choice | 0.249999998–0.250000000 | 0.251249998–0.251250000 |
| Noisy readings | 0.077608694–0.077608696 | 0.077996338–0.077996340 |

## Final outcomes

| Environment | Method | Runs | Mean true worst error | Root-noise probability | Noise-action fraction |
| --- | --- | ---: | ---: | ---: | ---: |
| Compatible readings | Learned proposals + hardest | 6/6 | 0.007483 | 0.005000 | 0.005001 |
| Compatible readings | Uniform proposals + random | 6/6 | 0.008080 | 0.005005 | 0.005169 |
| Compatible readings | Uniform proposals + hardest | 6/6 | 0.007485 | 0.005000 | 0.005002 |
| Compatible readings | All targets (extra decoder work) | 6/6 | 0.007489 | 0.005002 | 0.005005 |
| Irreversible choice | Learned proposals + hardest | 6/6 | 0.251362 | 0.005033 | 0.217686 |
| Irreversible choice | Uniform proposals + random | 6/6 | 0.291801 | 0.005094 | 0.209967 |
| Irreversible choice | Uniform proposals + hardest | 6/6 | 0.251432 | 0.005085 | 0.211931 |
| Irreversible choice | All targets (extra decoder work) | 6/6 | 0.251701 | 0.005987 | 0.171098 |
| Noisy readings | Learned proposals + hardest | 6/6 | 0.094117 | 0.006875 | 0.008682 |
| Noisy readings | Uniform proposals + random | 6/6 | 0.110418 | 0.008764 | 0.013401 |
| Noisy readings | Uniform proposals + hardest | 6/6 | 0.096168 | 0.008104 | 0.011033 |
| Noisy readings | All targets (extra decoder work) | 6/6 | 0.087863 | 0.009659 | 0.015066 |

Root-noise probability concerns the first action. Noise-action fraction averages both actions and all four worlds; the second action is irrelevant in the irreversible environment. Equal weighting of worlds is used only for this descriptive noise-use diagnostic; the training objective and simulation audits use worst-world error and no prior.

## Decoder and model diagnostics

The empirical fitted-decoder gap compares achieved error with the best decoder for the same empirical model. The deployed decoder gap makes the same comparison in the true model, so the deployed gap can reflect both imperfect fitting and empirical-model shift. Each gap is maximized over the archived targets before averaging seeds.

| Environment | Method | Empirical fitted-decoder gap | Deployed decoder gap | Empirical achieved loss | True achieved loss | Fixed-decoder loss shift | Optimal-profile model gap |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| compatible | adversarial | 0.000250 | 0.024821 | 0.007411 | 0.028661 | 0.024646 | 0.000091 |
| compatible | random | 0.000525 | 0.036366 | 0.006496 | 0.039033 | 0.036076 | 0.000098 |
| compatible | hardest_uniform | 0.000026 | 0.026746 | 0.006885 | 0.031465 | 0.026792 | 0.000091 |
| compatible | all_targets | 0.000983 | 0.051079 | 0.007399 | 0.052139 | 0.050471 | 0.000115 |
| irreversible | adversarial | 0.000078 | 0.000080 | 0.251420 | 0.251442 | 0.000079 | 0.004387 |
| irreversible | random | 0.000224 | 0.011328 | 0.210943 | 0.211398 | 0.006936 | 0.005027 |
| irreversible | hardest_uniform | 0.000096 | 0.002129 | 0.251504 | 0.251538 | 0.002067 | 0.004387 |
| irreversible | all_targets | 0.000629 | 0.017005 | 0.251759 | 0.251806 | 0.012254 | 0.004383 |
| noisy | adversarial | 0.000709 | 0.020911 | 0.085369 | 0.103956 | 0.021014 | 0.019320 |
| noisy | random | 0.001193 | 0.037159 | 0.077543 | 0.098648 | 0.035923 | 0.018949 |
| noisy | hardest_uniform | 0.000835 | 0.023967 | 0.083442 | 0.103691 | 0.022344 | 0.020171 |
| noisy | all_targets | 0.001316 | 0.054726 | 0.086274 | 0.108686 | 0.053725 | 0.016888 |

Achieved losses are each seed's largest archived-target error using the actual fitted decoders. Fixed-decoder loss shift is the largest absolute empirical-versus-true change for those same decoders. Optimal-profile model gap instead compares the optimal deficiency in each model across all 27 targets. The optimal-profile gap may be small even when a particular fitted decoder changes substantially between models.

## Paired comparisons

Differences are adversarial minus the named control; negative favors adversarial. The across-round measure averages rounds 1 through the registered final round, excluding initialization. Wins/ties/losses use tolerance 1e-7 and describe these seeds only.

| Environment | Control | Mean final difference | Mean rounds 1–R difference | Wins / ties / losses |
| --- | --- | ---: | ---: | ---: |
| Compatible readings | random | -0.000597 | -0.062050 | 6 / 0 / 0 |
| Compatible readings | hardest_uniform | -0.000001 | -0.000075 | 1 / 4 / 1 |
| Irreversible choice | random | -0.040440 | -0.073428 | 3 / 0 / 3 |
| Irreversible choice | hardest_uniform | -0.000070 | -0.000072 | 4 / 0 / 2 |
| Noisy readings | random | -0.016301 | -0.056950 | 4 / 0 / 2 |
| Noisy readings | hardest_uniform | -0.002051 | 0.001291 | 4 / 0 / 2 |

Every seed's signed differences are retained in SUMMARY.json, including losses and missing pairs.

## Selection diagnostics

Candidate errors are compared with the previous checkpoint's collector, before adding the candidate. A target can look difficult because its decoder is undertrained or the empirical model is inaccurate. An already simulable target need not be pure noise; both counts are therefore retained.

| Environment | Method | Selected targets | World-independent targets | Already simulable in true model |
| --- | --- | ---: | ---: | ---: |
| compatible | adversarial | 30 | 0 | 1 |
| compatible | random | 30 | 0 | 7 |
| compatible | hardest_uniform | 30 | 0 | 0 |
| compatible | all_targets | 0 | 0 | 0 |
| irreversible | adversarial | 30 | 0 | 0 |
| irreversible | random | 30 | 12 | 12 |
| irreversible | hardest_uniform | 30 | 1 | 1 |
| irreversible | all_targets | 0 | 0 | 0 |
| noisy | adversarial | 30 | 0 | 0 |
| noisy | random | 30 | 0 | 6 |
| noisy | hardest_uniform | 30 | 0 | 0 |
| noisy | all_targets | 0 | 0 | 0 |

## Actual computation

| Environment | Method | Mean training seconds | Mean decoder-target updates | Mean candidate queries | Mean generator updates |
| --- | --- | ---: | ---: | ---: | ---: |
| compatible | adversarial | 4.924 | 18650 | 20 | 75 |
| compatible | random | 4.815 | 18650 | 20 | 0 |
| compatible | hardest_uniform | 4.849 | 18650 | 20 | 0 |
| compatible | all_targets | 4.904 | 105300 | 0 | 0 |
| irreversible | adversarial | 4.678 | 18650 | 20 | 75 |
| irreversible | random | 10.439 | 18650 | 20 | 0 |
| irreversible | hardest_uniform | 4.573 | 18650 | 20 | 0 |
| irreversible | all_targets | 4.605 | 105300 | 0 | 0 |
| noisy | adversarial | 4.653 | 18650 | 20 | 75 |
| noisy | random | 4.599 | 18650 | 20 | 0 |
| noisy | hardest_uniform | 4.598 | 18650 | 20 | 0 |
| noisy | all_targets | 4.576 | 105300 | 0 | 0 |

## Missing or invalid records

None among the registered runs.

## Figures

- `training_curves.png` / `.pdf`: means and all individual seed trajectories; no confidence intervals.
- `final_target_profiles.png` / `.pdf`: all 27 targets for the first registered seed, chosen before outcomes.
- `decoder_and_noise.png` / `.pdf`: empirical and deployed decoder gaps, root-noise probability, and the fraction of noise actions.

These results establish no convergence guarantee, approximation guarantee for eventual J_w, or superiority on unseen world classes. Positive minimax error can be an unavoidable tradeoff. No true-model audit was used to choose targets or update the learner.
