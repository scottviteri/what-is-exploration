# Completed primary comparison

Captured 2026-09-23T19:15:47.744934+00:00. All 17 completion jobs passed their saved-certificate audit. The original archive and recovered-policy checks are separately recorded in the provenance.

Collectors observe three steps, are optimized with three-step objectives, and are evaluated against all 32,768 four-step target policies. The actual world remains unknown within each supplied model class. Lower worst-target deficiency is better.

| Method | Comparator | Cases | Wins | Ties | Losses |
|---|---|---:|---:|---:|---:|
| minimax | information | 22 | 21 | 1 | 0 |
| minimax | brier | 22 | 19 | 1 | 2 |
| minimax | legacy_native_weighted | 20 | 14 | 1 | 5 |
| minimax | face_information_0 | 22 | 21 | 1 | 0 |
| minimax | face_brier_0 | 22 | 20 | 1 | 1 |
| weighted128 | information | 22 | 20 | 1 | 1 |
| weighted128 | brier | 22 | 18 | 2 | 2 |
| weighted128 | legacy_native_weighted | 20 | 10 | 0 | 10 |
| weighted128 | face_information_0 | 22 | 20 | 1 | 1 |
| weighted128 | face_brier_0 | 22 | 19 | 1 | 2 |

The results support a useful finite comparison, with important limits:

- Finite minimax beats ordinary Brier in 19 of 22 classes; weighted native beats it in 18. These describe the recorded optimizer representatives, not every policy optimizing the corresponding reward. The comparison tolerance is 1e-6, with interval envelopes across verified representatives in each class.
- The delayed class with parameters 0.25 and 0.1 remains an unfavorable example: Brier has four-step error about 0.14324, minimax 0.16622 and weighted native 0.18157. Optimizing the three-step audit does not guarantee optimal four-step simulation.
- In the symmetric irreversible class, the selected weighted optimum has error about 0.24569 versus 0.236 for information, Brier and minimax. The existing optimum-selection audit found another equally weighted-optimal saved policy with better held-out performance. This loss is evidence about optimizer selection, not a proof that every weighted optimum loses.
- Favorable nominal Brier selection means minimizing the THREE-step audit within its reward-optimal set (absolute numerical reward slack 1e-10). It need not improve the FOUR-step audit. In the symmetric sensor case, this selection changes held-out error from about 0.10817 to 0.10979; minimax is about 0.10824. This explains why the native win count can rise against a control designed to be favorable at the training horizon.
- Increasing the fixed weighted library from the legacy 16 targets to 128 is not uniformly beneficial: in the 20 comparable classes it gives 10 wins and 10 losses on the four-step worst-target audit. More targets change the finite weighted objective; they are not merely a more accurate numerical solve of the same score.
- Neither native method is the eventual infinite-rich J_w. These are numerical finite-horizon results under model-class planning access. The twelve fresh classes and ten earlier classes do not establish broad distributional performance or an interaction-only learning guarantee.
- The earlier 15 September benchmark failed its prespecified broad-benefit screen for its 16-target native objective. This different horizon/target benchmark does not erase that outcome.

The seventy-policy 1%/5% regret extension has separate registration and is not included in this checkpoint. It tests how much of the observed gap survives a small reward tradeoff without reoptimizing or selecting on the held-out horizon. Eighteen original control policies were unavailable.

[PRIMARY_COMPARISON.json](PRIMARY_COMPARISON.json) retains each pair, numerical interval, and exact result/check provenance. [FIGURE_CAPTION.md](FIGURE_CAPTION.md) states the intended interpretation. The live [STATUS.md](STATUS.md) and eventual FINAL_SUMMARY.md report subsequent extension coverage and failures.
