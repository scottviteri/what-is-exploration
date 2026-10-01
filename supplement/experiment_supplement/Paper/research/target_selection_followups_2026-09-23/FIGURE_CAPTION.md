# Candidate empirical figure: caption and interpretation

This is a research candidate, not an edit to the selected manuscript. `FOLLOWUP_FIGURE.pdf` is regenerated from verified follow-up results. The figure and `figure_data.csv` describe one captured summary; `STATUS.md` can be newer while work is running.

## Proposed self-contained caption

**How well can an optimized policy's evidence reproduce longer experiments?** Each row is a supplied class of possible environments, with a common action/observation interface and an unknown actual member. Policies collect three observations. Information, posterior Brier, and the categorical pseudo-count bonus are optimized over this collection horizon; the native methods optimize either mean deficiency or maximum deficiency against all 128 deterministic three-step target policies. All collectors may adapt actions to their observed histories. We then hold the collector fixed and evaluate

\[
A_{3,4}(\pi)=\max_\sigma\min_G\max_Q
\operatorname{TV}\!\left(K_{\pi,3}(Q)G,K_{\sigma,4}(Q)\right),
\]

using all 32,768 deterministic four-step target policies. Each decoder may depend on its target policy, but the same decoder must work for every possible world in that row. Lower values mean that the collected evidence better reproduces even its hardest target experiment. The four-step targets do not select the collector.

Panel (a) shows upper bounds across the recorded, numerically verified optimizer representatives, alongside a uniform-action control. Panel (b) shows the Brier collector's error minus each native collector's error. Filled circles use the ordinary Brier optimizer returned by planning; open diamonds use a collector selected to minimize the three-step audit while preserving optimal Brier reward up to an absolute numerical slack of 1e-10. This favorable selection is made at the training horizon, without using the four-step results. Intervals reflect numerical bounds and variation among recorded optimizer representatives, not statistical confidence intervals or bounds over every objective-optimal policy. A dagger marks a visible representative spread. Missing entries are unfinished or unavailable comparisons, not zero error. The weighted native method is a finite, uniform 128-target objective; neither it nor the finite minimax objective is the eventual infinite-rich J_w.

## Why this is a useful candidate

The figure compares the exploration induced by distinct objectives on a common, operational evaluation, and tests a longer target horizon than the one used by the native optimizers. A finite minimax optimizer's advantage on its identical three-step training audit would follow from its definition; advantage on this four-step audit does not. The previously observed delayed-horizon reversal remains in the figure. Recorded weighted-native optima can also lose to Brier, including a case where an equally weighted-optimal policy has better held-out performance. These limits belong next to any positive case counts.

The twelve fresh model classes supplement ten pre-existing cases. They do not constitute a broad distributional guarantee. Class counts are descriptive, and runs that select different optima in one class are not independent environments. The comparison uses known hypothesis classes and planning access to every candidate model; it does not establish that a learner with only interaction access can discover those policies or decoders.

## The near-optimal extension

The separate extension evaluates all seventy available previously optimized information/Brier control policies with normalized reward regret 0.01 or 0.05. If R_max and R_min are the best and worst achievable rewards at collection horizon three, the original constraint is

    R(pi) >= R_max - r * (R_max - R_min) - 1e-10.

Within that constraint, the original planner minimized A_{3,3}; the new work only evaluates the already selected collector on A_{3,4}. Thus “1%” means one percent of the achievable reward range, not one percent of the optimal reward. The eighteen originally registered but unavailable collectors stay missing. This extension can reveal whether a small reward sacrifice allows the baseline to recover capabilities; it is not a new optimizer or a worst-case statement about all near-optimal collectors. Its results should inform the final empirical interpretation before deciding whether to replace the paper's current last figure.
