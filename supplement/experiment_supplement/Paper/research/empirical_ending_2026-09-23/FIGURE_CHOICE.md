# Choosing the empirical ending after Commission 01

This is a recommendation about standalone candidates, not an edit to the paper.
The completed [Missing citations explanation](MISSING_CITATIONS_EXPLANATION.md)
recommends the 22-class comparison. The initial candidate uses its separate
12-setting computation study. Both address a more substantial question than
startup-only learning: which finite objectives select evidence capable of
reproducing longer interactions?

Both standalone candidates are available: [12-setting figure](CANDIDATE_FIGURE.pdf)
and [22-class figure](CANDIDATE_22_CLASSES.pdf). The latter preserves every row,
131/132 available absolute entries, and 78/88 paired differences; its
[check](FIGURE22_CHECK.json) reconstructs 355 saved representatives.

The choice should follow that question and the completeness of the evidence,
not which cohort gives the larger native win count.

| Consideration | 22-class comparison | 12-setting comparison |
|---|---|---|
| Variety | Structured sensors, delay, irreversible choice, recurring and fresh random classes | One random hidden-state construction varied across class size and concentration |
| Posterior controls | Five missing 5%-Brier controls; 18 missing 1%/5% controls overall | Complete 0/1/5% information/Brier grid |
| Uniform control | One unavailable evaluation | Complete |
| Native weighted objective | Uniform finite mean over 128 deterministic targets | Retained part of a specified rich weighted sum on 131 encodings |
| Target witness replay | Original exhaustive profiles lack saved per-target witnesses; new sweeps preserve them | Every depth-four target witness replayed |
| Selection | Envelopes over available verified representatives expose tied-optimum sensitivity | Fixed compute checkpoints, with static optimization gaps and actual rewards available |
| Objective coverage | Includes the source-qualified categorical pseudo-count score | Information and posterior Brier, plus native methods and uniform control |
| Interpretation directly measured | Explicit delayed reversal and representative sensitivity | Computation cost, actual reward sacrifice and bidirectional record deficiencies |

Neither is a broad independent replication study. The 22-class grid includes ten
earlier cases; the twelve-setting grid shares two independent seed families.
The original 22-class computations are not invalidated by their narrower saved
witness boundary. However, no figure caption should silently upgrade that
boundary to the stronger new replay standard.

## Provisional recommendation

Keep the **12-setting figure as the leading candidate** while the second
commission reviews both choices. Its main advantage is that the favorable reward
controls cover every displayed setting, and their relation to actual reward
sacrifice can be shown without a changing denominator. This supports a focused
ending about capability/reward tradeoffs. Planning time can be a compact third
panel or a supporting plot; the paper need not become a solver comparison.

Use the **whole 22-class figure as a substantive companion**, retaining its delay
reversal, tied-optimum sensitivity, count comparison, and missing controls. Do
not select only the favorable structured examples. In particular, compare ordinary
and 5%-Brier counts on the same 17 available classes: minimax is 15/0/2 for both;
weighted128 changes from 14/2/1 to 13/0/4. These are wins/numerical ties/losses,
not unchanged error magnitudes or statements about the five missing controls.

If the desired main question prioritizes diversity and the count objective over
complete controls and matched cost accounting, the 22-class figure is defensible
as the primary descriptive figure. That is the substantive case for Missing
citations' recommendation. It must retain the missingness and verification
qualifications. The two cohorts must never be pooled as one win-rate experiment.
The 12-setting rich-background certificates, 21.17% median Brier sacrifice,
planning times and 144 incomparability pairs do not describe the different
22-class policies.

## What the commissioned explanation corrected

The actual 12-setting reward constraint is

    R(pi) >= R_max - max(1e-10, r*(R_max-R_min)).

The 22-class code instead subtracts `r*(R_max-R_min) + 1e-10`.
The difference is numerically tiny here, but the formulas should match the code.
The initial candidate README had imported the latter formula; it has now been
corrected after checking `quality_corrected/planner.py` lines 115–116. This does
not change any policy, audit or plotted value.

## Next computation should answer a named missing question

No expensive new run is necessary to review these two candidates. Three distinct
extensions should not be conflated:

1. **More reward coverage in the complete study:** apply the existing source-qualified
   add-one categorical pseudo-count objective to the twelve supplied model classes.
   Preserve `1/sqrt(1+N(o))`, counts before the current observation, raw observation
   labels, finite return and full-history policy space. This is a density-model
   specialization, not the CTS Atari implementation. Planning is cheap relative
   to the additional exhaustive acquired-experiment audits. This is proposed,
   not executed; the source and independent checker must be frozen before a run.
2. **Complete the broader grid:** recover the remaining uniform audit and originally
   missing posterior controls, preserving prior failures; separately decide whether
   full per-target witness replay is worth its cost. These repairs improve coverage,
   not independent generalization.
3. **Independent confirmation:** the existing [draft](CONFIRMATION_DRAFT.md) proposes
   eight fresh seed families. Add the same source-qualified count arm if objective
   breadth is the chosen priority; budget its additional audits explicitly before
   freezing. This tests a new grid after presentation choices are settled. It does
   not turn the old outcomes into prospective confirmation of those choices.

The second Missing citations commission asks for a judgment among these priorities
and between the two figures. Its review is pending until that conversation reports
completion. No numerical workers, shared manuscript edits, or publication actions
are part of this presentation-comparison pass.
