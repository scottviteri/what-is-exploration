# Candidate empirical ending: objective, capability, and computation

23 September 2026. **Proposal and standalone figure only; the manuscript is unchanged.**
the lead author asked this conversation to work toward replacing the last experiment and to
commission definitions-first explanations from the existing Missing citations
conversation at substantive milestones. The first commission is complete; see [brief](COMMISSION_01.md) and [delivery record](COMMISSION_01_DELIVERY.json).
Read the completed [definitions-first explanation](MISSING_CITATIONS_EXPLANATION.md).
Completion was reported by the owning conversation and its output hash recorded.

The completed commission recommends a broader 22-class main figure. The
[22-class alternate figure](CANDIDATE_22_CLASSES.pdf) and its
[caption](CAPTION_22.md) are now available. The [figure-choice note](FIGURE_CHOICE.md)
compares that recommendation with the
12-setting candidate and records the differing objectives and evidence coverage.
Both presentations are being reviewed separately; their results are not pooled.

## Concrete candidate

[Main figure (PDF)](CANDIDATE_FIGURE.pdf) · [PNG](CANDIDATE_FIGURE.png) ·
[tradeoff diagnostic (PDF)](TRADEOFF_DIAGNOSTIC.pdf) · [caption](CAPTION.md) ·
[plotting source](make_candidate.py) · [all plotted-source rows](figure_data.csv) ·
[derived comparisons](ANALYSIS.json) · [source and artifact checks](FIGURE_CHECK.json) ·
[independent candidate review](INDEPENDENT_REVIEW.json).

**Question:** With the same three action–observation pairs and supplied candidate
world models, how do intrinsic objectives differ in the evidence they acquire for
reproducing four-step interactions, and what reward and computation do those
choices cost?

This question advances the paper's comparison of objective-induced exploration.
The current startup pilot learns only the initial action probabilities with fixed
continuation. All six currently presented conditions favor inspection. The
candidate instead optimizes full-history adaptive policies on several unknown-world
classes, computes the resulting acquired experiments, and exhaustively evaluates
their hardest four-step targets. It is a planning study, not a new policy-training
or unknown-model-learning study.

The primary source is Missing citations' completed
[corrected finite-computation study](../jw_computational_tests_2026-09-23/quality_corrected/summary/REPORT.md).
The figure keeps all twelve settings and both unfavorable native cases. Its layout
and the emphasis of this recommendation are post-design interpretation; they do
not retroactively change that study's frozen protocol or create a new confirmation.

## Objects and measured quantity

A **world** is a candidate controlled response law. Each case supplies four or eight
candidate models with three hidden physical states, two actions, and two observations.
The initial physical state is zero. Which model is actual remains unknown. All
methods receive the same candidate transition/observation arrays. Knowing the set
of possible models is different from knowing its actual member; a singleton class
would make the information comparison vacuous.

A **policy** chooses an action distribution from the preceding actions and
observations, using no direct access to the actual world. Its length-three
**record** contains its three actions and three observations. The **experiment**
`K_{pi,3}` is the family of distributions of that record, one distribution for each
candidate world; it is not one sampled trajectory.

A **target policy** is another permissible adaptive policy, executed for four
steps in the same declared world class. Its experiment is `K_{sigma,4}`. A
**decoder** is a randomized transformation of the collected record into a simulated
target record. It may depend on which target is requested and on the known model
class, but the same transformation must work in every candidate world. It cannot
be told the actual model. Total variation measures distributional mismatch.

The reported scalar is

\[
 A_{3,4}(\pi)=\max_{\sigma}\;\min_G\;\max_{Q\in\mathcal Q}
 \operatorname{TV}\!\left(K_{\pi,3}(Q)G,K_{\sigma,4}(Q)\right).
\]

The deficiency direction is **collected record to target record**. The outer
maximum chooses the target whose evidence is hardest to reproduce, with each
target allowed its own best world-independent decoder. Collection length is three;
target length is four. They are separate budgets. The complete audit enumerates
all 32,768 deterministic depth-four observation trees; randomized targets are
covered by the finite-mixture reduction, not by sampling them.

The models use two independent generator seeds, each reused at four/eight worlds
and Dirichlet concentrations 0.2/1/5. Concentration controls how uneven the sampled
transition/observation rows tend to be. The twelve parameter settings are useful
paired comparisons, **not twelve independent random seed families**. No population
significance test or statistical confidence interval is proposed from this grid.

## Methods and why the evaluation is different

- **Full-world information gain:** maximize `H(prior) - E[H(posterior)]` after
  three steps under the uniform world prior. The posterior is over the actual
  world label, not selected features or the hidden physical state alone.
- **Ordinary posterior Brier improvement:** maximize
  `E[sum_Q posterior(Q)^2] - sum_Q prior(Q)^2`, equivalently the expected cumulative
  squared posterior movements. It also concerns the whole world label. Both
  posterior objectives are optimized by full-history dynamic programming on the
  supplied models. These are objective-level Bayesian comparisons, not claims
  about the training performance of a published exploration implementation.
- **Fixed native weights:** minimize the retained weighted sum of deficiencies
  to 131 training targets: all 128 deterministic depth-three trees and independent
  uniform-action targets of lengths one, two, and three. A uniform foreground on
  these encodings receives mass 0.95, and a fixed positive countable background
  receives mass 0.05. Original background coefficients are retained without
  renormalizing the truncated sum.
- **Finite minimax reference:** minimize the maximum deficiency over that same
  finite training library. This is a different objective from the weighted one.
- **Uniform actions:** a simple policy control, with both actions equally likely.
- **Favorable posterior controls:** minimize the training-library maximum
  deficiency subject to posterior reward at least
  `R_max - max(1e-10, r*(R_max-R_min))`, for `r = 0, .01, .05`. These select particular
  nearly optimal posterior policies using training targets only; they are not
  the complete set of reward optima or the best policies on held-out targets.

The native planners see depth-three training targets; evaluation fixes the same
collector and asks about depth-four targets. No depth-four audit chooses the
policy, weights, checkpoint, or posterior control. This avoids optimizing the
identical evaluation loss. It does not demonstrate transfer to another model
class or arbitrary unseen horizons.

The retained finite weighted loss, the full countable weighted loss at collection
time three, and the paper's eventual `J_w` are distinct. The omitted coefficient
mass is about 0.04895. A later certificate refinement bounds the fixed method's
regret for the **full fixed-time sum** by 0.00243–0.00616 in these settings; it does
not bound eventual `J_w` regret or construct a successful infinite policy. Its
additional audit/certification cost lies outside the planning allowance.

## What the completed evidence says

At forty seconds, fixed weights and finite minimax each beat the ordinary
information and Brier representatives in ten settings and lose in two. Their
median reductions against ordinary Brier are 0.023019 and 0.022625, respectively.
Against the Brier control allowed 5% reward-range loss, both win nine and lose
three, with median reductions 0.000885 and 0.008081. Fixed weights beat the
corresponding information control eight times and lose four.

The favorable controls materially change the interpretation. Fixed native
weighting itself gives up a median **21.17% of the attainable Brier reward
range**, spanning 11.08–38.96%, and less expected information than the information
optimum in every case. Thus a near-tie against the 5% control is a useful result
for Brier. It would be misleading to portray the raw audit improvement as a free
gain in information.

Computation also matters. At two seconds, fixed weights versus ordinary Brier are
six wins, five losses, and one unresolved comparison. Ordinary posterior dynamic
programming takes about 5 ms excluding interpreter startup/output. The native
methods have the same acquisition budget but require substantially more planning.
Forty seconds is an allowance, not work consumed by every method. Evaluation and
witness checking are additional costs.

The strongest interpretive limit is substantive, not just a caveat about sample
size: **all 144 tested native/baseline pairs are numerically incomparable at
collection time three**, including scalar-audit wins and losses. Each record can
preserve a capability that the other cannot reproduce exactly. The supporting
figure shows both deficiency directions for fixed/minimax versus Brier. A smaller
`A_{3,4}` does not establish policy dominance, eventual sufficiency, or an
all-purpose superiority of `J_w`.

After aggregating already valid in-budget lower bounds, all 96 static forty-second
training-objective gaps are at most 8.1e-7. Some original endpoint CSV gaps were
attached to earlier incumbents and should not be used as the final gap. Small
numerical gaps still concern selected representatives, not all optimizers.

## What to include and what to keep supporting

Use the fixed-weight, information, Brier, uniform, and finite-minimax comparisons
as the core. This does not cover every reward in the theory table: rewards defined
on observed physical states or stationary skill families require their own
source-faithful experimental interfaces. Do not substitute observation labels
for those state variables to add more rows. The main candidate shows absolute errors, planning-budget sensitivity,
and favorable posterior controls. The supporting figure exposes reward sacrifice
and same-time incomparability directly.

Keep changing-weight heuristics secondary: at forty seconds cost-adaptation beats
fixed weights eight times and loses four with a small median change; hard-target
adaptation is six/six. Both adaptive methods lose to uniform actions in eight of
twelve settings at two seconds. These are useful computational findings, but a
weight-adaptation algorithm is a separate contribution from comparing intrinsic
objectives.

Keep the earlier [16-target failed screen](../native_objective_benchmark_2026-09-15/README.md)
visible. Its prespecified broad-benefit criterion failed and it had no nominal
wins over Brier on its primary decision-average metric. The newer worst-target
audits use a different endpoint and do not erase or replicate that failed test.
The [22-case follow-up](../target_selection_followups_2026-09-23/FINAL_SUMMARY.md)
provides broader designed/random examples and favorable reward controls; preserve
its incomplete recovery and missing-control accounting when using it. It should
be supporting evidence, not pooled as independent replication of this fresh grid.

## Next substantive milestone

The completed study supports a narrow descriptive empirical ending already. Before
using it as the principal empirical evidence, the best next numerical investment
is **more independent seed families under a frozen confirmation protocol**, rather
than more adaptive heuristics or selecting more favorable environments. Proposed
scope is in [CONFIRMATION_DRAFT.md](CONFIRMATION_DRAFT.md); it is not a launched run.

The requested Missing citations explanation should first check this interpretation
and identify any source/optimization/formal-scope errors. The [second commission](COMMISSION_02.md) has now been queued to
review the concrete figure and confirmation design, asking again for terms and
quantifiers to be explained before assessing claims; its [dispatch record](COMMISSION_02_DELIVERY.json)
is separate from completion of that review. A further commission belongs
after new confirmation results or any material change in the interpretation. This
is milestone-based coordination, not automated frequent status requests.

No shared manuscript, figure directory, Lean file, navigation index, evidence ledger,
Git state, or Overleaf package is changed by this candidate package. The plotting
script verifies existing data bindings and derived arithmetic; it launches no LP,
training, or exhaustive audit workers.
