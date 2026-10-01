# What the completed experiments establish, and how to use them

23 September 2026. Explanation commissioned by Introduction Edits at the lead author's
explicit request. This document stands alone and makes a recommendation; it
does not implement a figure or change the manuscript.

My recommendation is to replace the startup-only main figure with the completed
comparison across 22 supplied sets of possible environments, including the
controls that allow information and Brier rewards to sacrifice a small amount
of their own return. Its central question is whether collecting evidence to
reproduce short experiments also helps reproduce longer experiments that were
not used to choose the collector. Both improvements and reversals are present.
The separate computation-budget study explains the computational price and the
limits of this result. Neither study establishes a generally superior
exploration algorithm.

The explanation below defines the objects before discussing the measurements.
The final part specifies one proposed main figure and the claims it can test.
All reported numerical results come from completed records. Reading and
recounting those records for this note launched no optimization or audit workers.

## 1. What is unknown, and what the experiment designer supplies

A chosen **action** is an input to the environment; an **observation** is the
signal it returns. A **world** specifies how observations respond to actions. At the general level
used in the paper, it need not have a state representation. For a finite
action-observation history
\[
h=((a_1,o_1),\ldots,(a_t,o_t)),
\]
write \(p_q(h)\) for its controlled observation probability in world \(q\).
It satisfies \(p_q(\varnothing)=1\) and
\[
\sum_o p_q(h(a,o))=p_q(h)
\quad\text{for each proposed action }a.
\]
The normalization is separately over observations for each action. These
numbers do not yet form one probability distribution over all histories,
because no rule has assigned probabilities to the actions.

A **hypothesis class** \(\mathcal Q\) is the declared set of possible worlds.
The actual member \(q\) stays fixed throughout a collection run. A comparison between
methods holds this class fixed. A different row of the experimental comparison
can use a different class.

The numerical studies instantiate worlds using controlled **hidden-state
models**. A hidden state \(s_u\) is the current internal physical configuration;
an observation \(o_u\) is the signal the agent receives. The state can change
while the world remains the same. In the random-model study, every world has
three hidden states, the initial state is zero, and actions and observations
are both binary. World \(q\) supplies transition probabilities
\(P_q(s'\mid s,a)\) and emission probabilities \(Z_q(o\mid s',a)\).
The implementation first transitions and then emits:
\[
s_{u-1}\xrightarrow{a_u}s_u,\qquad
o_u\sim Z_q(\cdot\mid s_u,a_u).
\]
The experiment code calls the transition array `T` and the emission array `Z`.
Below, \(T_j\) denotes a target experiment instead; it is a different object.

For example, a class with four worlds and three hidden states has four possible
transition/emission mechanisms, each with three internal states. It is neither
four states in one model nor twelve competing world labels. The collector sees
actions and observations, not the hidden state or the true world label.
Marginalizing hidden-state trajectories produces the controlled probabilities
\(p_q(h)\) used by the general theory.

These are **supplied-model planning** experiments. Every method receives the
same exact candidate-model arrays. It may calculate how a proposed policy would
behave in each candidate world, but it cannot condition its actual action on
which world is true. There is no preliminary task of learning those arrays from
samples. This gives a well-defined policy optimization problem and removes
model-fitting error; it does not demonstrate learning from interaction alone.

Information and posterior Brier additionally use a **prior**
\(\alpha(q)\), a probability distribution over world labels. It is uniform in
the comparisons here. The native errors defined below take a maximum over
worlds instead of averaging with this prior. Supplying the same models therefore
does not make the objectives identical.

Sources: the [controlled-behavior reference](../../../TheoryDocs/causal_behavior_semantics.tex),
the [current theory setup](../../CURRENT_THEORY_STATE.tex), and the independent
[physical-policy replay](../jw_computational_tests_2026-09-23/quality_corrected/validate_audits.py).

## 2. Policies, records, and statistical experiments

A **policy** \(\pi(a\mid h)\) gives a distribution over the next action for each
previous action-observation history. It may randomize and depend on the full
history. All the main collectors considered here have this access. They are
not restricted to choosing an initial action followed by a fixed continuation.

A **record** \(H_t\) is the retained sequence of the first \(t\) actions and
observations. The **collection horizon** \(t\) is the number of physical
interactions in this record. In the primary comparisons discussed below,
\(t=3\). A record is one possible output, not the probability law of all outputs.

The policy supplies the missing action probabilities:
\[
w_\pi(h)=\prod_{u=1}^t\pi(a_u\mid h_{u-1}),\qquad
E_{\pi,t}(q,h)=w_\pi(h)p_q(h).
\]
For each \(q\), the row \(E_{\pi,t}(q,\cdot)\) sums to one. The matrix
\[
E_{\pi,t}:q\longmapsto\operatorname{Law}^{\pi}_q(H_t)
\]
is the acquired **statistical experiment**. Here “experiment” means a
family of signal distributions indexed by the unknown world. It does not mean
one training run or one simulated episode. The paper also writes this matrix as
\(K_{\pi,t}\).

With two actions, two observations and \(t=3\), there are \(4^3=64\)
possible complete records, including records of zero probability. A full
behavioral policy has \(1+4+16=21\) action-distribution rows before that deadline.
This is a substantially larger policy choice than the startup-only softmax
parameter in the current figure.

Records include actions. A randomized choice can label which measurement
generated the observation. Discarding that label can change the statistical
experiment. Different policies can nevertheless produce identical acquired
matrices; where that happens, the capability evaluation can be reused after
checking the policies and model bindings.

The numerical evaluation calculates these distributions from supplied models.
It is not an empirical estimate from a finite sample of episodes. The random
seeds generate model classes or computational target orders; they are not
repeated Monte Carlo measurements of one fixed decoder's error.

## 3. Targets, decoders, and the direction of deficiency

A **target** is an experiment we want the collected record to be able to
replace. A native target uses the same action-observation interface and a
specified intervention policy \(\sigma\), run for a **target horizon** \(n\):
\[
F_{\sigma,n}(q,\cdot)=\operatorname{Law}^{\sigma}_q(H_n).
\]
“Native” says that this target can actually be generated through the declared
interface. The target horizon \(n\) need not equal the collection horizon \(t\).
In the principal evaluation, a three-interaction collector is asked to
substitute for four-interaction targets.

These target laws start at the model's specified initial condition. They
describe counterfactual experiments that could have been run in the same world.
Decoding a target record does not restore a physical option after an irreversible
action or perform new interactions in the collector's current state.

A **decoder** \(G(y\mid x)\) is a randomized rule that takes an acquired record
\(x\) and outputs a simulated target record \(y\). Its rows are nonnegative and
sum to one. It may depend on the known model class, collector, target and
horizons. It must be the **same rule for every unknown world**. Allowing a
different decoder for each world would give it the answer it is supposed to
infer.

For two distributions \(u,v\) on the same finite output set, their
**total-variation distance** is
\[
\operatorname{TV}(u,v)=\frac12\sum_y|u(y)-v(y)|.
\]
It lies between zero and one and bounds their difference on any event.

The directed **deficiency** is
\[
\delta(E,F)=
\min_G\max_{q\in\mathcal Q}
\operatorname{TV}\bigl((EG)(q,\cdot),F(q,\cdot)\bigr).
\]
The finite problems here attain the minimum; the general definition uses an
infimum. The source is the **first** argument. Small \(\delta(E,F)\) says
that \(E\) can simulate \(F\). It says nothing by itself about
\(\delta(F,E)\).

For a direction check, suppose the two worlds are labelled 0 and 1. Let \(E\)
reveal the label exactly and let \(F\) always produce the same symbol.
Then \(\delta(E,F)=0\): discard the revealed bit. Conversely,
\(\delta(F,E)=1/2\): a decoder with no information can output a fair bit, but
cannot be correct in both worlds more accurately than that. This is why a
larger deficiency means a missing capability, not more exploration.

The quantifier order matters. For every chosen target, find one decoder that
works uniformly over worlds. Different targets may use different decoders.
The definition does not require a single coherent reconstructed world model or
one decoder that simultaneously generates all counterfactual records.

The operational meaning is reuse: after decoding, any bounded decision rule on
the target output can be applied to the simulated output, with its expected
loss changing by at most the decoder's TV error. This supplies a reason to care
about the measurement. It does not make one scalar summary of these errors a
preference-free ordering of all policies.

Sources: [native test geometry](../../../TheoryDocs/native_test_geometry.tex)
and the selected paper's [comparison definitions](../../draft/exploration_decision.tex).

## 4. The evaluation metric and its finite scope

For a fixed collector define
\[
A_{t,n}(\pi)=
\max_{\sigma\text{ deterministic, depth }n}
\delta(E_{\pi,t},F_{\sigma,n}).
\]
This is its worst error over the specified native target horizon. The decoder
is optimized separately for each target. The collector is held fixed during
evaluation.

A deterministic target selects an action at each past observation sequence.
Its previous actions can be reconstructed recursively from its own rule, so
this observation-tree representation loses none of its complete record.
For binary actions and observations there are
\[
2^{\,1+2+\cdots+2^{n-1}}=2^{2^n-1}
\]
such trees: 128 for \(n=3\), 32,768 for \(n=4\), and
2,147,483,648 for \(n=5\).

Every randomized finite-history target can be represented as a
world-independent mixture of deterministic plans. Mixing the corresponding
decoders bounds its error by the largest deterministic-plan error; prefix
projection covers shorter targets. Thus a completed enumeration at depth four
controls all randomized targets of depth at most four as well. It is
exhaustive for this finite target question, despite not enumerating each
randomized policy separately.

This maximum does **not** measure all collection times, an infinite target
horizon, actual-state coverage, or every possible decision problem with the
same accuracy ordering. A policy can have a smaller worst error and a larger
error on particular targets. The full vector of capabilities contains more
information than its maximum.

An evaluation of \(A_{3,4}\) is more demanding than \(A_{3,3}\):
three-step targets are prefixes of legal four-step targets. However, minimizing
\(A_{3,3}\) need not minimize \(A_{3,4}\). The completed experiments include
an actual reversal.

The finite deterministic-to-randomized reduction is registered as
`thm:finite-universality` in the
[support ledger](../../../Formal/PAPER_SUPPORT.json). It is a mathematical
reduction, separate from checking whether a numerical implementation really
enumerated and solved all 32,768 cases.

## 5. Three different native weighted losses

Fix native targets \(T_j\). Write \(d_j(\pi,t)=\delta(E_{\pi,t},T_j)\).
There are three distinct constructions in this discussion.

**A finite weighted loss.** For a finite library \(S\) and fixed coefficients
\(c_j\geq0\),
\[
L_{S,c,t}(\pi)=\sum_{j\in S}c_j d_j(\pi,t).
\]
Introduction Edits' final `weighted128` method minimizes the uniform average
over all 128 deterministic depth-three targets: \(c_j=1/128\).
At earlier library sizes \(K\), its coefficients are \(1/K\).
Adding targets and renormalizing therefore changes the objective being solved;
it is not merely a more accurate solve of the previous finite sum. Relative
to the fixed 128-target uniform reference, a smaller library is a selected
approximation whose error needs separate analysis.

The **finite minimax loss** is instead
\[
M_{S,t}(\pi)=\max_{j\in S}d_j(\pi,t).
\]
These two methods express different preferences: average selected-target error
versus worst selected-target error. A full depth-three minimax solve minimizes
\(A_{t,3}\). Neither finite objective is the paper's eventual score.

**The full countable fixed-prefix loss.** A countable family is **rich** if it
approximates every finite randomized native experiment arbitrarily closely,
uniformly over worlds on the same output alphabet. Rational full-history
policy tables provide a written construction. Fix strictly positive weights
\(w_j\) summing to one. At a fixed collection time,
\[
L_{w,t}(\pi)=\sum_{j=1}^{\infty}w_jd_j(\pi,t).
\]
“Full” here means all the target terms, including targets longer than \(t\).
It does not mean an infinite acquired record. A good optimizer can still have
positive unavoidable loss at this short collection time.

**The eventual score.** Now fix one infinite policy \(\pi\) and let its record
grow. Later records retain earlier ones, so each target error decreases to
\[
\ell_j(\pi)=\inf_t d_j(\pi,t).
\]
The paper's score is
\[
J_w(\pi)=1-\sum_j w_j\ell_j(\pi)
        =\lim_{t\to\infty}\bigl(1-L_{w,t}(\pi)\bigr).
\]
The final equality uses fixed summable weights and bounded target errors.
It is a limit along one policy. It does not interchange optimization and a
limit, turn a sequence of separately chosen short collectors into one policy,
or identify the eventual scores of arbitrary post-deadline continuations.

For orientation, policy \(\pi\) dominates policy \(\rho\) in the **finitary
process order** when every fixed finite record of \(\rho\) becomes uniformly
simulable from sufficiently long records of \(\pi\):
\[
\forall n,\qquad
\inf_t\delta(E_{\pi,t},E_{\rho,n})=0.
\]
Strict dominance additionally excludes the reverse comparison. The rich
eventual profile represents this order; every fixed strictly positive
weighting makes \(J_w\) strictly increase under strict dominance. It chooses
between incomparable profiles according to its weights.

Consequently an attained exact maximizer is undominated. If a sufficient
policy is feasible, exact maximizers are sufficient. These statements supply
no uniform compute bound, acquisition deadline or useful separation margin
for a target with a tiny weight. All the numerical collectors below are
finite-horizon objects.

The actual statements are in
[finitary objective properties](../../draft/finitary_objective_properties.tex),
included by the [full reader](../../draft/exploration_long.tex), and in
[StrictFinitaryRegularity.lean](../../../Formal/Formal/StrictFinitaryRegularity.lean),
especially `exists_causalBehavior_regular_strictly_finitary_objective` and
`tendsto_weightedFinitaryPrefixObjective`. The remaining effective-optimization
and online-assembly boundaries are explicit in
[OPEN_PROBLEMS.md](../../../Formal/OPEN_PROBLEMS.md).

## 6. What the Bayesian and other comparison methods optimize

After a positive-probability record \(h\), the posterior over worlds is
\[
\beta_h(q)=
\frac{\alpha(q)p_q(h)}{\sum_{q'}\alpha(q')p_{q'}(h)}.
\]
The common action-propensity factor \(w_\pi(h)\) cancels. Thus the posterior
at a specified record can be calculated from the candidate models without
knowing which policy brought us there. The policy still changes the probability
of reaching that record.

**World information.** Define entropy in bits by
\(H(b)=-\sum_q b(q)\log_2 b(q)\), taking \(0\log_2 0=0\). Then
\[
R_I(\pi,t)
=H(\alpha)-\mathbb E_{\alpha,\pi}H(\beta_{H_t})
=I(Q;H_t).
\]
For distributions \(b,c\), their KL divergence is
\(D_{\rm KL}(b\|c)=\sum_q b(q)\log_2(b(q)/c(q))\), with the usual zero-mass
conventions. The information reward equals the expected sum of successive
posterior KL information gains
through \(t\). It scores information about the fixed world label, not entropy
of the raw observations, information about the current hidden state alone, or
predictive surprisal. An observation stream can be unpredictable in every world
and reveal no world information.

The underlying source is Bayesian information-based experimental design and
the finite-horizon instance of the sequential information objective.
Orseau et al.'s pinned original, pp. 3–5, equations (3)–(5), explicitly concerns
posterior information and a horizon/discount specification. This experiment
does not test the source's infinite-horizon continuation guarantee or a learned
neural implementation of information gain.

**Posterior Brier gain.** For a categorical forecast \(b\) of the world label
and a realized label \(q\), category-summed Brier loss is
\[
S(b,q)=\sum_r(b(r)-\mathbf1_{\{r=q\}})^2.
\]
Under posterior \(\beta\), its minimum expected value is \(1-\|\beta\|_2^2\),
attained by forecasting \(\beta\). The expected improvement through collection
time \(t\) is therefore
\[
R_B(\pi,t)
=\mathbb E_{\alpha,\pi}\|\beta_{H_t}\|_2^2-\|\alpha\|_2^2
=\mathbb E_{\alpha,\pi}\sum_{u=1}^t
       \|\beta_{H_u}-\beta_{H_{u-1}}\|_2^2.
\]
The second equality uses the posterior martingale identity; it is an equality
of expectations, not a pathwise identity between potential increments and
squared movement.

Brier's original article supplies the categorical forecast loss and its
minimization. Choosing the world label as the forecasted category and using
posterior improvement as a sequential objective is the declared reference
construction here. It is not “Brier's reinforcement-learning algorithm,” and
it is not squared error in predicting the next raw observation.

These two rewards have fixed terminal-record values. Full-history dynamic
programming evaluates the two possible actions backwards through the finite
tree and computes their global reward optima algebraically. The implementation
uses floating-point arithmetic and checks Bellman values and policy replay.
“Exact DP” identifies the complete finite optimization problem being solved;
it is not a claim of exact rational arithmetic in these random-model runs.
The returned tie-breaking policy is one optimizer representative.

**Categorical pseudo-count.** The retained Introduction Edits comparison uses
the add-one categorical observation predictor and bonus
\(1/\sqrt{1+N_{u-1}(o_u)}\), summed through the collection horizon and averaged
under the uniform world prior. \(N_{u-1}(o)\) counts earlier occurrences of the
raw observation label \(o\). Its declared density-model specialization and
update timing are part of the objective. It is not a physical-state count or
the original Atari CTS implementation. The source audit in the
[follow-up protocol](../target_selection_followups_2026-09-23/PROTOCOL.md)
identifies the Dirichlet pseudo-count and inverse-square-root source passages.

**Uniform actions.** This chooses each action with probability \(1/2\) after
every history. It is a control policy, not the optimizer of an information or
native objective.

The selected empirical comparison does not include archived predictive-loss,
empirical label-entropy, ICM or RND specializations as evidence about the
published methods. Their source-fidelity removal and historical results are
preserved. The separate MOP, state-occupancy and DIAYN mathematical examples do
not become computationally tested methods through inclusion in the paper's
theory table.

Source pointers: [literal reward implementation](../jw_computational_tests_2026-09-23/quality_corrected/source/objective_dp.py),
[Brier original, pp. 1–2](../../lit/pdf/review_2026-09-13/brier1950verification_0.pdf),
[Orseau original, pp. 3–5](../../lit/pdf/review_2026-09-13/orseau2013universal_0.pdf),
and the qualified per-use assessments in [USES.md](../../citations/USES.md).

There is also an important **positive theoretical baseline case**. On a finite
world class with a full-support prior (positive probability for every world),
complete information and complete
posterior Brier gain are themselves strictly monotone in the finitary order;
this does not require attainable full revelation. If the feasible family
contains a sufficient policy, their complete-return regrets also bound eventual
native error. That existence assumption is not established by these short
simulations. The exact scope is recorded under
`prop:finite-world-strict-finitary` and
`cor:finite-world-posterior-calibration`, with actual declarations in
[QuantitativeStrictness.lean](../../../Formal/Formal/QuantitativeStrictness.lean)
and [PosteriorCalibrationCorollary.lean](../../../Formal/Formal/PosteriorCalibrationCorollary.lean).
The finite experiments compare acquisition and capability preferences; they
cannot establish a unique eventual-consistency advantage for \(J_w\).

## 7. Native planning, adaptation, and the richer certificates

In both studies, native policy optimization uses linear-program formulations
of causal policy probabilities and decoder errors. The decomposition solver
alternates between a smaller planning problem and decoder calculations.
A **cut** is a lower-bound constraint derived from a target's decoder dual:
it remains valid for other candidate collectors. Accumulating cuts improves
the global planning lower bound. Feasible collectors with checked decoders
supply upper bounds. This explains why the solver can certify a gap without
enumerating every real-valued policy.

There are two different meanings of “adaptive” in the packages:

- In Introduction Edits' **adaptive minimax target selection**, the next target
  is selected for its large current deficiency. A complete separation sweep can
  certify the fixed full depth-three maximum. The target search is part of
  training computation. It need not change the underlying full minimax objective.
- In our **adaptive weighting** study, the same 131 targets are checked every
  round, and their importance weights change. This changes the objective.
  It is not a test of skipping targets or allocating lower precision to cheap
  targets.

Our 131 targets are all 128 deterministic depth-three trees plus independent
uniform-action policies of depths one, two and three. They are encoded as
literal rational full action-observation policies. The added randomized,
shorter targets cannot increase the maximum beyond the full deterministic
depth-three maximum, by the mixture/prefix argument above. Thus our
finite-minimax arm also targets \(A_{3,3}\); the weighted arms do depend on
these additional terms.

Let \(b_j>0\) be the frozen
rich background weights over all rational target encodings. Concretely, at
depth \(n\) a binary full-history table has \(m_n=(4^n-1)/3\) action rows.
For denominator \(d\geq1\), there are \((d+1)^{m_n}\) such tables, each assigned
background mass
\[
b_{n,d,k}=\frac{2^{-n-1-d}}{(d+1)^{m_n}}.
\]
Here \(k\) indexes the table. Different encodings can represent the same
experiment; their coefficient masses still belong to the declared sum.
Summing tables and denominators gives depth mass \(2^{-n-1}\), and summing
depths gives total mass one. The program expands only selected small tables;
the infinite background is handled by its definition and tail bounds, not
by materializing every table.

Let \(a_j\) be an emphasis distribution supported on the 131 retained
encodings. The full weights are
\[
w_j=\epsilon b_j+(1-\epsilon)a_j,\qquad \epsilon=1/20.
\]
The solver retains the actual \(w_j\) for the selected encodings. It does not
renormalize the omitted background into them.

The three weighted methods use:

| Method | Emphasis on the 131 selected targets |
|---|---|
| Fixed | Uniform \(a_j=1/131\), unchanged throughout planning. |
| Cost-adaptive | Uniform reference weights divided by \(1+C_j/s\), then normalized; \(C_j\) is cumulative measured decoder cost and \(s\) is the first-round median cost scale. |
| Hard-target | \(a_j^{r+1}\propto a_j^r\exp(\widehat d_j^r)\), where \(\widehat d_j^r\) is the midpoint of the current deficiency bracket. Floating-point log/exponentiation is normalized into represented rational coefficients. |

Here the superscript in the hard-target update indexes completed planning
rounds. There is no certified convergence theorem for that update as implemented.
Cached target-specific cuts remain valid after reweighting, but an aggregate
lower bound for the old weighted objective cannot certify the new one.
The code recomputes the bound for the current weights.

Fixed and minimax primary endpoints use the best fully audited training
incumbent available before the specified compute deadline. Adaptive primary
endpoints use the **last fully audited iterate**. Secondary averages combine
causal realization weights (the products of action probabilities defined in
Section 2) and replay the resulting policy; they do not
average conditional action rows. Their own decoder checks must finish in budget.
They are not substitutes selected after viewing evaluation outcomes.

The omitted background mass is exactly
\[
\beta=\frac{5369266971004237}{109684753201889280}
\simeq0.0489518.
\]
If \(U\) bounds the candidate's retained loss and \(B\) lower-bounds the
retained optimum over all feasible collectors, then
\[
L_{w,3}(\pi)\le U+\beta,\qquad
L_{w,3}(\pi)-\inf_\rho L_{w,3}(\rho)\le U+\beta-B.
\]
The second bound is valid because omitted losses are nonnegative, so \(B\)
also lower-bounds the full optimum. A retained solver gap of \(10^{-6}\)
does not, by itself, give full-loss regret of \(10^{-6}\).

A post-design refinement uses a decoder from the acquired record to the
**identity experiment**, whose output is the world label. If that decoder has
worst-world error \(R\), composing it with any known target law bounds every
target error by \(R\). This mathematical upper bound does not require physical
world revelation to be an available action.

Let \(D_3\) be the largest saved decoder upper bound over all deterministic
depth-three targets. The rich background's omitted depth-zero terms have
zero loss; its omitted depths one through three are bounded using
\(C_3=\min(D_3,R,1)\); deeper terms are bounded using \(R\). Their masses give
\[
\text{omitted loss}
\le 0.0208268\ldots\, C_3+\frac1{320}R.
\]
The exact fraction is retained in the certificate report. All 108 weighted
checkpoints passed this replay. At 40 seconds the resulting fixed-weight
full **fixed-prefix** regret upper bounds range from about 0.00243 to 0.00616.
This refinement took additional evaluation/replay work and is not credited
to the planning budget.

Finally, absolute loss and regret differ. A certificate \(L_{w,t}\le z\)
implies \(d_j(\pi,t)\le\min(1,z/w_j)\). A regret bound \(\eta\) only gives
the same expression with \(z=\inf_\rho L_{w,t}(\rho)+\eta\).
Nonzero optimal loss and small target weights can make that bound weak.
An absolute fixed-prefix loss upper bound also bounds the eventual loss of
every continuation retaining that prefix: later evidence can always discard
its new observations. Thus it gives a lower bound on every such continuation's
\(J_w\). But fixed-prefix **regret** is relative to the fixed-prefix optimum,
not the eventual optimum. These certificates neither identify a continuation's
eventual score nor establish that every continuation is sufficient.

Sources: [prospective protocol](../jw_computational_tests_2026-09-23/quality_corrected/PROTOCOL.md),
[executed planner](../jw_computational_tests_2026-09-23/quality_corrected/planner.py),
and [certificate refinement](../jw_computational_tests_2026-09-23/quality_corrected/certificate_refinement/README.md).

## 8. Optima, returned policies, and favorable Bayesian controls

An **objective optimum** is the best value over the declared full policy
space. There can be many policies with that value. A **selected policy** is
the particular policy a solver returns before a time limit.
Certifying its objective value near the optimum does not characterize what
every optimizer does on a different metric.

For static native objectives, a global lower bound \(B\) and a feasible
policy/decoder upper bound \(U\) give a numerical optimization-gap upper
\(U-B\). In our study, some saved incumbent records attach the lower bound
available when that incumbent first appeared. Later rounds provide a stronger
bound for the same unchanged objective. A post-design aggregation of already
checked, in-budget rounds shows that all 96 static 40-second endpoints have
training-gap upper bounds at most \(8.1\times10^{-7}\).
The apparently large original export gaps must not be treated as evidence
that these final static solves failed. Adaptive moving-weight objectives are
excluded from this aggregation.

Introduction Edits groups available, verified representatives of the same
finite objective in each class. Its displayed envelope is the smallest lower
and largest upper evaluation bound among those saved representatives.
It is neither a confidence interval nor a bound over **all** optima.
Different target orders can lead to different objective-optimal policies
with different four-step capability.

The Bayesian controls address this selection issue more directly. For reward
\(R\), let \(R_{\max}\) and \(R_{\min}\) be its best and worst attainable
values over three-interaction policies. A control at tolerance \(r\) tries to
minimize the training worst deficiency while satisfying
\[
R(\pi)\ge R_{\max}-r(R_{\max}-R_{\min}),
\]
up to a stated numerical allowance.
Thus 5% means five percent of the **attainable reward range**, not five
percent of the optimum reward or five percent native deficiency.

Introduction Edits uses an additional absolute slack \(10^{-10}\).
Our implementation subtracts
\(\max(10^{-10},r(R_{\max}-R_{\min}))\).
Both nominal zero controls therefore allow \(10^{-10}\) reward loss and
must not be described as exact arithmetic characterization of the optimizer set.
Both select using training targets, not the held-out depth-four audit.

These are favorable **returned controls**: give a reward nearly its best
value, then seek good short-target capability. They do not find the best
four-step policy in the entire near-optimal set, bound the worst such policy,
or establish that every near-optimal Bayesian policy is capable.

Even an exact improvement of the control's training criterion need not improve
its held-out criterion. In Introduction Edits' symmetric sensor class,
favorable nominal Brier selection changes four-step error from about 0.10817
to 0.10979, while minimax is about 0.10824. “Favorable” refers to the
training selection rule. The control is not guaranteed to win in evaluation.

Sources: [static-bound correction](../jw_computational_tests_2026-09-23/quality_corrected/static_certificate_aggregation/README.md)
and [Introduction Edits' primary comparison](../target_selection_followups_2026-09-23/PRIMARY_COMPARISON.md).

## 9. Why the comparison is informative, and where it is deliberately aligned

The primary training and evaluation questions are:

| Method | What chooses the three-interaction collector? | Common evaluation after selection |
|---|---|---|
| Information | Maximum expected information about the world by time three. | \(A_{3,4}\). |
| Posterior Brier | Maximum expected reduction of world-label quadratic Bayes risk. | \(A_{3,4}\). |
| Categorical count | Maximum expected cumulative declared observation-count bonus. | \(A_{3,4}\). |
| Finite weighted native | Minimum weighted deficiency on a declared short-target library. | \(A_{3,4}\). |
| Finite minimax | Minimum worst deficiency on that short-target library. | \(A_{3,4}\). |
| Favorable information/Brier | Minimum training worst deficiency subject to a reward constraint. | \(A_{3,4}\). |

If we optimized full \(A_{3,3}\) and then advertised a win on that identical
criterion, the minimax advantage would follow from its definition. The main
comparison evaluates depth-four targets that did not choose the collector,
weights, stopping rule, or favorable baseline representative.
Weighted averages additionally differ from the evaluation maximum.
Observed four-step reversals show that this distinction has consequences.

There is nevertheless deliberate alignment. Native methods are designed
around simulation error, and the evaluation also measures simulation error.
It is an operational criterion chosen because it expresses the project's
notion of reusable evidence, not a neutral vote of all possible preferences.
The models are supplied for planning and evaluation; these are not held-out
worlds or an unknown distribution shift. The held-out aspect is the target
experiment horizon and its exclusion from selection.

Reporting information/Brier return sacrifices and direct comparisons of the
records is therefore useful. It reveals what the chosen scalar evaluation
leaves out.

## 10. What the two completed packages actually found

### Introduction Edits: wider finite-objective comparison

The [completed follow-up](../target_selection_followups_2026-09-23/FINAL_SUMMARY.md)
covers 22 model classes: ten earlier structured/recurring cases and twelve
prespecified fresh random classes. They are not 22 identically distributed
independent replications of one statistical hypothesis. The main information,
Brier, count and two native comparisons have all 22 cases. One uniform-control
evaluation remains unavailable.

Here “tie” is the report's numerical classification within \(10^{-6}\);
it is not exact equality. Counts also respect envelopes across available
verified representatives.

| Native method | Comparator | Cases | Wins / numerical ties / losses |
|---|---|---:|---:|
| Minimax | Information | 22 | 21 / 1 / 0 |
| Minimax | Brier | 22 | 19 / 1 / 2 |
| Weighted 128 | Information | 22 | 20 / 1 / 1 |
| Weighted 128 | Brier | 22 | 18 / 2 / 2 |
| Minimax | Categorical count | 22 | 20 / 1 / 1 |
| Weighted 128 | Categorical count | 22 | 20 / 1 / 1 |
| Minimax | 5% Brier control | 17 | 15 / 0 / 2 |
| Weighted 128 | 5% Brier control | 17 | 13 / 0 / 4 |

The near-optimal evaluation extension completed all 70 available saved 1%/5%
information/Brier controls. Eighteen of the originally registered 88 policies
were unavailable. They remain missing rather than being imputed as wins,
ties or zero error.

To compare ordinary and 5% Brier fairly, restrict both to the **same 17 cases**.
A read-only recount of `COMBINED_STATUS.json` for this note gives:

| Native method | Ordinary Brier on those 17 | 5% Brier on those 17 |
|---|---:|---:|
| Minimax | 15 / 0 / 2 | 15 / 0 / 2 |
| Weighted 128 | 14 / 2 / 1 | 13 / 0 / 4 |

The broad minimax pattern survives this available control set. Weighted
comparisons become less favorable. Equal win counts do not imply unchanged
error magnitudes, and this says nothing about the five missing 5% Brier cases.
Comparing 18/22 directly with 13/17 would mix a control change with a coverage
change.

Important unfavorable cases remain:

- In the delayed class with parameters 0.25 and 0.1, Brier's four-step error
  is approximately 0.14324, minimax's 0.16622, and weighted native's 0.18157.
- In the symmetric irreversible class, the selected numerically certified
  weighted solution has
  approximately 0.24569 error versus 0.236 for information, Brier and minimax.
  Another saved representative with the same weighted optimum to numerical
  precision does better on the
  held-out metric. This is optimizer-selection sensitivity, not an all-optima
  failure theorem.
- Increasing the finite uniform weighted library from the older 16 targets
  to 128 yields ten wins and ten losses over the 20 available comparisons.
  More targets do not uniformly improve this separately measured maximum.

The earlier 15 September finite-native benchmark failed its prespecified
broad-benefit screen. This later, differently specified comparison does not
withdraw that result.

### Our study: fixed and changing weights under compute limits

The [completed computation study](../jw_computational_tests_2026-09-23/README.md)
uses twelve random parameter settings: four/eight worlds, three hidden states,
three Dirichlet concentrations, and **two independent seed families**.
Different parameter settings share those seeds. Twelve settings, repeated
budgets, many policies and millions of target solves are not twelve or millions
of independent random replications.

At each budget, entries below are native-method wins / losses / unresolved
against information on \(A_{3,4}\):

| Method | 2 seconds | 10 seconds | 40 seconds |
|---|---:|---:|---:|
| Fixed weights | 7 / 4 / 1 | 10 / 2 / 0 | 10 / 2 / 0 |
| Cost-adaptive weights | 4 / 7 / 1 | 10 / 2 / 0 | 10 / 2 / 0 |
| Hard-target weights | 4 / 7 / 1 | 9 / 3 / 0 | 10 / 2 / 0 |
| Finite minimax | 7 / 5 / 0 | 10 / 2 / 0 | 10 / 2 / 0 |

At two seconds, both adaptive methods also lose to uniform actions in eight
of twelve settings. Their short-budget weakness is a result to explain, not
a reason to discard those budgets. At forty seconds, cost adaptation beats
fixed weights in eight settings and loses four; hard-target adaptation splits
six/six. There is no uniform adaptive advantage.

Against the 5% Brier control, fixed weights win three and lose nine at two
seconds; at forty seconds they win nine and lose three. Against the 5%
information control the corresponding comparisons are four/eight and
eight/four. The controls materially reduce some apparent advantages.
Information and Brier produce identical acquired matrices in eight settings,
so their similar results are not independent corroborations.

A post-design reward replay finds that the 40-second fixed native collector
has less information reward in every setting, by approximately
0.00244–0.1198 bits, and less Brier reward, by 0.000619–0.04487.
It often improves the worst native audit while sacrificing these other
preferences. This is a tradeoff, not free improvement on every criterion.

The two packages must stay separate in reporting. Their finite weighted
objectives, model selections, solvers and timing protocols differ.
They are related evidence, not one pooled win-rate experiment.

## 11. What the 144 incomparability comparisons mean

This was a **post-design diagnostic**, with its own complete grid frozen
before its LPs ran. It used every one of our twelve settings, four primary
native methods and three baselines—information, Brier and uniform—at the
40-second checkpoint:
\[
12\times4\times3=144\text{ pairs},\qquad
288\text{ directed decoder problems}.
\]
Both source and target were saved complete **length-three acquired records**,
not the earlier depth-four evaluation target set.

For each pair \(E_N,E_B\), it measured both
\(\delta(E_N,E_B)\) and \(\delta(E_B,E_N)\). All 288 directions passed
independent witness replay. In every pair both numerical lower bounds exceeded
\(10^{-6}\); the smallest was about 0.00350.
All 144 pairs therefore show numerical same-time incomparability.

This includes all 127 native-method wins and all 17 losses on the scalar
depth-four audit among those pairs. A native collector with a lower worst
depth-four error still misses something that the baseline record can reproduce;
the baseline also misses something the native record can reproduce.
Thus the empirical conclusion is not that native planning has acquired a
uniformly better experiment.

The boundaries matter:

- The comparisons are numerical, using feasible decoder and decision-loss
  witnesses; they are not exact or outward-rounded proofs.
- They compare two finite records at the same collection time. They establish
  no eventual relation between arbitrary continuations.
- The 144 pairs exclude favorable reward controls and adaptive averages.
  Some baselines coincide, so 144 is not a count of independent discoveries.
- Incomparability is consistent with strict monotonicity: a strictly monotone
  scalar must respect strict dominance, but can prefer either of two
  incomparable experiments.

Sources: [diagnostic protocol](../jw_computational_tests_2026-09-23/quality_corrected/same_time_order/PROTOCOL.md)
and [complete results](../jw_computational_tests_2026-09-23/quality_corrected/same_time_order/results/REPORT.md).

## 12. Computation and verification are part of the evidence

**Planning computation** includes model geometry, target construction,
optimization, target queries used for selection, decoder checks needed to
accept an incumbent, and adaptive update/cache work. Our 2/10/40-second
checkpoints charge those operations. Imports and certificate serialization
are separately recorded. A policy whose required evidence arrives after a
checkpoint cannot be backdated into it.

**Evaluation computation** holds the policy fixed and solves decoder problems
for the held-out targets. It can be much more expensive than producing the
policy. It is reported separately and was not used to select checkpoints.
The certificate refinement and record-to-record diagnostics are additional
costs, not planning speedups.

At the 40-second endpoint, median policy-and-required-evidence availability
was approximately 11.2 seconds for fixed weights, 6.8 seconds for minimax and
38–39 seconds for adaptive methods. Information/Brier DP took about five
milliseconds in these small supplied-model problems, excluding startup/output.
A common compute allowance does not mean equal consumed computation or equal
practical efficiency.

An accepted deficiency interval has two explicit witnesses. A stochastic
decoder \(G\) gives an upper bound
\[
u=\max_q\operatorname{TV}((EG)_q,F_q).
\]
A probability vector \(\lambda\) over worlds and entries
\(0\le b_{qy}\le\lambda_q\) give a lower bound
\[
l=\sum_{q,y}F_{qy}b_{qy}
 -\sum_x\max_y\sum_qE_{qx}b_{qy}.
\]
Here \(\lambda\) is a dual witness, not the Bayesian planning prior.
Independent checkers reconstruct the actual source and target probabilities,
check these objects and recompute the values. The required per-target bracket
width is at most \(2\times10^{-7}\). Comparing methods uses the larger
\(10^{-6}\) separation threshold.

For a completed target sweep, \(\max_j l_j\) and \(\max_j u_j\) bound its
maximum deficiency. In an incomplete sweep, the largest found lower bound
is still a valid adverse witness; the largest found upper bound is **not**
an upper bound on unseen targets. A separate global bound is required.

Our corrected study has 132 planning executions, 540 scientific endpoint rows,
and 300 distinct acquired experiments. All 300 received completed audits over
32,768 targets: 9,830,400 intervention checks. Saved per-target witnesses
passed independent replay. Reuse applies only to byte-identical acquired
matrices within the same model after policy checks; it never reduces the
charged planning work. The independent reporting checker passed 55,013
checks. These are floating-point certificates, not new Lean proofs.

Introduction Edits has a different audit boundary. Its archive audit passed
all 976 recorded runs, including retained checkpoints from failed/interrupted
runs. It reconstructed 2,495 policy checkpoints, 2,160 compact master
certificates, 5,968 saved hardest/revelation witnesses and arithmetic for
16,342,912 profile entries. **The original archive did not retain a decoder
witness for every profile entry.** This replay does not independently
reconstruct all old per-target solves. Its 17 completed recovery-of-coverage
jobs passed their corresponding saved-certificate audit. The new recovery and
70 near-optimal evaluation sweeps retain and replay every target witness.
The main figure must preserve these differing verification scopes.

Failures and corrections also remain part of the record:

- Our initial quality run was oversubscribed: 96 visible CPUs hid a shared
  cgroup allowance of 10.2 CPU-equivalents. All 132 planning jobs were repeated
  unchanged at eight workers. The old run remains preserved.
- Two originally proposed seed families were exposed during the feasibility
  pilot and were retained as design data. Confirmation used the next unused
  families, selected without capability outcomes.
- The corrected audit coordinator later exited with signal 143. Completed
  and orphan-worker outputs were independently validated and the remaining
  registered work recovered. Final coverage is complete; the interruption
  did happen, its cause is unknown, and some original process timing/exit
  telemetry is unavailable.
- The GPU pilot retained 70 accuracy rejections among 468 replayed witnesses.
  Feasible but insufficiently tight bounds were not accepted. The tested
  persistent CPU decoder was the useful backend for the main work.
- The backend comparison retained nine monolithic timeouts. Decomposition
  helped larger cases but could be slower on small ones. Cached cuts reduced
  incremental reweighting cost in 53/54 comparisons; cache construction and
  preceding solves are additional work.
- Introduction Edits' five distinct recovery evaluations ended with four
  verified completions and one failure. The missing uniform case is
  `fresh_hmm_2026100801_q8_s3_c0.2`. The original failures remain visible.
  Its 70 available near-optimal evaluations all finished, but the other
  18 registered control policies remain unavailable.

These details justify confidence in specified computations and honest coverage
accounting. They do not supply a general runtime guarantee or statistical
confidence interval for performance on new environments.

Sources: [our final review](../jw_computational_tests_2026-09-23/FINAL_REVIEW.json),
[resource correction](../jw_computational_tests_2026-09-23/quality_corrected/RESOURCE_CORRECTION.md),
[backend study](../jw_computational_tests_2026-09-23/backend_validation/README.md),
[GPU pilot](../jw_computational_tests_2026-09-23/gpu_audit_pilot/README.md),
[Introduction Edits' audit scope](../target_selection_followups_2026-09-23/README.md)
and [final coverage](../target_selection_followups_2026-09-23/FINAL_SUMMARY.md).

## 13. Prospective evidence versus later diagnostics

“Post-design” describes when an analysis was chosen. It does not mean its
arithmetic is invalid. It does limit how it can be presented as confirmation
of a previously specified empirical claim.

| Component | Status and interpretation |
|---|---|
| Our model grid, methods, 2/10/40-second checkpoints and depth-four evaluation | Prospectively specified before confirmation-model comparisons, with documented resource/seed corrections. |
| Our 0/1/5% information/Brier controls | Prospectively specified policies and objectives. |
| Complete table of our native-versus-control comparisons | Layout added after the primary preview; it uses all prespecified controls without changing policies or metrics. |
| The 144 same-time comparisons | Post-design diagnostic; complete grid frozen before those decoder solves. |
| Replaying information/Brier return on all 540 endpoints | Post-design diagnostic; no policy optimization. |
| Stronger full fixed-prefix certificate bounds | Post-design application/replay; additional computation, unchanged policies and coefficients. |
| Static in-budget lower-bound aggregation | Post-design metadata correction/aggregation of existing checked rounds; unchanged policies and outcomes. |
| Introduction Edits' original target-selection campaign | Frozen prospective queue, stopped at its resource limit with failures and missing work retained. |
| Its 17 completion jobs and saved-policy recovery | Explicit subsequent completion/recovery with preserved provenance and unchanged objectives. |
| Its 70 near-optimal depth-four evaluations | Separately registered evaluation extension of all available eligible policies; absent from the original queue. |
| Main figure recommended here | Retrospective presentation of completed evidence, not a newly preregistered superiority test. |

The controlled [SAFE/FAST study](../jw_computational_tests_2026-09-23/safe_fast/README.md)
adds a distinct mechanism check. Its 2,448 prospective cells and 356 literal
record cross-checks separate a moving objective from an inaccurate solve of a
fixed objective. The infinite-world moving-emphasis examples retain a fixed
capability loss despite tightly solved small optimization problems. Its fixed
finite-world controls preserve information gain's success once enough bits
can be collected. The special compression is a written argument with numerical
and exact-rational checks, not a general efficient native optimizer.
It should not be pooled into the random-model performance counts.

The justified conclusions are therefore specific: objective choice changes
finite acquired capability; transfer to a longer target horizon often helps
in the reported native comparisons but has reversals; near-optimal baseline
selection matters; short compute budgets can hurt; and scalar audit wins need
not be dominance. These results establish neither all-optima superiority,
eventual completion, interaction-only learning, nor broad population superiority.

## 14. One recommended main experiment and figure

**Use the completed 22-class, three-interaction collection/four-interaction
evaluation comparison as the main empirical ending.** A suitable plain-language
title is: “Which short collection objective preserves longer experimental
capabilities?”

It advances the paper beyond the startup-only figure because it optimizes
full-history collectors across multiple classes and compares actual evidence
distributions. The startup study can remain in the supplement as a sampled
learning diagnostic. The replacement must be called supplied-model planning;
it would not be a stronger demonstration of learned exploration.

I recommend one figure with two aligned panels:

1. **Absolute capability across all 22 classes.** One row per class in the
   original manifest order. Plot \(A_{3,4}\) for information, posterior Brier,
   categorical count, uniform actions, weighted 128 and minimax. Use the
   verified interval envelopes, marking the missing uniform entry and
   visible spread among saved representatives. Distinguish the ten earlier
   cases from the twelve fresh classes. Do not rank rows by the native advantage.
2. **Sensitivity to favorable Brier selection.** On the same rows, plot
   \(A_{3,4}(\pi_B)-A_{3,4}(\pi_N)\) for each of the two native methods,
   using ordinary Brier and the 5% Brier control. Positive means the native
   method has smaller error. Mark the five missing controls explicitly.
   Keep the nominal-zero and 1% results, and the analogous information controls,
   in a directly linked supplementary table. Differences use interval
   subtraction \([l_B-u_N,u_B-l_N]\), preserving representative envelopes.

The first panel has 131 available method/class points out of 132.
The second panel makes the main selection sensitivity visible rather than
leaving it behind a headline win count. If the layout needs more space,
reduce labels or move explanatory text; do not select favorable classes or
replace full envelopes with the best held-out representative.

The concrete, falsifiable descriptive claims for this figure are:

- **Short-target optimization sometimes transfers.** A majority of the declared
  classes show smaller four-step worst error for each native method than for
  the ordinary information and Brier representatives. Report all counts and
  reversal cases. This would be contradicted by the complete paired records
  not supporting that majority at the declared numerical threshold.
- **Transfer is not guaranteed.** The delayed and irreversible cases exhibit
  losses or representative sensitivity. A claim of universal improvement is
  already contradicted.
- **Some advantages survive the computed reward-tolerance control.** On the
  same 17 available 5% Brier cases, minimax has 15 wins/two losses and weighted
  native 13 wins/four losses. The weighted comparison is weaker than its
  ordinary-Brier comparison on those same cases. This is about the saved
  training-selected controls, not the entire near-optimal policy set.

These are statements about this completed finite benchmark, not a
preregistered statistical superiority claim. The caption should explicitly
state \(t=3\), training depth three, evaluation depth four, supplied candidate
models, numerical/representative envelopes, and the distinction from eventual
\(J_w\). It should say that a scalar improvement need not be dominance,
with the 144-pair diagnostic as separate supporting evidence.

The computation-budget study belongs in a short supporting paragraph and
supplementary budget plot, with information/Brier runtimes and adaptive
two-second failures visible. Its methods are different from `weighted128`.
Do not attach its timing or rich-background certificates to the 22-class
policies without a separate matching calculation.

This recommendation can be implemented from
[COMBINED_STATUS.json](../target_selection_followups_2026-09-23/COMBINED_STATUS.json)
and [combined_figure_data.csv](../target_selection_followups_2026-09-23/combined_figure_data.csv);
the control pairs and their exact result/check paths are in the JSON.
The existing [candidate caption](../target_selection_followups_2026-09-23/FIGURE_CAPTION.md)
does not yet present the completed 1%/5% extension's outcomes,
so it needs a focused update at the figure milestone.
There is no need to rerun the completed campaign to decide whether this figure
is more informative than the current startup-only ending.

## 15. Confirmation that would materially help

First use the saved data to verify the exact figure joins, show common-case
ordinary/control comparisons, and inspect every displayed representative's
optimization and audit status. This is cheap reporting work. The current
complete certificates and source bindings support it without numerical workers.

If stronger conclusions are wanted, prioritize the experiment that addresses
the actual missing premise:

| Desired stronger conclusion | Useful next confirmation |
|---|---|
| The control comparison covers the declared grid | Complete the 18 unavailable original near-optimal policies/evaluations under a new frozen completion protocol; retain original failures and source definitions. Recover the remaining uniform audit if displaying uniform throughout. |
| The observed pattern generalizes beyond these classes | Freeze the methods, weights, budgets and figure metrics, then evaluate genuinely fresh independent model seeds. Existing outcomes are design evidence for that new confirmation. |
| The advantage survives a longer acquisition budget | Run a matched longer-collection comparison using compatible completed checkpoints first. Distinguish collection horizon from target horizon and solver time; preserve the delayed counterexample. |
| Adaptive computation makes a fixed native score cheaper | Compare target scheduling/caching against the validated fixed solver with unchanged full coefficients, certified omitted work and all setup/search costs charged. Current adaptive-weight results do not test this. |
| Every reward optimizer has a stated capability property | Bound the evaluation across the whole optimal/near-optimal policy set, or prove an appropriate theorem. Additional favorable representatives do not answer that quantifier. |

For a larger-horizon experiment, a feasibility pilot should freeze coverage
before capability outcomes. Exhaustive depth-five targets number over two
billion, so a partial search must retain a valid global upper bound and be
labelled partial. The validated decomposition and persistent CPU decoder are
useful starting points, with independent replay preserved. Incremental cache
speedups exclude cache construction unless it is explicitly charged.

I would not delay the first replacement-figure review for a new expensive
campaign. The completed data already support a substantive, qualified ending.
Fresh confirmation becomes important if the intended claim expands from
“these objectives select different finite capabilities, with measured
tradeoffs” to a broader performance or efficiency promise.

## Evidence boundary of this explanation

This pass reread the protocols, actual reward/planner/evaluator definitions,
current paper/theory routes, relevant formal support boundaries and saved
reports. It recomputed the matched-subset counts from the final comparison
JSON. It did not rerun numerical optimization, exhaustive witness checking or
Lean, and it does not certify subsequent shared-tree changes.

For an exact record of the principal snapshots used here:

| Record | SHA-256 |
|---|---|
| Our `quality_corrected/summary/summary.json` | `6f337654628056074c7926a00dfac54d6ec7ac3baaf9f55c769b99d307950c5e` |
| Our `same_time_order/results/SUMMARY.json` | `b1a0b8148760b1d0c141122dcf2fdb05e3789f2f07420bf18ad105be66282360` |
| Our `static_certificate_aggregation/CHECKS.json` | `4f1fd43f1784b8353363726a0e19daaded562c08efcb9ebe1e162f3de826393f` |
| Introduction Edits' `COMBINED_STATUS.json` | `d57d9be8cd7562f2bd97ba942375bb9d592e7c7eb56bda2f6261d3682c7813ea` |
| Introduction Edits' `FINAL_SUMMARY.md` | `c15335a496815013a363c3657fa304338b72be1256d06a8ff841e13abe60ed8a` |

Only this explanation file was authored by this pass. No manuscript, Lean,
support ledger, numerical-worker, commit or push action was taken.
