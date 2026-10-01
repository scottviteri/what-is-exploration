# Review of the proposed empirical ending and confirmation

23 September 2026. Requested by Introduction Edits at the lead author's authorization.
This is the second explanatory commission. The completed
[first explanation](MISSING_CITATIONS_EXPLANATION.md) supplies the full definitions,
proof boundaries, computational history, and interpretation of both experimental
packages. This review reads the current candidate, rather than treating that
earlier figure recommendation as binding.

**Recommendation:** the twelve-setting candidate is defensible as a retrospective
comparison of finite capability, posterior reward, and planning cost. It is a
substantial replacement for the startup-only experiment. Make the unequal reward
sacrifice visible in the main figure, narrow the incomparability sentence, and
carry the post-design disclosure into the caption. No expensive new experiment is
necessary to make that descriptive presentation honest. Eight fresh seed families
are a reasonable subsequent test of repeatability, but do not answer whether the
native method improves capability at comparable posterior reward. Decide which
question the next run should answer before launching it.

I reviewed [README.md](README.md), [CAPTION.md](CAPTION.md),
[CONFIRMATION_DRAFT.md](CONFIRMATION_DRAFT.md), the plotting source and saved data,
and visually inspected [the main candidate](CANDIDATE_FIGURE.pdf) and
[the tradeoff diagnostic](TRADEOFF_DIAGNOSTIC.pdf). The owner subsequently supplied
[FIGURE_CHOICE.md](FIGURE_CHOICE.md), the [22-class caption](CAPTION_22.md), and
[its PDF](CANDIDATE_22_CLASSES.pdf); I read those and inspected that PDF too.
The detailed new arithmetic checks below concern the twelve-setting candidate.
This review runs no optimizer, numerical audit campaign, training, or Lean build.
It changes only this note.

## 1. Precisely what the plotted objects mean

A world is one candidate controlled environment law. A class contains four or
eight candidate models, each with three hidden physical states and a binary
action/observation interface. The planner knows these candidate models, including
their common initial physical state; it does not know which model is actual. A
policy chooses actions from its preceding action–observation record. Its
three-interaction record has three actions and three observations. The experiment
\(K_{\pi,3}\) is the distribution of that record in **each** candidate world, not
one sampled record and not the posterior from one realization.

A target is another allowed policy, here executed for four interactions. A decoder
is a randomized map from the collected record to a simulated target record. It
knows the requested target and the supplied model class, but not the actual world.
The same decoder must work in every world. Write

\[
\delta(E,F)=\inf_G\max_Q\operatorname{TV}(E(Q)G,F(Q)).
\]

The direction is **from the experiment on the left to the experiment on the
right**. Zero means that the left experiment can reproduce the right experiment
exactly through an allowed decoder. The plotted audit is

\[
A_{3,4}(\pi)=\sup_\sigma\delta(K_{\pi,3},K_{\sigma,4}).
\]

It asks for the hardest four-interaction target, allowing a different decoder for
each target. Smaller is better on this scalar. The collection horizon three,
target horizon four, and forty-second planning allowance are three different
quantities. The first two concern interaction with the environment; the last
concerns computation before collection. Decoder/audit computation is additional.

The optimization/evaluation separation in the candidate is real:

| Method | What selects its three-interaction collector | What the plotted audit adds |
|---|---|---|
| World information gain | Expected reduction in entropy of the world posterior under the uniform world prior | Worst-world simulation of every four-interaction target |
| World-posterior Brier improvement | Expected increase in the squared Euclidean norm of that posterior | The same four-interaction audit, with no world prior inside its worst-world maximum |
| Fixed native weights | Retained weighted deficiencies to 131 training encodings of length at most three | Targets of length four, not used to select the policy or weights |
| Finite minimax | Largest deficiency over the same finite training library | The same longer-target audit |
| Favorable posterior controls | Minimize the training-library maximum subject to a posterior-reward constraint | Longer targets not used by that constrained selection |
| Uniform actions | No optimization | A reference acquired experiment |

The native objectives deliberately have a closer conceptual connection to the
evaluation than posterior information does. Holding out target depth makes this
more than reporting their training objective, but does not make the evaluation
an objective-neutral test of every possible use of evidence. It tests the paper's
specified capability criterion. It establishes neither new-model generalization
nor performance at arbitrary horizons.

The Brier variable here is the **world label**. It is not next-observation squared
prediction loss, physical-state prediction, or a learned prediction-error bonus.
The information variable is also the world label, not predictive surprisal.
These are exact Bayesian objective comparisons on supplied models. The paper must
retain that wording when importing the figure; a citation to a proper scoring
rule does not identify every use of that rule with a published intrinsic-learning
algorithm or with a different predicted variable in the theory table.

The fixed native planner minimizes a finite retained sum. The countable background
also defines a full sum at collection time three; eventual \(J_w\) uses eventual
deficiencies and is a third object. The reported refined regret bounds
0.00243–0.00616 concern the full **fixed-time** sum, with extra certificate work.
They are not eventual-regret bounds. An absolute prefix-loss upper bound can also
bound the eventual loss of any continuation retaining that prefix, but this does
not convert a fixed-time optimality gap into an eventual optimality gap or prove
complete exploration.

## 2. The 21.17%-versus-5% comparison is the central interpretation

For one model class, let \(R_B(\pi)\) be expected three-interaction world-posterior
Brier improvement. Let \(R_B^{\max}\) and \(R_B^{\min}\) be its largest and smallest
values over the allowed three-interaction policies. The reported normalized
sacrifice is

\[
r_B(\pi)=
\frac{R_B^{\max}-R_B(\pi)}{R_B^{\max}-R_B^{\min}}.
\]

Thus “21.17%” is a median of **class-specific fractions of the attainable reward
range**. It is not 21.17% of optimal reward, an error probability, the theoretical
range of all Brier scores, or a percentage of the information in the world. The
denominator is obtained from the same allowed finite-horizon policy problem.

At forty seconds, fixed native weighting sacrifices 11.08–38.96% of that range
across the twelve settings, with median 21.17%. Every 5%-Brier control in this
comparison sacrifices approximately 5%, within the implementation's numerical
allowances. Consequently, the control has **better Brier reward in every setting**.
The native policy is not being compared with an equally costly concession in
Brier value.

This does not make the comparison illegitimate: the objectives are meant to value
different things. It determines its interpretation. In nine cases fixed native
has the smaller four-step audit error, at the price of worse Brier reward. In three
cases the 5%-Brier control has **both** better Brier reward and smaller audit error.
The latter are losses for fixed native on both measured scalar criteria:

| Setting | Fixed native Brier sacrifice | 5%-Brier sacrifice | \(A_{3,4}(\text{Brier5})-A_{3,4}(\text{fixed})\) |
|---|---:|---:|---:|
| Four worlds, concentration 0.2, seed 926104 | 18.328% | 5.000% | −0.0323642 |
| Four worlds, concentration 1, seed 926104 | 12.327% | 5.000% | −0.0028748 |
| Four worlds, concentration 5, seed 926104 | 28.418% | 5.000% | −0.0103494 |

These values are read-only arithmetic from [figure_data.csv](figure_data.csv).
Their differences are much larger than the corresponding numerical intervals.
Two-score dominance is **not** Blackwell dominance: two favorable numbers do not
exhibit a decoder capable of simulating the entire other experiment. The existing
144 bidirectional tests do not include the 5%-Brier controls, so they do not settle
the order of these particular pairs either.

The median audit reduction for fixed native changes from 0.023019 against ordinary
Brier to 0.000885 against the 5% control. A nine-to-three win count alone conceals
that change in magnitude and the greater native sacrifice. The small median is
descriptive; no prespecified practical-equivalence threshold makes it a proved
tie or a universally negligible difference.

The favorable control is also not “Brier plus arbitrary small training error.” It
is deliberately chosen by a **second optimization**, using native training targets,
inside the allowed posterior-reward set. Its strong performance establishes an
attained favorable tradeoff. It does not show that a typical approximate Brier
learner, every near-optimal Brier policy, or an unassisted Brier implementation
will select that tradeoff. That secondary planner and its cost belong in the
description.

The current README correctly uses the actual twelve-setting constraint,

\[
R(\pi)\ge R^{\max}-\max\{10^{-10},r(R^{\max}-R^{\min})\}.
\]

This matches
[planner.py](../jw_computational_tests_2026-09-23/quality_corrected/planner.py),
lines 115–116. The earlier additive-slack formula belonged to the other package;
[FIGURE_CHOICE.md](FIGURE_CHOICE.md) now records the correction. It is resolved,
not an outstanding criticism. In the caption, however, call the zero arm
**nominal zero, with the stated numerical allowance**. “At most 0%” is not its
literal constraint. More generally the saved controls are numerical feasible
representatives, not exact symbolic optima.

Make this comparison visible in the main image. Panel (c)'s x-axis currently
covers the controls' 0–5% sacrifice, while its zero comparison line represents
fixed native policies sacrificing 11–39%, outside that axis. The caption discloses
this, but the image alone can suggest a matched sacrifice. At minimum annotate
that line with the native range and median. Better, put native and Brier-control
points on common Brier-sacrifice and audit coordinates, paired by setting, using
the already saved rewards and errors. Mark the three losses on both scores.
Do not label the resulting sampled points a Pareto frontier.

## 3. What incomparability and small optimizer gaps do—and do not—establish

For two collectors \(\pi\) and \(\rho\), same-time incomparability means both

\[
\delta(K_{\pi,3},K_{\rho,3})>0,
\qquad
\delta(K_{\rho,3},K_{\pi,3})>0.
\]

Neither three-interaction record experiment can exactly replace the other by
world-independent random decoding. One may still have smaller \(A_{3,4}\): that
number compresses an entire capability profile into one worst-target error. It
does not record every direction in which one experiment preserves more evidence.
There is no contradiction with the strict-order theorem: incomparable objects
have no prescribed ranking from a monotonicity implication.

The exact tested grid is twelve settings × four native methods
(fixed, minimax, cost-adapted, hard-target-adapted) × three ordinary controls
(information, Brier, uniform), all at the forty-second endpoint: **144 pairs**.
The smallest directional lower witness bound is about 0.00349552. The supporting
plot displays the 24-pair subset for fixed/minimax versus ordinary Brier. Its
axis directions are correct.

Replace the main caption's “Every tested native and baseline record pair” with a
sentence giving that scope or a clear pointer to it. In particular, the 144 tests
do not cover the reward-constrained controls shown in panel (c), earlier
checkpoints, or arbitrary continuations. The main image's footer should also say
**numerically incomparable**, as the caption already does. These are checked
floating-point witness calculations, not exact outward-rounded interval proofs,
new Lean theorems, or statistical confidence intervals. They give no eventual
incomparability result: later collection might erase a finite-prefix difference.

The static forty-second training gaps, all at most \(8.1\times10^{-7}\) after
valid lower-bound aggregation, support near-global optimality of the returned
policies for their respective **finite training problems**. They do not enumerate
all optimizers or bound variation in the held-out audit across all optimizers.
The ordinary posterior dynamic program likewise returns a representative. The
nominal-zero constrained arm helps expose favorable selection near the reward
optimum, but is not a characterization of the whole optimizer set.

These distinctions should remain explicit if the experiment follows a theory
table with all-optima statements. The experiment studies numerical selected
policies. It does not empirically establish all-optima counterexamples, and its
finite losses are not evidence that every computable approximation to \(J_w\)
must have the same properties as information gain.

## 4. Figure choice and concrete presentation corrections

I now support the twelve-setting figure as the leading candidate **for the focused
capability/reward/computation question**, with the full 22-class plot as a companion.
This updates the first explanation's broader 22-class recommendation in response
to the actual standalone figures and explicit comparison in FIGURE_CHOICE. The
reason is complete controls, rewards tied to the very same policies, and complete
per-target witness replay—not a larger favorable win count. The 22-class choice
remains reasonable if breadth of objectives and constructions is the priority.

The Commission 02 addendum asks for an explicit main-figure comparison. These are
the scientific and presentational reasons for that recommendation:

| Decision | 22-class candidate | Twelve-setting candidate |
|---|---|---|
| Strongest main question | Which capabilities do different finite objectives retain across sensors, delay, irreversible choice, and random models? | How do capability, posterior reward, and planning cost trade off on a consistently specified random-model grid? |
| Objective breadth | Adds the source-qualified categorical count reward to information and posterior Brier, alongside the native objectives and uniform control. This is a substantive advantage for a paper comparing intrinsic rewards. | Compares two world-posterior objectives with native objectives and uniform actions. It should not be presented as a broad numerical survey of all rewards in the theory table. |
| Coverage of favorable posterior controls | Five of the 22 classes lack the 5%-Brier control; one uniform evaluation is unavailable. Missing entries remain informative limitations, even with all rows displayed. | The information/Brier 0/1/5% control grid is complete for every setting, permitting comparisons at a constant denominator and with actual reward sacrifice available. |
| Verification coverage | Original exhaustive profiles have saved hardest/revelation witnesses and profile arithmetic, but not all per-target decoder witnesses; the newer control/recovery audits have full replay. | Every depth-four target has a saved witness replay for the acquired experiments used in this study. This is stronger verification coverage, not broader environmental generality. |
| What a reader can explain from one figure | Structured rows connect a change in objective to recognizable mechanisms, including delay and irreversible choices; saved-representative envelopes also expose selection sensitivity. | A common generator and complete controls isolate the comparison more cleanly, including the cost of relinquishing posterior reward. Interpreting the specific environment mechanisms is harder. |
| Main burden on the caption | Explain heterogeneous classes, incomplete controls, representative envelopes, and different archive verification coverage. Twenty-two rows are also visually demanding at manuscript width. | Explain the two independent seed families, finite-compute selection, and the unequal reward sacrifice. Keep solver details secondary so the ending stays about intrinsic objectives. |

For the current proposed ending, **complete reward controls and a clear accounting
of what each policy gives up are decisive**. This supports twelve settings as the
main figure and the whole 22-class figure as substantive supporting evidence. It
does not mean that random classes are scientifically preferable to structured
examples, or that an archive without every decoder witness is invalid. If the
ending is instead meant primarily to connect the theoretical counterexamples to
several recognizable environment mechanisms and an additional reward family,
choose the 22-class figure and accept its explicit missingness. That is a
different, legitimate scientific emphasis, not a choice to make after comparing
which image looks more favorable to native methods.

The extra count baseline is specifically the documented categorical observation
density-model specialization: the finite return sums
\(1/\sqrt{1+N_{\mathrm{previous}}(o)}\), using counts before the current observation
and raw observation labels. Its presence broadens reward coverage; it does not
turn this finite model-class test into an evaluation of the CTS Atari learner or
of every pseudo-count method. The caption must retain that source qualification.
Adding this arm to the twelve-setting study would require a separately specified
run; its results cannot be imported from the different 22 classes.

The weighted objectives must also retain separate names. In the 22-class study,
the native weighted loss is the uniform mean over 128 deterministic depth-three
targets. In the twelve-setting study, it is the retained sum on 131 encodings
(those targets plus three uniform-action targets), with the specified foreground
and countable-background coefficients left unrenormalized. These are different
optimization problems, even though both are evaluated by the same form of
\(A_{3,4}\). Do not combine their weighted-method win counts, treat them as repeated
runs of one weighted objective, or attach the twelve-setting timing, background
certificate, or incomparability results to the 22-class policies. The tiny slack
conventions remain distinct too: twelve settings use the maximum with
\(10^{-10}\); the 22-class control subtracts the percentage-range loss **plus**
\(10^{-10}\). Both are now described correctly in their respective files.

The 22-class candidate usefully preserves the delayed reversal, irreversible-case
representative spread, count objective, missing uniform evaluation, and five
missing 5%-Brier controls. Its caption correctly distinguishes envelopes of saved
representatives from all optima and statistical intervals, and compares ordinary
and favorable Brier on the same seventeen available cases. Do not transfer the
twelve-setting reward sacrifice, compute timings, rich-background certificates,
or 144 incomparability findings to those different policies. Its original archive
also has the explicitly narrower witness-replay boundary. No pooling is justified.

For the twelve-setting main figure, prioritize three messages: absolute capability
errors for all settings; the Brier-reward tradeoff including favorable controls;
and the cost of finding the selected policies. The current absolute-error panel
already retains the two unfavorable native cases. If space is tight, put the
planning-budget curves in supporting material before hiding the reward tradeoff.
The paper's contribution concerns intrinsic objectives; the implementation study
should support that comparison rather than become the main subject.

Specific remaining corrections are small but consequential:

- Change “three collected observations” to “three interactions” or “three
  action–observation pairs”; the record includes the chosen actions.
- Change “Same evidence budget” to “Same collection length.” Equal numbers of
  interactions do not imply equal information in the resulting experiments.
- Replace “Reward concessions reduce the gap” with “Effect of posterior-reward
  concessions,” or explicitly qualify the descriptive median trend. Increasing
  the allowed concession relaxes the training constraint; it does not imply
  monotonic improvement on the held-out depth-four audit for every setting.
- Add “Post-design presentation of completed data” to the main caption or image.
  “Completed data” alone does not disclose that this presentation and its
  emphasis were chosen after seeing the results. The supporting diagnostic
  already has the stronger disclosure.
- Preserve the numerical-versus-statistical interval distinction and the two
  independent seed families in the caption. Targets, methods, and the six
  parameter combinations per family are not additional independent replications.
- Describe the supporting plot as neither record **exactly** simulating the
  other at this collection time, and give the tested-pair scope. Its current
  axes implement the stated direction correctly.

The plots are readable at their supplied standalone sizes. Readability after
reduction to the manuscript width still needs inspection during a future
integration, especially the footers and multi-part caption. I found no sign
reversal, dropped unfavorable twelve-setting row, or data-join error in the main
plotting arithmetic. Its median-x/median-y points are explicitly described as
summaries, not one policy or a proved frontier; preserve that qualification.

## 5. What eight fresh seed families would actually confirm

The proposed confirmation does several things correctly: it fixes unused seeds
before outcomes, keeps all six parameter settings per family, freezes the models'
interface and native weights, makes ordinary and 5%-Brier comparisons obligatory,
retains other methods and failures, and charges audit work separately. Excluding
adaptive-weight heuristics uniformly before new outcomes is appropriate for this
question; their existing short-budget failures remain supporting evidence.

Let \(\Delta_{s,c}=A_{3,4}(\text{comparator})-A_{3,4}(\text{fixed})\) for seed
family \(s\) and parameter combination \(c\). The proposed statistic is

\[
\bar\Delta_s=\tfrac16\sum_{c=1}^{6}\Delta_{s,c},
\qquad
\bar\Delta=\tfrac18\sum_{s=1}^{8}\bar\Delta_s.
\]

This is an equal-weight summary of the declared parameter mixture. It need not
represent how frequently those environments occur in an application. Carrying
LP witness bounds through those averages bounds numerical uncertainty for the
realized grid. It does not create a confidence interval for a generator population.
Eight families are more informative than two, but eight is a resource/design
choice here, not a power or precision guarantee.

Applying the proposed family aggregation to existing saved endpoints gives:

| Existing seed family | Mean improvement against ordinary Brier | Mean improvement against 5%-Brier |
|---|---:|---:|
| 926103 | +0.036880637 | +0.010203877 |
| 926104 | +0.015469479 | −0.001501247 |
| Equal mean of the two families | +0.026175058 | +0.004351315 |

Each family's sign is separated from zero by its numerical bounds. These are
new summaries of existing data, **not** new experimental results or independent
confirmation. They show why two seed families are insufficient for a stable
repeatability story: the favorable-control comparison already changes sign
between families. The all-setting median of +0.000885 and the family-averaged
mean of +0.004351315 answer different summary questions; neither should be selected
after fresh outcomes because it looks better.

Forty-second endpoints are a sensible primary audit choice. The existing static
training problems have small gaps there, while early native checkpoints often
perform poorly. Saving two- and ten-second checkpoints is cheap compared with
their exhaustive evaluation. Auditing only the forty-second policies, however,
does **not** independently confirm the planning-budget curves. Keep those as old
descriptive evidence unless the prospectively specified early-audit extension is
also completed.

The proposed 528 audits before deduplication and roughly 36 single-worker hours
are reasonable scale estimates from the completed study, not promises. Planning,
long tails, validation, retries, and process overhead remain additional. Existing
GPU pilots do not justify switching the confirmation's numerical backend for an
assumed speedup. Likewise, depth five is a different computational problem, not
a routine alternative to adding seed families.

Before freezing the protocol, close these reporting details:

1. **Missing endpoints and the estimand.** Retain the planned denominators of six
   settings and eight families. Do not average only completed cases after the
   twelve-hour stop. Use valid partial audit brackets, or the trivial
   \(0\le A_{3,4}\le1\) if no tighter bound exists, to propagate unresolved
   comparisons. A reported complete-case summary must be explicitly secondary.
   The proposed positive criterion must refer to the whole planned grid.
2. **Queue order under the resource cap.** Freeze an interleaving of families,
   parameter cells, and methods, and a rule for initial attempts versus longer
   retries. Otherwise a fixed stop can systematically omit the expensive methods
   or settings. A failed numerical validation must not become a looser-tolerance
   success. Preserve both attempts and their costs as the draft proposes.
3. **Planner timing and cached work.** State what the forty seconds includes,
   how in-budget checkpoints and incumbents are chosen, and how reused targets or
   factorizations are charged. Keep training, post-design certification, and
   exhaustive evaluation time distinct. Freeze the corrected study's convention
   instead of introducing an unannounced new timing definition.
4. **Meaning of a positive result.** A numerical interval above zero certifies
   the sign on the realized finite mixture, within the floating-point witness
   methodology. It is not statistical significance or evidence of a practically
   meaningful margin by itself. Report magnitude and family heterogeneity even
   when both proposed mean signs are positive. Do not invent a practical-effect
   threshold after seeing the new outcomes.

The original failed sixteen-target broad-benefit screen must remain visible.
Fresh seeds under a newly chosen worst-target endpoint do not retrospectively
replicate that old claim. Similarly, fresh random models do not test source
fidelity for other rewards, unknown-model learning, model misspecification,
arbitrary horizons, eventual sufficiency, or all-optima assertions.

## 6. Which next investment I recommend

First use the completed data to expose the reward tradeoff in the main figure and
report the family summaries above. This requires no optimizer or new exhaustive
audits. It answers the immediate presentation problem more directly than another
large campaign. The descriptive empirical ending is already useful if its claim
is that different finite objectives select different reusable evidence, at
different reward and computational costs.

If the next question is **repeatability of that finite-grid pattern**, eight fresh
families with primary forty-second audits are a focused next main run. The draft
is a good basis after the clarifications above. Keep the ordinary and 5%-Brier
comparisons together. A new result that favors Brier is equally informative.
No native-superiority result is required to make this a successful investigation.

If instead the question is **whether native capability gains survive matching
posterior reward**, eight more families with the same 0–5% controls do not resolve
it. They repeat an unequal-sacrifice comparison more precisely. For that question,
I would prioritize one bounded reward-matched diagnostic on the existing twelve
classes before an expensive replication.

Here is an exact candidate diagnostic, not a request to launch it. For each class
let \(\pi_N\) be the already selected forty-second fixed-native policy, let
\(\mathcal T\) be the frozen training-target library, and let

\[
M(\rho)=\max_{T\in\mathcal T}\delta(K_{\rho,3},T).
\]

Select a policy by

\[
\min_\rho M(\rho)
\quad\text{subject to}\quad
R_B(\rho)\ge R_B(\pi_N).
\]

The threshold uses the native policy's world-posterior reward, not its held-out
four-step audit. The native policy itself is feasible. Therefore an **exact**
optimizer cannot have a worse training maximum than that policy; no analogous
inequality follows automatically for the held-out four-step maximum. Evaluating
the latter is the informative step. Numerical implementations need their usual
feasibility and optimization-gap checks, all twelve classes, and preserved failures.

This is a reward-matched hybrid selector, not the original Brier objective or a
proof that all Brier-near-optimal policies do well. Its threshold also depends on
obtaining the native policy. If presented as a new algorithm rather than a
retrospective diagnostic, the cost of obtaining that threshold must be charged;
it cannot be called an independent forty-second Brier procedure for free. Nor
does one returned point trace a full Pareto frontier.

My priority is thus: make the completed tradeoff legible now; use this small
diagnostic if matched reward is the unresolved scientific question; use the
eight-family draft if independent repeatability is the chosen next question.
Do not require both campaigns before the paper can present an honest descriptive
figure. Adding the source-qualified count arm or repairing the wider 22-class
coverage addresses objective breadth, a separate decision. Those are reasonable
alternatives if breadth is the reason for changing the ending, but are not
substitutes for either reward matching or independent replication.

## 7. Verification performed and reviewed snapshot

The first explanation was completed before this review and is unchanged. I
independently rechecked the twelve-setting candidate's nineteen source/output
hashes recorded in [FIGURE_CHECK.json](FIGURE_CHECK.json); all matched. Read-only
arithmetic reconstructed all 108 comparison groups in [ANALYSIS.json](ANALYSIS.json)
from its 540-row plotting table, including win/loss/unresolved counts, median
differences, and per-setting differences; no mismatch was found. I checked the
actual constraint code, the 144-pair grid, the reward comparisons above, and the
family means, and inspected all three PDF images described at the beginning.

This is a reporting and design review, not a rerun of the underlying millions of
decoder LPs, an independent new witness replay, or a formal proof. The original
packages' stronger and weaker verification boundaries remain as documented in
the first explanation and candidate captions. I did not independently rerun the
new 22-class plotting verifier in this commission.

SHA-256 bindings for the reviewed snapshot are below. The owner's README changed
during review to correct the constraint and add the figure-choice material; the
hash recorded here is that corrected version.

| File | SHA-256 |
|---|---|
| `README.md` | `a99304c988aef56a3d009c128975a7070ecb300c7cade3eab398e50daee989d1` |
| `CAPTION.md` | `532e64b85b1059ed156777d4241590b4774f36b906b6150f25358d50eedffe9e` |
| `CONFIRMATION_DRAFT.md` | `e767fa41ccbf55175f4217680d79ad23b8e6d1c3e28d2611238ed2f5d09e8ad5` |
| `FIGURE_CHOICE.md` | `ffacade4eb02cbfce5e70e7d7a0a883d13bd902372fffd0ade9aca3535b0ea5f` |
| `CANDIDATE_FIGURE.pdf` | `1b4a8211f0a0e7fd6c89a44053b543321bddf92d52a0e3dba83bef6e50c2829b` |
| `TRADEOFF_DIAGNOSTIC.pdf` | `d474db40538e69226f50c4809f89d3e6f82b3a4499799e499de30434ca28c4ed` |
| `CANDIDATE_22_CLASSES.pdf` | `783c50a4c508d7adb752b0fd131223986c5bcd49c8f18d35f6161177dbf1a62d` |
| `CAPTION_22.md` | `44b37ae7b1307cf09727bf32780274c93c37e673f255417dce3cfa0e9616be8e` |
| `make_candidate.py` | `6e59839271a731fdce802e7c613133ba3e75d165d528e06831f025b18ff52f9c` |
| `ANALYSIS.json` | `778ede4371965d1311cd178b5d0432585601e4ae5ef659d0c527881177b47bb4` |
| `figure_data.csv` | `bb633eb6900a390153349c08084c6991be8a6a8b16e120072777f81fa8d31cf5` |
| `MISSING_CITATIONS_EXPLANATION.md` | `91d0fbb21e97f178537acdd251ef0625025d9b0091ec783d0e82c14dfc82a38d` |
