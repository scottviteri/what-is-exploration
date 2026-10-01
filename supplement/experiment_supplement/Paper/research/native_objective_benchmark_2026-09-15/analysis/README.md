# Why the fixed native objective did not win broadly

15 September 2026. Exploratory follow-up to the [frozen benchmark](../README.md),
requested by the lead author. [Analysis questions](PLAN.md), [code](diagnose.py),
[numerical results and verification](results.json). The original protocol,
objective, results and screening rule are unchanged.

[Weight sensitivity and Blackwell-monotone target weights](weights/README.md)
adds a separate analysis of how the same saved records are ranked.

## Main conclusions

1. The primary evaluation is a particular uniform-prior posterior decision score,
   not the full native comparison. Its squared-loss counterpart is exactly a
   multiple of the Brier objective. This explains why Brier is a well-matched
   baseline, but does not prove that it maximizes the zero-one evaluation.
2. In all five cases where Brier's nominal-optimal worst mean exceeded native's,
   even the BEST native-selected policy has lower mean performance. The losses
   cannot be removed merely by choosing a favorable native optimizer.
3. The saved native/Brier optimum pairs are numerically incomparable in eight
   cases and equivalent in two. Higher mean accuracy therefore does not show
   that the native record is inferior for every subsequent purpose.
4. The asymmetric sensor case gives a direct explanation: native protects the
   weaker sensor's experiment, while Brier gains more accuracy on the stronger
   bit and sacrifices some weaker-bit accuracy.
5. Equal percentage regret specifies different policy sets. Cross-evaluating
   their actual returns reveals different directions of permissible loss; it is
   not generally one larger set containing the other.

![Two mechanisms behind the results](capability_tradeoffs.png)

[Figure PDF](capability_tradeoffs.pdf); [plot source](plot.py). Left: saved
nominal-optimal worst-mean policies, rounded values. Right: the analytic
symmetric irreversible-choice calculation.

## The experiment in concrete terms

All ten cases have four fixed possible worlds, binary actions and observations,
three acquisition steps, and a full retained action-observation record. Unlike
the main paper's sensor study, this benchmark has no WAIT action. A world is
the fixed behavior indexed 00, 01, 10 or 11. In the three random hidden-state
cases these are model labels, not literal bits read by separate sensors.

| Family | Cases | What an action does |
|---|---:|---|
| Repeatable sensors | 3 | L reads U, R reads V; independent noise conditional on the fixed world. |
| Delayed access | 2 | The first consecutive L gives a fair coin. Later consecutive L reads U. R reads V and resets L access. |
| Irreversible choice | 2 | The initial action locks which bit can be read. Every later action measures that same bit. |
| Recurring hidden-state dynamics | 3 | Actions change a three-state hidden process and its emissions; the fixed world chooses its transition/emission matrices. |

Every adaptive randomized policy is feasible. There are 128 distinct pure
observation-contingency trees, but continuously many randomized policies. Full
history action weights and decoder allocations represent that entire family.

The candidate is a finite weighted native loss on 16 targets: L and R at .1
each; four length-two words and eight length-three words at .05 each; a tagged
fair L/R choice and a tagged fair LLL/RRR choice at .05 each. Total retained
weight is .9. This is one untuned choice of target list and weights, not the
complete J_w or a canonically justified finite approximation. A rich eventual
objective's strictness/completion results do not supply a finite average-task
advantage for these particular weights.

For each reward and allowed regret, the primary evaluation computes the mean
best accuracy on seven questions, then minimizes that mean across the whole
selected policy family. The questions are U, V, U xor V and the four indicators
that the world equals a specified one of 00,01,10,11. All use uniform evaluation
prior. The 60 objective optima and 720 decision endpoints include three regret
levels and four evaluation objectives: that joint mean and the three separate
balanced-label guarantees. The main result uses neither average performance of
random training seeds nor a worst-world guessing probability.

## Why the evaluation is especially close to Brier

Let p=(p_1,p_2,p_3,p_4) be the posterior after a record. For a binary question
with yes-world subset S, optimal guessing accuracy is max(p(S),1-p(S)). Define

    g(p) = (1/7) sum_S max(p(S), 1-p(S)),

where the seven S are the nontrivial subsets modulo complements. The benchmark
scores E[g(p)]. It thus averages a particular finite set of decision uses. It
does not quantify over all priors, payoff tables, or native target experiments.

The category-summed binary quadratic potential for that question is
p(S)^2+(1-p(S))^2. An exact algebraic identity is

    (1/7) sum_S [p(S)^2+(1-p(S))^2]
      = (3+4 sum_i p_i^2)/7.

To prove it, the sum over the seven complement pairs equals the sum of p(S)^2
over all fourteen nonempty proper subsets. Across all sixteen subsets, each
p_i^2 appears eight times and each cross term 2p_i p_j appears four times.
Thus the total is 4+4 sum_i p_i^2; removing the full subset subtracts one.

Consequently, the average Brier GAIN on these seven binary questions is exactly
4/7 of the four-world Brier gain used as a baseline. The evaluated loss is
zero-one rather than quadratic, so the objectives are closely related but not
identical. No theorem that Brier wins these accuracy comparisons follows.

Indeed, uniformly permute the posterior vector (3/5,2/5,0,0), or uniformly
permute (2/3,1/9,1/9,1/9). Both constructions have mean posterior uniform and
define finite experiments under that prior: give permutation signal s likelihood
4 p_s(i)/24 in world i. Their squared norms are respectively 13/25 and 13/27,
so Brier prefers the first; their mean guessing accuracies are 27/35 and 17/21,
so the seven-task score prefers the second. These are generic experiment
examples, not new policies in the registered binary-action benchmark.

For additional intuition, write a=max_i p_i and d=min_i p_i. The singleton
questions contribute 3 when a<=1/2, and 2+2a otherwise. Sorting the coordinates
shows the three balanced questions contribute max(1+2a,2-2d). In particular,

    a >= 1/2  implies  g(p) = (3+4a)/7.

On such posteriors the mean is an affine function of the probability of the
most likely world. These identities were also checked exactly on 455 rational
posterior vectors; the algebra above, not the finite checks, is their proof.

## A loss explained by an actual capability tradeoff

For repeatable sensors with errors (.1,.3), take the saved records that attain
the nominal-optimal worst mean. The rounded values are:

| Subsequent use | Native weighted | Brier |
|---|---:|---:|
| Guess U | .9000 | .9720 |
| Guess V | .7000 | .6640 |
| Guess parity | .6600 | .6600 |
| Mean of seven questions | .795343 | .801429 |
| Simulate one R reading: deficiency | 0 | .036 |
| Simulate RRR: deficiency | .084 | .120 |
| Simulate LLL: deficiency | .072 | .007902 |

Brier's saved nominal-optimal policy is especially interpretable: read L twice;
if the readings agree, use the last step for R; otherwise use it for L. The L
readings disagree with probability .18. Then R is never read, and V must be
guessed at chance. Its V accuracy is therefore .82*.7+.18*.5=.664. U accuracy
is .972. Native's record preserves both individual sensor experiments to numerical
tolerance, and trades some U accuracy for V accuracy and repeat-R capability.

Thus the native objective is doing something visible that the primary average
does not reward enough to make it win. It is not evidence that Brier can replace
every native use of the selected record. Different optimal policies may realize
the same reported values in different ways; these are concrete saved witnesses.

## Why native beats information in the delayed example

At errors (.25,.1), L needs two consecutive actions before producing an actual
U measurement. Compare two simple schedules:

| Schedule | Evidence | Information gain (bits) | Brier gain | Native loss | Mean accuracy |
|---|---|---:|---:|---:|---:|
| RRR | Three good V readings; no U information | .862418 | .224701 | .056250 | .710286 |
| LLR or RLL | One U reading and one V reading, plus a fair coin | .719726 | .262500 | .026531 | .814286 |

The information optimum is RRR. The broader record contains less total Shannon
information but supports more of these guessing decisions. Brier and native
select the broader record and tie on its mean. A delayed acquisition cost and
different posterior potentials explain this example without a rare-world prior.

## Why average performance misses an irreversible protection

With equal .1 error, committing to either sensor supplies three readings of its
bit. Its optimal bit-guessing accuracy is .972. Let alpha be the probability
of committing to U. The recorded choice is retained. Then

    U accuracy = .5 + .472 alpha,
    V accuracy = .5 + .472 (1-alpha).

Information and Brier gains are independent of alpha by symmetry. Their exact
optimizer sets include alpha=0 and alpha=1; hence the separate worst guarantees
for U and V are both .5. Those minima need not occur at the same policy.

The registered native objective selects alpha=.5 (the full native LP verifies
the resulting guarantees), giving .736 for each bit. Nevertheless g is invariant
under swapping the bit labels and the branch label is recorded, so the mean
seven-task value is constant at .710286 for every alpha. The average criterion
is literally indifferent to this capability allocation. This is a precise
limitation of that evaluation, not a universal win for balanced acquisition.

## Are the native losses just unfavorable ties?

No, for the five nominal-zero-regret losses in the registered primary metric.
The follow-up maximizes the SAME seven-task mean over every policy satisfying
the saved native cost cutoff, using exact linear full-history value coefficients.

| Case | Worst native | Best native | Worst Brier |
|---|---:|---:|---:|
| Sensors (.1,.3) | .795343 | .795343 | .801429 |
| Irreversible (.1,.3) | .706189 | .706189 | .710286 |
| HMM 91501, concentration .2 | .862006 | .862009 | .874638 |
| HMM 91502, concentration 1 | .686892 | .686894 | .690793 |
| HMM 91503, concentration 5 | .688606 | .688614 | .693164 |

These are numerical statements on the original optimum-plus-1e-8 sets, not
new exact-face theorems. Each gap to Brier is much larger than either the native
best/worst spread or the numerical residual. Favorable tie selection alone does
not repair this candidate's primary-score losses.

## What the regret percentages mean

At symmetric sensor error .1, the native 1%-regret worst-mean record has about
2.707% Brier regret. Conversely, the Brier 1%-regret worst-mean record has about
5.994% native regret. Both are measured using their respective full feasible
ranges. The selected sets therefore differ in WHICH sacrifices they allow;
neither simple witness supports treating one set as a superset of the other.
Global range normalization removes a choice of affine units. It does not make
the local sensitivity of different rewards to losing a capability identical.
The native losses already present at nominal zero regret also show that
normalization is not the entire explanation.

## What remains a hypothesis

The analysis verifies concrete target tradeoffs, absence of a tie-only repair,
and the relationship between the evaluation and Brier. It does not identify a
unique cause of every hidden-state result, prove that a richer library improves
these scores, or establish a better choice of native weights. The 16-target list
contains fixed action words and two tagged mixtures, leaving general adaptive
targets unscored. It also includes different words that can be informationally
equivalent in some interfaces. Counting those words with fixed weights is a
substantive preference, not a theorem-derived distribution over future uses.

A useful next comparison should preserve the existing primary results and test
both average decision value and uniform protection of individual attainable
capabilities on fresh cases. Any new target/weight rule needs an independent
reason and a held-out confirmation; repeatedly tuning this grid until native
wins would not establish the requested stronger claim.

## Verification

Thirty new best-mean LPs cover all ten native selected sets at the three saved
regret levels. Each has a saved primal/dual certificate and policy. New policies
are scored with independently assembled fixed-source decoder LPs; literal world
laws and LP feasibility/duality are checked. The follow-up reports 2,184 numerical
checks with maximum residual below 1.49e-9, plus 455 exact rational score-identity
checks. These are numerical certificates and written algebra, not new Lean
claims. Reproduce with `python3 diagnose.py` from this directory.
