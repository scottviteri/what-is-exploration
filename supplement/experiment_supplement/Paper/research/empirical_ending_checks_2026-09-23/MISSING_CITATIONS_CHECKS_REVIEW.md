# Commission 03: review of the completed grid and additional support

24 September 2026. Written for the lead author and Introduction Edits. This review changes
only this note. It reads the completed reports, verification and plotting source,
the two exact Lean modules, and the current manuscript ending; it runs no
optimizer, decoder-audit campaign, training, Lean build, or Git mutation.

**I now recommend the completed 22-class study as the main empirical ending, with
the separate 12-setting study supporting the computation discussion.** Completing
the posterior controls removes the strongest reason I previously favored the
12-setting figure. The 22 classes also illustrate recognizable mechanisms and an
additional reward family. This recommendation follows completeness, scientific
scope, and reader clarity; it does not depend on obtaining a favorable native
win count. The main figure should retain the reward-sacrifice panel and every
adverse case.

There is one concrete release correction: the aggregate reward report currently
contains stale hashes for 19 subsequently replayed check reports. The policies
and audit-result bindings I checked are unchanged, and all 19 current checks pass.
This is a report-binding problem to repair before freezing the package, not a
reason to rerun the optimization. The reward-matched comparison is separately
pending at the final review check, 2026-09-24 00:12:37 UTC: the final comparison
report and its figure are absent. I assess its design below without inventing its outcomes.

## 1. The experiment, from its basic objects

A **world** is one possible environment law: it says how observations respond to
actions. A **hypothesis class** is the supplied finite list of such worlds. The
agent does not know which member is actual. A model may implement its law with a
hidden physical state, transition probabilities, and observation probabilities.
That hidden state is different from the world label: the state can change during
interaction; the actual world specifies the law governing those changes.

The planner receives all the candidate model arrays. This is supplied-model
planning with uncertainty about the actual member, rather than learning unknown
model arrays from a training dataset. Structured sensor, delayed, irreversible,
and random hidden-state classes are included. The random classes vary world
count and generator concentration; the 22 classes are a heterogeneous comparison
grid, not 22 independent samples from one declared application distribution.

A **policy** maps preceding actions and observations to an action distribution.
It has no access to the actual world label or hidden physical state. A length-three
**record** contains three actions and three observations. For policy \(\pi\), its
**experiment** \(E_\pi=K_{\pi,3}\) is the matrix whose row for world \(Q\) is the
probability distribution of that record in \(Q\). An experiment is thus a family
of possible record laws, not one trajectory.

A **target** is another permitted policy, run for a specified number of
interactions. A **decoder** is a randomized transformation of the collected record
into a simulated target record. It can depend on which target is requested and
on the known hypothesis class, but it must be the same transformation in every
world. It cannot be told which world produced the record. The directed deficiency
is

\[
\delta(E,F)=\inf_G\max_{Q\in\mathcal Q}
  \operatorname{TV}(E(Q)G,F(Q)).
\]

The source is on the left and the target on the right. Small deficiency means the
source record can approximately stand in for the target record. Zero means exact
simulation in this finite setting. The maximum over worlds is part of this
capability criterion; it is not an average under the posterior reward's prior.

The reported audit is

\[
A_{3,4}(\pi)=\max_{\sigma}\delta(K_{\pi,3},K_{\sigma,4}).
\]

Every target gets its own best world-independent decoder. Collection lasts three
interactions; targets last four. Computational planning time and audit time are
separate budgets, neither of which extends the collected record.

All 32,768 deterministic depth-four binary observation trees are enumerated.
For one deterministic tree, the observations determine the actions the target
would have taken, so its record can be encoded by its observation sequence.
Randomized finite policies are mixtures of deterministic policies; mixing their
decoders gives the corresponding coverage argument. Shorter targets can be
extended and then projected back to their prefixes. This is exhaustive coverage
of the declared finite target problem, not of every future interaction horizon.

## 2. What each method optimizes, and what evaluation adds

Use a uniform prior \(\mu\) on the candidate worlds. If \(P_\pi(Q\mid h)\) is the
world posterior after record \(h\), the two posterior rewards are

\[
R_I(\pi)=H(\mu)-\mathbb E_h H(P_\pi(\cdot\mid h)),
\qquad
R_B(\pi)=\mathbb E_h\sum_Q P_\pi(Q\mid h)^2-\sum_Q\mu(Q)^2.
\]

The implementation uses bits for information. Brier here measures improvement in
predicting the **world label**, not next-observation squared prediction loss,
physical-state prediction, or predictive surprisal. Exact finite-history dynamic
programming optimizes these posterior objectives on the supplied class. That is
an objective-level Bayesian comparison, not a claim about the training behavior
of a published learned exploration implementation.

The categorical pseudo-count arm uses the specified add-one categorical
observation-density specialization. Its finite return sums
\(1/\sqrt{1+N_{\mathrm{previous}}(o)}\), with the count taken before the current raw
observation label is added. Preserve this source qualification: it is not an
experiment on the full CTS Atari learner, state visitation, or every pseudo-count
construction. Uniform actions are an unoptimized policy control.

Let \(\mathcal T_3\) contain the 128 deterministic depth-three targets. The two
native planning objectives in this cohort are

\[
L_{128}(\pi)=\frac1{128}\sum_{T\in\mathcal T_3}\delta(E_\pi,T),
\qquad
M_3(\pi)=\max_{T\in\mathcal T_3}\delta(E_\pi,T).
\]

Weighted native minimizes the finite **mean**; minimax minimizes the finite
**maximum**. A favorable posterior control also minimizes \(M_3\), subject to

\[
R(\pi)\ge R^{\max}-r(R^{\max}-R^{\min})-10^{-10},
\qquad r\in\{0.01,0.05\}.
\]

This control is a constrained native planner with a posterior-reward floor. It
shows what a specifically selected nearly optimal posterior policy can achieve.
It does not show what an arbitrary approximate Brier learner will select, and
it is not ordinary Brier optimization alone.

All these policies are selected at collection/target depth three and then held
fixed for the depth-four evaluation. The evaluation therefore does not simply
repeat the native training loss. Nonetheless the native loss is deliberately
aligned with the paper's capability criterion; this is not a criterion-neutral
ranking of every possible use of evidence. The transfer tested is to a longer
native target on the same model class, not to new models or eventual exploration.

The eventual \(J_w\) is different again: it uses strictly positive weights on a
rich countable target family and eventual deficiencies as the record grows.
Neither \(L_{128}\) nor \(M_3\) is that objective. In particular, do not import the
other study's retained 131-encoding rich-background loss, fixed-prefix regret
certificates, timings, seed-family statistics, or 144 order comparisons here.
The same notation for an audit does not make the optimized objectives identical.

## 3. What is complete, with the correct denominators

The completed evidence now supports the following statements:

| Quantity | Coverage and meaning |
|---|---|
| Main absolute comparison | 132 of 132 method/class entries: six methods on each of 22 classes |
| Originally registered near-optimal controls | 88 of 88: information and Brier, each at 1% and 5%, on all 22 classes |
| Additional repaired audits | 18 missing controls plus the uniform audit: 19 complete audits, 622,592 target witness checks |
| Reward replay inventory | 427 distinct saved policy instances; several native representatives per class/method are included |
| Combined plotting summaries | 220 method/class envelopes: six main methods plus four constrained controls on each class |
| Same-time order diagnostic | 88 policy pairs, two directions each: 22 classes × two native methods × ordinary Brier/Brier5 |
| Normalized Brier-sacrifice summaries | 21 classes; the remaining class has constant Brier reward and stays in every capability comparison |

The 427 policies are not 427 independent experiments or the full optimizer set.
The 88 controls include some already present in the original representative
inventory; the inventories are combined as a union, not by blindly adding their
headline counts. “Complete controls” means the registered 1%/5% grid, not every
possible reward tolerance.

The new audits check saved stochastic decoders and bounded decision-loss witnesses
against every target, including policy/model replay and ordered target coverage.
The last uniform recovery reuses and checks 28,928 old witnesses, then completes
the missing targets; the old failed attempt remains a failure in the archive.
The initial missing-`highspy` launch is likewise preserved separately from the
successful retry. Four deliberately corrupted certificates were rejected. These
are useful checks of the numerical evidence pipeline, not proofs that the checker
can have no other defects.

The original representative envelopes still retain their original, narrower
verification boundary: complete profile arithmetic and saved master/hardest/
revelation witnesses, without all old per-target decoders. Completing missing
entries does not retroactively produce those missing witnesses for every old
policy. The new reward-matched pass specifically re-audits its one chosen original
reference per class, but that strengthens those selected references only.

## 4. The complete outcomes preserve a substantial Brier-positive story

For the following counts, a win means lower \(A_{3,4}\) for the native method.
The intervals include the saved representatives, and classifications use the
stated \(10^{-6}\) numerical separation rule.

| Comparator | Weighted native: wins / ties / losses / mixed | Minimax: wins / ties / losses / mixed |
|---|---:|---:|
| Ordinary world-posterior Brier | 18 / 2 / 2 / 0 | 19 / 1 / 2 / 0 |
| Favorable 5%-Brier control | 16 / 0 / 6 / 0 | 18 / 1 / 2 / 1 |

Against Brier5, the descriptive median audit reductions are approximately
0.006960 for weighted native and 0.010416 for minimax. Those are medians of
representative-envelope midpoint differences. They are neither an attained policy
in general nor a population estimate, and they should not replace the full rows.

Weighted native loses against Brier5 in `delayed_0.25_0.1`, both irreversible
classes, `hmm_91501_0.2`, the fresh four-world concentration-0.2 draw 2, and the
fresh eight-world concentration-0.2 draw 1. Minimax loses in that delayed case
and the latter eight-world case, ties in `irreversible_0.1_0.1`, and has a mixed
comparison in the fresh eight-world concentration-5 draw 1. In that mixed case,
the saved difference envelope runs from approximately −0.00029545 to +0.00009006.
Its width is not merely floating-point uncertainty; the sign depends on which
saved representative is used. Do not fold it into ties or count its midpoint
as a definite loss.

Reward sacrifice is normalized **within each class**:

\[
s_B(\pi)=\frac{R_B^{\max}-R_B(\pi)}{R_B^{\max}-R_B^{\min}}.
\]

It is a fraction of the reward range attainable by the same three-interaction
policy family. It is not a fraction of optimal reward, a Brier prediction-error
probability, or a percentage of all information available in the world. An
absolute \(10^{-10}\) reward allowance can also make the displayed normalized
5% concession exceed exactly 5% by a tiny amount; retain the literal constraint.

In `irreversible_0.1_0.1`, the computed maximum and minimum coincide at
0.22470136986301364. Normalized sacrifice is undefined there. The caption correctly
leaves its normalized point absent while retaining its capability row. A constant
reward does not imply all policies induce equivalent experiments: it means this
particular finite scalar cannot distinguish their reward values.

Across the other 21 classes, the medians of the saved sacrifice-envelope midpoints
are about 18.07% for weighted native and 23.65% for minimax. These are new
read-only summaries of the completed report, not the 21.17% number from the
separate twelve-setting study. They make the central caution concrete: native
methods can spend substantially more Brier reward than the 5% controls. A lower
capability audit is not necessarily a reward-matched improvement.

Moreover, the audit-envelope midpoint and sacrifice-envelope midpoint in two
panels need not describe the same returned policy. The caption should say this
explicitly. Conclusions involving two scores simultaneously require their
policy-level pairing, which the new matched diagnostic is designed to supply.

## 5. Scalar audit comparisons versus order of experiments

A record experiment dominates another at time three only if it can simulate
that whole experiment with zero deficiency. Two scalar scores do not establish
such a decoder. Conversely, two positive directed deficiencies establish that
neither experiment exactly replaces the other.

The new 22-class order diagnostic selects the lexically first verified
representative for each class/method, without choosing it by the directed-error
outcomes. Of its 88 pairs, 84 have positive numerical lower bounds in both
directions; four have upper bounds at numerical zero in both directions. The
latter pairs are:

- Weighted native versus ordinary Brier in `sensors_0.25_0.25`.
- Weighted native versus ordinary Brier in `irreversible_0.1_0.3`.
- Minimax versus ordinary Brier in `irreversible_0.1_0.1`.
- Minimax versus Brier5 in `irreversible_0.1_0.1`.

Call the first group **numerically incomparable** and the second **equivalent
within numerical tolerance**. These float64 calculations are not exact
outward-rounded interval theorems. They concern the selected policies' records
at time three, not all optimizers or their arbitrary later continuations.

This is new evidence about the 22-class policies. It must replace, rather than
borrow, any attempted use of the twelve-setting study's 144 comparisons to
explain these records. The result is also substantively different: here some
pairs are equivalent within tolerance. The direction labels are source-to-target,
so a positive native-to-Brier bound identifies Brier evidence that this native
record cannot reproduce, and the opposite bound identifies evidence missed by
Brier. A scalar audit win and this two-way obstruction can coexist.

## 6. Exactly what the Lean certificates add

The actual declarations in
[`EmpiricalEndingCertificates.lean`](../../../Formal/Formal/EmpiricalEndingCertificates.lean)
prove generic rational upper/lower certificates for the real finite deficiency.
`rational_lower_bound` requires finite world/signal types, nonempty worlds and
target signals, valid rational experiment rows, and a valid bounded decision-loss
witness. With rational weights \(\lambda_Q\ge0\), \(\sum_Q\lambda_Q=1\),
\(0\le\mu_{Qy}\le\lambda_Q\), and
\(b_x\le\sum_Q\mu_{Qy}E(Q,x)\) for every \(x,y\), its certificate is

\[
\sum_x b_x-\sum_{Q,y}\mu_{Qy}F(Q,y)\le\delta(E,F).
\]

The inequality holds for **every real stochastic decoder**, not just rational
ones, solver-returned decoders, or a searched list. The witness weights are part
of a worst-world lower-bound argument; they need not equal the uniform prior
used by the posterior reward. The upper theorem supplies an actual rational
stochastic decoder and verifies its half-\(\ell_1\) errors world by world. Together
these certify an interval for the infimum without trusting the LP optimizer.
The concrete application separately proves validity of both experiment tables.

[`EmpiricalEndingDelayed.lean`](../../../Formal/Formal/EmpiricalEndingDelayed.lean)
defines two explicit rational tables: four worlds with 36 retained native signals
and 16 retained Brier signals. Kernel-checked rational arithmetic proves

\[
0.0878\le\delta(E_N,E_B)\le0.0879,
\qquad
0.0276\le\delta(E_B,E_N)\le0.0277.
\]

`records_incomparable` follows from the two strictly positive lower bounds. This
is the four-world structured numerical case `delayed_0.25_0.1`, using native
reference `cell_0014` and Brier reference `cell_0208`. It is not the paper's separate
two-world, horizon-dependent, all-continuations delayed-test theorem.

There are three verification levels to preserve:

1. **Exact Lean theorem:** validity and directed-deficiency bounds for the literal
   rational tables and certificates in the module. Rational checks use
   `decide +kernel`. The recorded axiom audit lists only `propext`,
   `Classical.choice`, and `Quot.sound`.
2. **Exact-rational Python construction:** physical-model filtering generates
   those tables after policy rows are quantized to millionths and model rows are
   rationalized and normalized. This code and its data are inspectable, but Lean
   does not yet prove that this recursion gives those tables or formalize the
   removal of zero record columns in this causal instance.
3. **Numerical archive comparison:** the reconstructed native table differs from
   the archived experiment by reported row-TV at most about \(3.5196\times10^{-7}\);
   the Brier difference is below \(7\times10^{-18}\). These proximity calculations
   and input-file bindings are numerical/provenance evidence, not a Lean theorem
   transferring the exact bounds to the original floating-point policy.

This supplies useful exact support for the meaning of a two-way deficiency
certificate, including in a case adverse to native on the scalar audit. It does
not prove the 32,768-target audit, native objective optimality, the reward-matched
comparison, all 88 pairs, or eventual behavior. An exact rational perturbation of
an optimizer has not thereby been proved optimal.

The four formal-report source hashes match the current modules/data/axiom record.
The owner records successful isolated compilation and a full Lean build; I read
those reports and the declarations, without rerunning Lean in this review. The
modules remain absent from the shared support ledger and root imports. Their
classification failure is deliberately pending research integration, not a failed
proof. Before citing them as new manuscript formal support, integrate their
precise claim scope and revalidate the affected shared records. The older
`EXACT_DIAGNOSTIC.json` generation status still says `lean_pending`; read it with
`FORMAL_CHECK.json`, which records the subsequent successful checks.

## 7. Reward matching: the question is well posed, the result is pending

[MATCHED_PROTOCOL.md](MATCHED_PROTOCOL.md) fixes one original weighted-native
reference \(\pi_N\) per class by lexical cell order. It selects a new control by

\[
\min_\rho M_3(\rho)
\quad\text{subject to}\quad
R_B(\rho)\ge R_B(\pi_N)-10^{-10}.
\]

The reference is itself feasible. Therefore an exact constrained minimum cannot
have a worse **training maximum** than the reference. With a certified numerical
optimization gap, the corresponding statement needs that tolerance. This is not
a theorem about the depth-four audit: \(M_3\) and \(A_{3,4}\) ask about different
target horizons. That missing implication is exactly why the new audit is useful.

“Matched” means the control retains at least the reference's Brier reward, up to
the explicit slack. It may retain more reward; the rewards are not forced equal.
For the constant-range class, the normalized percentage is undefined and the
absolute reward floor remains the meaningful quantity. The protocol's nominal
zero-concession handling is appropriate there.

The comparison must use the specific reference selected in the manifest, not the
most favorable original native representative or an envelope midpoint. Both sides
receive fresh full-witness audits, so this diagnostic also removes the unequal
per-target witness-retention boundary **for these pairs**. The original broader
representative envelopes retain their own boundary.

This is primarily a comparison of a finite native mean with a reward-constrained
finite native maximum. A control win would not establish that ordinary Brier
optimization selects the better policy. A native win would show that this
particular constrained minimax selection failed to match its longer-target score
at the allowed reward floor; it would not prove that every equally rewarding
policy is worse or that the native reference lies on a full Pareto frontier.
The control does not optimize the held-out target depth, so it is not a certificate
of the best possible \(A_{3,4}\) at that reward.

Matching reward also does not match computation. The new planners have their
specified one-hour cap, separate depth-four audit budgets, and the cost of
obtaining the original reference whose reward sets the floor. These are not the
other study's forty-second policies. Report actual planning and evaluation costs,
and do not describe the hybrid control as a free ordinary Brier implementation.

At the final check, 2026-09-24 00:12:37 UTC, 22 of 22 matched-control
audits and 21 of 22 reference re-audits had complete target coverage and
passed check reports bound to their current result files. `MATCHED_COMPARISON.json`
and `REWARD_MATCHED_DIAGNOSTIC.pdf` were still absent. These partial counts establish
progress, not a completed comparison or its aggregate signs. I have not inferred
outcomes from partial directories. The required final boundary is a passed
22-case comparison report, its input/constraint/optimizer checks, and both
validated audits for every pair.

Even a fully completed result will remain a post-design diagnostic on existing
classes. The lexical selection rule protects against selecting a reference by
the new held-out outcomes; it does not turn previously inspected environments
into independent confirmation.

## 8. Recommendation and concrete corrections before integration

Replace the startup-only main ending with this completed 22-class comparison,
subject to repairing report bindings and preparing a legible final-size figure.
It optimizes full-history policies, uses several environment mechanisms and an
additional source-qualified reward, and evaluates capabilities not directly
optimized during selection. The startup study answers a narrower learning
question with fixed continuation. Preserve it as supporting evidence rather than
presenting the new model-based planning calculation as its training replacement.

The focused empirical claim should be: **on these declared finite classes,
objectives select different capabilities at a fixed collection length; posterior
reward concessions materially affect the comparison, and a smaller worst-target
error usually does not mean the whole record experiment is better.** This remains
useful when a baseline wins. It is not a native-superiority claim or evidence that
efficiently approximating eventual \(J_w\) is impossible.

The new three-panel figure addresses the main weakness identified in Commission
02: absolute errors, favorable Brier comparisons, and actual Brier sacrifices
are visible together for every class. The 22-class study now has its own order
and reward diagnostics. Keep the twelve-setting study for the distinct
compute-budget and rich-background questions; do not pool its results. Preserve
the earlier failed sixteen-target broad-benefit screen: this completion neither
withdraws its outcome nor replicates its different criterion.

The remaining concrete corrections are:

- **Refresh the aggregate check-file bindings.** My read-only integrity pass checked
  1,698 input/formal/directed-witness hashes. Nineteen mismatched: all repaired
  `control_audits/*/CHECK.json` and `uniform_audit/CHECK.json` hashes stored in
  `COMPLETE_REWARDS.json`. The later replay writes dated check files. Every current
  check says passed, covers 32,768 targets, and binds the unchanged complete
  `result.json`; those result hashes also match the aggregate. The other 1,679
  checked hashes matched. Refresh dependent aggregate/report hashes after the
  last replay, without changing assessments or repeating optimization. This was
  sent to the owner as an actionable correction.
- **Name the constrained comparator visibly.** “Minimax with a 5%-Brier reward
  allowance” makes its extra optimization clear even without reading the caption.
  Keep ordinary world-posterior Brier separate. Add the literal absolute
  \(10^{-10}\) allowance to the caption's reward constraint.
- **Explain envelope midpoints and pairing.** Midpoints need not be attained;
  separate reward and audit envelopes do not supply a jointly attained policy.
  Retain the mixed minimax comparison and the constant-reward row.
- **Use the actual reference-progress pointer.** The README names
  `REFERENCE_QUEUE.json`, which is absent at this snapshot. The current evidence
  is in the reference-chain reports and per-reference audit/check files. Supply
  a real aggregate completion pointer when the matched pass finishes.
- **Keep exact Lean and numerical evidence labels separate.** Classify the two
  research modules only in the authorized shared-integration window. Do not label
  the complete figure Lean-verified or silently identify rationalized policies
  with the archived optimizer outputs.
- **Inspect at manuscript display size.** The standalone 17-by-12-inch PDF is
  readable, and I found no clipped data: panel (b)'s extrema, about −0.0432 and
  +0.0925, are inside its plotted limits. Shrinking its 8.5–10-point labels to
  normal paper width would make them too small. Re-layout or re-render with fonts
  sized for the final width, retaining all 22 rows and adverse outcomes. This is
  a reader-clarity issue, not a request to solve the paper's page-limit problem.

There is no need to add expensive independent seeds merely to make this
retrospective figure publishable as a descriptive comparison. Finish and interpret
the already-running matched diagnostic first. Fresh seed families would then test
a precisely chosen repeatability claim; they would not prove all-optima,
source-fidelity, or eventual-order statements.

## 9. What this review checked

I read the required reports and the two modules, their certificate dependency,
the rational construction, policy/reward replay, repaired-witness checks,
comparison construction, and planned matched-analysis checks. I visually inspected
`CANDIDATE_22_COMPLETE.pdf`. Read-only report arithmetic reconstructed all 220
method/class envelopes, all sixteen comparison groups, the 88 order-pair
classifications, and the reward summaries above. No arithmetic mismatch was found.
The nineteen stale check-file bindings are the integrity exception detailed above.

I did not rerun the hundreds of thousands of witness checks, rebuild Lean, or
infer a new formal theorem from the numerical archive. Hash agreement verifies
which evidence was read; it is not a replacement for those original checks.
The matched outcome remains pending under the stated snapshot boundary.

The following SHA-256 values bind the reviewed inputs at note creation. This is
an active research directory; later completion or rebinding should be described
as a later evidence boundary rather than silently attributed to this review.

| File | SHA-256 |
|---|---|
| `COMMISSION_03.md` | `85f2318a0211b6f28c2a8b33bbc75a03c5781569081c7c16d3e7491c9a50136c` |
| `README.md` | `0ee058dc5bc3f62b80f0609cdee00c8dd8407c9239ed05f9bc75d8477acbc2f7` |
| `CAPTION.md` | `56e5d563c96e0de6d922b6e72e930b2d7773313d10d70a29bce3b77ae8292de9` |
| `COMPLETE_COMPARISON.json` | `3c56b24cd088d311997af00066ae4259b00c4c3296e5b79a448dcd7bde854d91` |
| `COMPLETE_REWARDS.json` | `aae4cfa308da8d52e3a878d869d81c3e9af165ae82ea7d5a67af42472c22af2b` |
| `EVIDENCE_CHECK.json` | `2bbf7157a8f56ed276ab3ad99bbbfbcc9b952874083238908abc8520ec655820` |
| `COMPLETE_ORDER.json` | `95193b48a5f8a3e880ea1e1e462b65c356e8f8f8c44233a79af260959c3ce045` |
| `FORMAL_SCOPE.md` | `fc4ac3f55a76dac42685714af1baffef8bf8db79c868de042cee2f04eb91a423` |
| `FORMAL_CHECK.json` | `455113c3eab71e6ff9a6a98444adda07505f03e72bb059ac66f306203d7a040d` |
| `MATCHED_PROTOCOL.md` | `1a9cdbcc0759eb0aa28e32763c1f49c4152f21e0d52aebd9338c22a82c4a9e94` |
| `CANDIDATE_22_COMPLETE.pdf` | `a0690bebb19495271e9798689fecb006c3e1122b6536c26519384cf0a3be525d` |
