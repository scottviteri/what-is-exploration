# Post-design fixed-prefix certificate refinement

This directory adds a separately labeled certificate refinement after the study
design. It preserves the primary report, all predeclared beta bounds, planning
budgets, weights, policies and held-out comparisons. It imports no optimizer or
planner and makes no comparison between methods.

**Full means the full countable target sum at collection time three.** It does
not mean eventual `J_w` under arbitrary continuations. The lower bound B is for
the same finite-stage policy optimization and current weights; it is not a lower
bound on the eventual optimum.

## Derivation

Write the fixed-prefix loss as retained loss plus omitted loss. For a candidate
experiment E, let U bound its retained loss, let B lower-bound the retained
optimum over all causal policies of collection length three, and let beta be the
omitted coefficient mass. The primary upper bounds are U + beta for loss and
U + beta - B for regret (the primary CSV uses max(0,U-B) + beta to handle tiny
numerical inversions).

Let G be a stochastic decoder from E to the identity experiment on the same
finite nonempty world class. Its worst-world total-variation error is R.
Every finite target F is a stochastic postprocessing of that identity experiment.
Composing G with F and applying TV contraction gives deficiency(E,F) <= R.
Consequently the secondary bounds are U + beta R and U + beta R - B.
This does not require full revelation to be physically attainable or use a prior.

The frozen background assigns every (depth n, denominator d) block total mass
2^(-n-1-d), for n >= 0 and d >= 1. Summing over d gives depth mass 2^(-n-1).
Depth zero has background mass 1/2 and identically zero loss. If c denotes the
original background mass of the 131 retained encodings, then

- c = 114970689090227 / 5484237660094464;
- beta = (1/20)(1-c) = 5369266971004237 / 109684753201889280;
- omitted depth-zero mass = 1/40;
- omitted depth-one-through-three mass =
  (1/20)(7/16-c) = 2284383287201101 / 109684753201889280;
- omitted depth-over-three mass = 1/320.

Let D3 be the maximum decoder upper over all 128 deterministic depth-three
training interventions. Every full-history randomized target of depth at most
three is a world-independent mixture of deterministic plans, followed where
needed by prefix projection. Mixture decoders and TV contraction therefore bound
its deficiency by D3. The 128 observation-tree representatives cover full-history
deterministic plans because their actions can be reconstructed recursively.
Put C3 = min(D3,R,1). The omitted loss is at most

    beta_short C3 + (1/320) R.

Add that expression to U, or to U-B, for the partition loss/regret upper.
This is a maximum-over-plans argument, not an average-over-policies assertion.
Geometric sums and coefficient arithmetic are exact Fractions; probability
products and decoder residuals remain floating point.

## Evidence and scope

The script covers all 108 planned fixed/tractability/hard primary checkpoint
rows. An unavailable primary row is retained with its reason. A failed replay
retains its row and causes an unsuccessful script exit. No row or method is
selected using the refined numbers.

Adaptive averages are excluded: this pass does not construct their separately
matched retained upper, lower and objective. Information gain, Brier, uniform,
minimax and reward-face controls receive no weighted regret claim.

For every eligible weighted checkpoint, the script:

1. Requires the final primary report and passing independent SUMMARY_CHECK, plus
   passing planning and held-out validation; verifies frozen hashes and the run
   manifest bindings of selected iteration, objective, policy and decoder files.
2. Reconstructs controlled probabilities directly from original T and Z and
   replays the actual policy; checks byte-identical E binding to the audit alias.
3. Reconstructs all 131 literal target kernels, replays every saved decoder and
   dual on original probabilities, and checks current exact weights and retained
   upper. The retained lower B is reused from the bound, independently audited
   planning record; this script does not reprove its LP dual/cut derivation.
4. Replays the identity witness against this same E. It never uses the depth-four
   audit upper as R. If the identity witness is absent, it uses the universal
   upper R=1. A present invalid identity witness is a failure, not a fallback.
5. Identifies the deterministic subset by target keys, never array position:
   the saved target order is permuted. It verifies exact mass partition and
   preserves the primary U, B, beta and gap-plus-beta values.

A tiny upward adjustment max(primary U, replayed rational-weighted numerical
decoder upper) is separately recorded for the secondary bounds. Secondary
regret values are clipped below at zero for numerical inversions within the
declared tolerance. This does not turn floating-point witnesses into exact or
outward-rounded certificates. Identity feasibility/replay uses 1e-12, training
decoder feasibility/gap 2e-7, and physical-policy replay 1e-10.

All additional replay/hash time is recorded separately. Identity witnesses were
computed during the earlier external audit; neither that audit nor this
refinement is backdated into the original planning budgets. Weights at different
adaptive checkpoints define different objectives; a refined regret upper for one
checkpoint is not a regret guarantee for a single fixed adaptive objective.

## Existing proofs and new application

Existing checked ingredients are:

- `decodeErr_stochasticRuleComp_le`, `Formal/Formal/MixtureDecoder.lean`;
- `finiteDeficiency_le_of_decoder` and
  `finiteDeficiency_decisionLaw_le`, `Formal/Formal/DualCertificate.lean`;
- `exists_decoder_to_causalPolicy_of_observation_plan_decoders`,
  `Formal/Formal/CausalUniversality.lean`, including mixture and prefix routes.

`Formal/PAPER_SUPPORT.json` records the relevant full finite-horizon universality
scope under `thm:finite-universality`. The weighted partition and numerical
packaging here are new written applications. No new Lean claim, rate, eventual
optimum, online-policy assembly or efficient full-objective theorem is asserted.

## Execution

Prepare/self-test only until the primary report finishes:

    /tmp/exploration-lp-cpu-venv/bin/python replay.py --self-test

Then, with one available CPU and a fresh output directory:

    /tmp/exploration-lp-cpu-venv/bin/python replay.py \
      --audits ../exhaustive_audits --summary ../summary \
      --output results --cpu CPU

Paths are relative to the caller's working directory; pass absolute paths when
calling outside this directory. The outputs are CERTIFICATES.json and a CSV with
every planned weighted checkpoint. They contain certificates and coverage only,
not wins/losses or cross-method comparative aggregation.

The independent primary checker defaults to `STUDY/SUMMARY_CHECK.json`, outside the generated summary directory. Use `--summary-check PATH` to supply another checked report.
