import Formal.CoverageBound
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi

/-!
# Off-policy episodic coverage: the tilt, Bernoulli thinning, and importance resampling

**Paper context** (Proposition `prop:episodic`(d) and Appendix `app:episodic`;
`TheoryDocs/gamma_surrogates.tex`, Lemma `lem:identity`, Proposition
`prop:tilt`, Theorems `thm:snis` and `thm:thin`).  In the episodic interface the
analyst sees `N` i.i.d. episodes collected by a *behavior policy* `π`, and wants
to reproduce the observation law `T = T^σ(Q)` of a fixed depth-`n` native test
`σ`.  `CoverageBound.lean` treats the case where every `σ`-consistent episode is
consistent with the same probability regardless of its observations (uniform
`π`).  For a general `π` the per-episode splicing identity (`lem:splice`) says
that one episode is `σ`-consistent *and* has observation string `o` with
probability `w(o) · T(o)`, where `w(o) ∈ (0, 1]` is the product of `π`'s
probabilities of the actions `σ` prescribes along `o`.  Hence the conditional
law of the observations given consistency is `w · T / Σ w T` — `T` *tilted* by
`w` — and the plain rejection decoder of `CoverageBound.lean` converges to the
tilted law, not to `T`.  Two repairs are stated in the paper:

* **Bernoulli thinning** (nonasymptotic).  Given a floor `ε` with
  `ε ≤ w(o)` for all `o`, accept a consistent episode with outcome `o` with
  probability `ε / w(o)`.  Then `P(accepted, o) = w(o) T(o) · ε / w(o) = ε T(o)`:
  acceptance has probability exactly `ε` in every world, and the accepted
  outcome has law exactly `T`, so the rejection decoder run on the thinned
  summaries is within total variation `(1 − ε)^N` of `T`.
* **Importance resampling** (asymptotic).  With the weights `w` recorded,
  among the consistent episodes select one with probability proportional to
  `1 / w(o)`.  The output law given the transcript is the self-normalized
  estimator `P̂_N(o) = (N_o / w(o)) / Σ_{o'} (N_{o'} / w(o'))`, where `N_o` counts
  consistent episodes with outcome `o`. The strong-law argument below proves
  its convergence to `T` as `N → ∞`.

**The abstract model** (finite alphabet `O` for outcomes; the world `Q`, the
policy `π`, and the test `σ` enter only through `T` and `w`, exactly as they
enter `CoverageBound.lean` only through `p` and `T`).  One episode under the
behavior policy is summarized by `(consistent?, outcome) : Bool × O` with law
`tiltedLaw w T R`: `P(true, o) = w o * T o` and `P(false, o) = (1 − p) * R o`,
where `p = consProb w T = Σ_o w o * T o` is the consistency probability and `R`
is the (irrelevant) outcome law on inconsistent episodes.

**What is formalized here** (everything below is proved; no axioms beyond
Mathlib's):

* `tiltedLaw_eq_epLaw` and `tvDist_plainOutputLaw_tiltedOutcome_le`: the
  behavior-policy summary law is `CoverageBound.epLaw` with match probability
  `consProb w T` and outcome law `tiltedOutcome w T = w · T / p`, so the plain
  rejection decoder is within `(1 − p)^N` of the *tilted* law (the upper half
  of `prop:tilt`).
* `thinnedLaw`, defined as the pushforward of the joint law of (summary, coin)
  under "accepted iff consistent and the coin accepted"; `thinnedLaw_true`
  (`= ε * T o`), `thinnedLaw_false`, and `sum_thinnedLaw_true` (acceptance
  probability is exactly `ε`).
* `thinnedLaw_eq_epLaw`: the thinned summary law is `epLaw ε T R'` for the
  explicit rejected-outcome law `R' = thinnedRest ε w T R`, which is a
  probability vector (`isDist_thinnedRest`).
* `tvDist_thinnedOutputLaw_le` and `tendsto_tvDist_thinnedOutputLaw`: the
  thinned rejection decoder is within `(1 − ε)^N` of `T`, and its error tends
  to `0` — obtained by instantiating `CoverageBound.tvDist_outputLaw_le`.
  The paper writes the floor as `ε^n` for a per-action floor `ε` over `n`
  steps; the `ε` of this module is that product.
* `expect_iwEmpirical`: the unnormalized importance-weighted empirical measure
  `(1/N) Σ_k 1{consistent_k, o_k = o} / w(o)` has expectation exactly `T o`
  under the i.i.d. transcript law (`N ≥ 1`).
* `ae_tendsto_snisLaw` and `ae_tendsto_tvDist_snisLaw`: for any probability
  space carrying a sequence of episode summaries that is pairwise independent,
  identically distributed, and has the consistent-part law `w o * T o`
  (`IIDEpisodes`), the self-normalized estimator `snisLaw` converges almost
  surely to `T` coordinatewise and in total variation, by Etemadi's strong law
  (`ProbabilityTheory.strong_law_ae_real`) applied to the numerators.
* `tendsto_snisOutputLaw` and `tendsto_tvDist_snisOutputLaw`: the decoder's
  output law — the expectation of `snisLaw` over transcripts — converges to `T`
  (bounded convergence).
* `episodeMeasure` and `iidEpisodes_episodeMeasure`: the hypotheses are
  satisfiable — the coordinate process on `ℕ → Bool × O` under Mathlib's
  infinite product `Measure.infinitePi` of `tiltedMeasure w T R` is such a
  sequence — and `ae_tendsto_tvDist_snisLaw_episodeMeasure`,
  `tendsto_tvDist_snisOutputLaw_episodeMeasure` specialize the limits to it.

**Formalization boundary:** this module is the abstract iid-summary core.
`CausalSplicing.lean` and `CausalEpisodicCoverage.lean` prove the actual causal
splicing identity and tilted finite-product summary law.
`CausalImportanceResampling.lean` constructs the genuine finite resampling
rule, identifies its finite-law expectation with this infinite iid expectation,
and composes the actual causal prefix/summary decoder for every longer episode
horizon. The canonical proposition's worldwise limit is therefore checked.
This module's limit uses positivity throughout the target tree.  The weaker
target-support-only formulation and the sharp concentrability-sensitive
finite-sample bound from the theory note's `thm:snis` are proved in the
downstream `ImportanceSupportPositivity.lean` and
`CausalImportanceResamplingSharpRate.lean` modules.
-/

set_option linter.unusedSectionVars false

namespace IdExp
namespace ImportanceResampling

open Finset Filter CoverageBound
open scoped Topology

variable {O : Type*} [Fintype O] [DecidableEq O]

/-! ## The tilted per-episode law -/

/-- The behavior policy's probability that one episode is `σ`-consistent:
`p = Σ_o w(o) T(o)` (the splicing identity summed over outcomes). -/
def consProb (w T : O → ℝ) : ℝ := ∑ o, w o * T o

/-- Per-episode summary law under the behavior policy, on `(consistent?, outcome)`:
a consistent episode with outcome `o` has probability `w o * T o` (the splicing
identity), and an inconsistent one has outcome law `R` (never used by any
decoder). -/
def tiltedLaw (w T R : O → ℝ) : Bool × O → ℝ :=
  fun a => if a.1 then w a.2 * T a.2 else (1 - consProb w T) * R a.2

@[simp] theorem tiltedLaw_true (w T R : O → ℝ) (o : O) :
    tiltedLaw w T R (true, o) = w o * T o := rfl

@[simp] theorem tiltedLaw_false (w T R : O → ℝ) (o : O) :
    tiltedLaw w T R (false, o) = (1 - consProb w T) * R o := rfl

theorem consProb_nonneg {w T : O → ℝ} (hw : ∀ o, 0 ≤ w o) (hT : ∀ o, 0 ≤ T o) :
    0 ≤ consProb w T :=
  Finset.sum_nonneg fun o _ => mul_nonneg (hw o) (hT o)

theorem consProb_le_one {w T : O → ℝ} (hw1 : ∀ o, w o ≤ 1) (hT : IsDist T) :
    consProb w T ≤ 1 := by
  unfold consProb
  calc ∑ o, w o * T o ≤ ∑ o, T o :=
        Finset.sum_le_sum fun o _ => by nlinarith [hT.1 o, hw1 o]
    _ = 1 := hT.2

/-- The tilted summary law normalizes (for any `T`: the inconsistent mass is
`1 − p` by construction). -/
theorem sum_tiltedLaw {w T R : O → ℝ} (hR : ∑ o, R o = 1) :
    ∑ a : Bool × O, tiltedLaw w T R a = 1 := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [tiltedLaw_true, tiltedLaw_false]
  rw [← Finset.mul_sum, hR]
  unfold consProb
  ring

theorem tiltedLaw_nonneg {w T R : O → ℝ} (hw : ∀ o, 0 ≤ w o) (hw1 : ∀ o, w o ≤ 1)
    (hT : IsDist T) (hR : IsDist R) (a : Bool × O) : 0 ≤ tiltedLaw w T R a := by
  rcases a with ⟨b, o⟩
  cases b
  · exact mul_nonneg (sub_nonneg.2 (consProb_le_one hw1 hT)) (hR.1 o)
  · exact mul_nonneg (hw o) (hT.1 o)

/-- A probability vector lives on a nonempty alphabet. -/
theorem nonempty_of_isDist {T : O → ℝ} (hT : IsDist T) : Nonempty O := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := hT.2
  simp at this

/-- The tilted outcome law `w · T / p`: the conditional law of the outcome given
consistency. -/
noncomputable def tiltedOutcome (w T : O → ℝ) : O → ℝ :=
  fun o => w o * T o / consProb w T

theorem isDist_tiltedOutcome {w T : O → ℝ} (hw : ∀ o, 0 ≤ w o) (hT : IsDist T)
    (hp : 0 < consProb w T) : IsDist (tiltedOutcome w T) := by
  constructor
  · intro o
    exact div_nonneg (mul_nonneg (hw o) (hT.1 o)) hp.le
  · unfold tiltedOutcome
    rw [← Finset.sum_div]
    exact div_self hp.ne'

/-- **The tilt.**  The behavior-policy summary law is `CoverageBound.epLaw` with
match probability `consProb w T` and outcome law `tiltedOutcome w T`, not `T`. -/
theorem tiltedLaw_eq_epLaw {w T R : O → ℝ} (hp : consProb w T ≠ 0) :
    tiltedLaw w T R = epLaw (consProb w T) (tiltedOutcome w T) R := by
  funext a
  rcases a with ⟨b, o⟩
  cases b
  · rfl
  · simp only [tiltedLaw_true, epLaw_true, tiltedOutcome]
    field_simp

/-- Transcript law of `N` i.i.d. behavior-policy episodes. -/
def tiltedTranscriptLaw (w T R : O → ℝ) (N : ℕ) (x : Fin N → Bool × O) : ℝ :=
  ∏ i, tiltedLaw w T R (x i)

/-- The plain rejection decoder (first consistent episode's outcome, else `o0`)
run on behavior-policy episodes. -/
def plainOutputLaw (w T R : O → ℝ) (o0 : O) (N : ℕ) (o : O) : ℝ :=
  ∑ x : Fin N → Bool × O,
    tiltedTranscriptLaw w T R N x * (if firstMatch o0 N x = o then 1 else 0)

theorem plainOutputLaw_eq {w T R : O → ℝ} (hp : consProb w T ≠ 0) (o0 : O) (N : ℕ) :
    plainOutputLaw w T R o0 N = outputLaw (consProb w T) (tiltedOutcome w T) R o0 N := by
  funext o
  unfold plainOutputLaw tiltedTranscriptLaw outputLaw transcriptLaw
  rw [tiltedLaw_eq_epLaw hp]

/-- **The plain rejection decoder stalls at the tilt** (upper half of
`prop:tilt`): under a general behavior policy its output law is within
`(1 − p)^N` of the *tilted* outcome law `w · T / p`. -/
theorem tvDist_plainOutputLaw_tiltedOutcome_le {w T R : O → ℝ} (hw : ∀ o, 0 ≤ w o)
    (hw1 : ∀ o, w o ≤ 1) (hT : IsDist T) (hR : IsDist R) (hp : 0 < consProb w T)
    (o0 : O) (N : ℕ) :
    tvDist (plainOutputLaw w T R o0 N) (tiltedOutcome w T) ≤ (1 - consProb w T) ^ N := by
  rw [plainOutputLaw_eq hp.ne']
  exact tvDist_outputLaw_le (consProb w T) (isDist_tiltedOutcome hw hT hp) hR
    (consProb_le_one hw1 hT) o0 N

/-! ## Bernoulli thinning -/

/-- Probability that the thinning coin accepts the summary `a`: `ε / w(o)` on a
consistent episode with outcome `o`, and `0` on an inconsistent episode. -/
noncomputable def acceptProb (ε : ℝ) (w : O → ℝ) (a : Bool × O) : ℝ :=
  if a.1 then ε / w a.2 else 0

/-- Joint law of (episode summary, coin): the coin is drawn given the summary
with acceptance probability `acceptProb`. -/
noncomputable def coinLaw (ε : ℝ) (w T R : O → ℝ) : (Bool × O) × Bool → ℝ :=
  fun z => tiltedLaw w T R z.1 *
    (if z.2 then acceptProb ε w z.1 else 1 - acceptProb ε w z.1)

/-- The thinned summary: accepted iff consistent and the coin accepted; the
outcome is unchanged. -/
def thin (z : (Bool × O) × Bool) : Bool × O := (z.1.1 && z.2, z.1.2)

/-- Law of the thinned summary `(accepted?, outcome)`: the pushforward of
`coinLaw` under `thin`. -/
noncomputable def thinnedLaw (ε : ℝ) (w T R : O → ℝ) : Bool × O → ℝ :=
  fun b => ∑ z : (Bool × O) × Bool, coinLaw ε w T R z * (if thin z = b then 1 else 0)

/-- **Thinning cancels the tilt.**  An accepted episode with outcome `o` has
probability `w o * T o * (ε / w o) = ε * T o`. -/
theorem thinnedLaw_true {ε : ℝ} {w T R : O → ℝ} (hw : ∀ o, w o ≠ 0) (o : O) :
    thinnedLaw ε w T R (true, o) = ε * T o := by
  unfold thinnedLaw
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, thin, coinLaw, acceptProb, Bool.true_and, Bool.false_and,
    Prod.mk.injEq, Bool.false_eq_true, false_and, true_and, if_false,
    mul_zero, Finset.sum_const_zero, add_zero, if_true]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    tiltedLaw_true]
  have := hw o
  field_simp

theorem thinnedLaw_false {ε : ℝ} {w T R : O → ℝ} (hw : ∀ o, w o ≠ 0) (o : O) :
    thinnedLaw ε w T R (false, o) = (w o - ε) * T o + (1 - consProb w T) * R o := by
  unfold thinnedLaw
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, thin, coinLaw, acceptProb, Bool.true_and, Bool.false_and,
    Prod.mk.injEq, Bool.true_eq_false, Bool.false_eq_true, false_and, true_and, if_false,
    mul_zero, zero_add, if_true, sub_zero, mul_one]
  simp only [ite_self, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, tiltedLaw_true, tiltedLaw_false, zero_add]
  have := hw o
  field_simp

/-- Acceptance has probability exactly `ε`, independent of the world. -/
theorem sum_thinnedLaw_true {ε : ℝ} {w T R : O → ℝ} (hw : ∀ o, w o ≠ 0)
    (hT : ∑ o, T o = 1) : ∑ o, thinnedLaw ε w T R (true, o) = ε := by
  simp_rw [thinnedLaw_true hw]
  rw [← Finset.mul_sum, hT, mul_one]

/-- The rejected-outcome law of the thinned summary (never used by the decoder):
`((w − ε) T + (1 − p) R) / (1 − ε)`, with the degenerate floor `ε = 1` (which
forces `w ≡ 1`, so nothing is ever rejected) sent to `R`. -/
noncomputable def thinnedRest (ε : ℝ) (w T R : O → ℝ) : O → ℝ :=
  fun o => if ε = 1 then R o else ((w o - ε) * T o + (1 - consProb w T) * R o) / (1 - ε)

theorem isDist_thinnedRest {ε : ℝ} {w T R : O → ℝ} (hεw : ∀ o, ε ≤ w o)
    (hw1 : ∀ o, w o ≤ 1) (hT : IsDist T) (hR : IsDist R) :
    IsDist (thinnedRest ε w T R) := by
  by_cases h1 : ε = 1
  · have : thinnedRest ε w T R = R := funext fun o => by simp [thinnedRest, h1]
    rw [this]; exact hR
  · obtain ⟨o₁⟩ := nonempty_of_isDist hT
    have hlt : ε < 1 := lt_of_le_of_ne ((hεw o₁).trans (hw1 o₁)) h1
    have h1ε : (0 : ℝ) < 1 - ε := sub_pos.2 hlt
    have hp : consProb w T ≤ 1 := consProb_le_one hw1 hT
    constructor
    · intro o
      simp only [thinnedRest, if_neg h1]
      refine div_nonneg (add_nonneg ?_ ?_) h1ε.le
      · exact mul_nonneg (sub_nonneg.2 (hεw o)) (hT.1 o)
      · exact mul_nonneg (sub_nonneg.2 hp) (hR.1 o)
    · simp only [thinnedRest, if_neg h1]
      rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, hR.2, mul_one]
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hT.2, mul_one]
      unfold consProb
      field_simp
      ring

/-- **The thinned summary is CoverageBound's `epLaw`** with match probability
`ε` and match-outcome law exactly `T`. -/
theorem thinnedLaw_eq_epLaw {ε : ℝ} {w T R : O → ℝ} (hε : 0 < ε) (hεw : ∀ o, ε ≤ w o)
    (hw1 : ∀ o, w o ≤ 1) (hT : IsDist T) :
    thinnedLaw ε w T R = epLaw ε T (thinnedRest ε w T R) := by
  have hw : ∀ o, w o ≠ 0 := fun o => (lt_of_lt_of_le hε (hεw o)).ne'
  funext a
  rcases a with ⟨b, o⟩
  cases b
  · rw [thinnedLaw_false hw, epLaw_false]
    by_cases h1 : ε = 1
    · have hall : ∀ o, w o = 1 := fun o => le_antisymm (hw1 o) (h1 ▸ hεw o)
      have hp : consProb w T = 1 := by simp [consProb, hall, hT.2]
      simp [thinnedRest, h1, hall, hp]
    · simp only [thinnedRest, if_neg h1]
      have : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
      field_simp
  · rw [thinnedLaw_true hw, epLaw_true]

/-- Transcript law of `N` i.i.d. thinned episodes. -/
noncomputable def thinnedTranscriptLaw (ε : ℝ) (w T R : O → ℝ) (N : ℕ)
    (x : Fin N → Bool × O) : ℝ :=
  ∏ i, thinnedLaw ε w T R (x i)

/-- The thinned rejection decoder's output law: the outcome of the first
*accepted* episode, else the fallback `o0`. -/
noncomputable def thinnedOutputLaw (ε : ℝ) (w T R : O → ℝ) (o0 : O) (N : ℕ) (o : O) : ℝ :=
  ∑ x : Fin N → Bool × O,
    thinnedTranscriptLaw ε w T R N x * (if firstMatch o0 N x = o then 1 else 0)

theorem thinnedOutputLaw_eq {ε : ℝ} {w T R : O → ℝ} (hε : 0 < ε) (hεw : ∀ o, ε ≤ w o)
    (hw1 : ∀ o, w o ≤ 1) (hT : IsDist T) (o0 : O) (N : ℕ) :
    thinnedOutputLaw ε w T R o0 N = outputLaw ε T (thinnedRest ε w T R) o0 N := by
  funext o
  unfold thinnedOutputLaw thinnedTranscriptLaw outputLaw transcriptLaw
  rw [thinnedLaw_eq_epLaw hε hεw hw1 hT]

/-- **The thinning certificate.**  With a floor `0 < ε ≤ w(o)` on the behavior
policy's weights (`ε ≤ 1` follows), the thinned rejection decoder is within total
variation `(1 − ε)^N` of `T`, uniformly in `T`, `R`, `w`, and `o0`.  The paper
writes the floor as `ε^n` for a per-action floor `ε` over `n` steps; the `ε`
here is that product. -/
theorem tvDist_thinnedOutputLaw_le {ε : ℝ} {w T R : O → ℝ} (hε : 0 < ε)
    (hεw : ∀ o, ε ≤ w o) (hw1 : ∀ o, w o ≤ 1) (hT : IsDist T) (hR : IsDist R)
    (o0 : O) (N : ℕ) :
    tvDist (thinnedOutputLaw ε w T R o0 N) T ≤ (1 - ε) ^ N := by
  obtain ⟨o₁⟩ := nonempty_of_isDist hT
  rw [thinnedOutputLaw_eq hε hεw hw1 hT]
  exact tvDist_outputLaw_le ε hT (isDist_thinnedRest hεw hw1 hT hR)
    ((hεw o₁).trans (hw1 o₁)) o0 N

/-- The thinned decoder's error vanishes as `N → ∞`. -/
theorem tendsto_tvDist_thinnedOutputLaw {ε : ℝ} {w T R : O → ℝ} (hε : 0 < ε)
    (hεw : ∀ o, ε ≤ w o) (hw1 : ∀ o, w o ≤ 1) (hT : IsDist T) (hR : IsDist R) (o0 : O) :
    Tendsto (fun N : ℕ => tvDist (thinnedOutputLaw ε w T R o0 N) T) atTop (𝓝 0) := by
  obtain ⟨o₁⟩ := nonempty_of_isDist hT
  exact squeeze_zero (fun _ => tvDist_nonneg _ _)
    (fun N => tvDist_thinnedOutputLaw_le hε hεw hw1 hT hR o0 N)
    (tendsto_coverage_bound hε ((hεw o₁).trans (hw1 o₁)))

/-! ## Importance weighting: unbiasedness of the unnormalized estimator -/

/-- The importance weight of outcome `o` carried by the summary `a`:
`1 / w(o)` if `a` is a consistent episode with outcome `o`, else `0`. -/
noncomputable def weightInd (w : O → ℝ) (o : O) (a : Bool × O) : ℝ :=
  if a = (true, o) then 1 / w o else 0

theorem weightInd_nonneg {w : O → ℝ} (hw : ∀ o, 0 < w o) (o : O) (a : Bool × O) :
    0 ≤ weightInd w o a := by
  unfold weightInd
  split_ifs
  · exact div_nonneg zero_le_one (hw o).le
  · exact le_rfl

/-- The unnormalized importance-weighted empirical measure on an `N`-episode
transcript: `(1/N) Σ_k 1{consistent_k, o_k = o} / w(o)`. -/
noncomputable def iwEmpirical (w : O → ℝ) (N : ℕ) (x : Fin N → Bool × O) (o : O) : ℝ :=
  (∑ k, weightInd w o (x k)) / N

/-- Marginal of an i.i.d. product law at one coordinate: for a normalized weight
`f`, `∑_x (∏ᵢ f (xᵢ)) · g (x_k) = ∑_a f a · g a`. -/
theorem sum_prod_mul_eval {E : Type*} [Fintype E] (f : E → ℝ) (hf : ∑ a, f a = 1)
    {N : ℕ} (k : Fin N) (g : E → ℝ) :
    ∑ x : Fin N → E, (∏ i, f (x i)) * g (x k) = ∑ a, f a * g a := by
  set F : Fin N → E → ℝ := fun i a => f a * if i = k then g a else 1 with hF
  have h1 : ∀ x : Fin N → E, (∏ i, f (x i)) * g (x k) = ∏ i, F i (x i) := by
    intro x
    simp only [hF]
    rw [Finset.prod_mul_distrib]
    simp
  have h2 : ∀ i : Fin N, (∑ a, F i a) = if i = k then ∑ a, f a * g a else 1 := by
    intro i
    by_cases h : i = k <;> simp [hF, h, hf]
  calc ∑ x : Fin N → E, (∏ i, f (x i)) * g (x k)
      = ∑ x : Fin N → E, ∏ i, F i (x i) := Finset.sum_congr rfl fun x _ => h1 x
    _ = ∏ i, ∑ a, F i a := (Fintype.prod_sum F).symm
    _ = ∏ i : Fin N, (if i = k then ∑ a, f a * g a else 1) :=
        Finset.prod_congr rfl fun i _ => h2 i
    _ = ∑ a, f a * g a := by simp

theorem sum_tiltedLaw_mul_weightInd {w T R : O → ℝ} {o : O} (hw : w o ≠ 0) :
    ∑ a : Bool × O, tiltedLaw w T R a * weightInd w o a = T o := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [weightInd, Prod.mk.injEq, Bool.false_eq_true, false_and, if_false, mul_zero,
    Finset.sum_const_zero, add_zero, true_and, mul_ite, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, tiltedLaw_true]
  field_simp

/-- **Unbiasedness.**  Under the i.i.d. behavior-policy transcript law, the
unnormalized importance-weighted empirical measure has expectation exactly `T`. -/
theorem expect_iwEmpirical {w T R : O → ℝ} (hw : ∀ o, w o ≠ 0)
    (hR : ∑ o, R o = 1) {N : ℕ} (hN : 0 < N) (o : O) :
    ∑ x : Fin N → Bool × O, tiltedTranscriptLaw w T R N x * iwEmpirical w N x o = T o := by
  unfold iwEmpirical tiltedTranscriptLaw
  simp_rw [← mul_div_assoc, Finset.mul_sum]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [sum_prod_mul_eval (tiltedLaw w T R) (sum_tiltedLaw hR) _ (weightInd w o),
    sum_tiltedLaw_mul_weightInd (hw o)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  field_simp

/-! ## The resampling limit -/

section Asymptotic

open MeasureTheory ProbabilityTheory

variable [MeasurableSpace O] [MeasurableSingletonClass O]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem measurable_weightInd (w : O → ℝ) (o : O) : Measurable (weightInd w o) :=
  measurable_of_finite _

/-- `N_o / w(o)` over the first `n` episodes: the importance-weighted count of
consistent episodes with outcome `o`. -/
noncomputable def snisNum (w : O → ℝ) (X : ℕ → Ω → Bool × O) (o : O) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ range n, weightInd w o (X i ω)

/-- The self-normalizing denominator `Σ_{o'} N_{o'} / w(o')`. -/
noncomputable def snisDen (w : O → ℝ) (X : ℕ → Ω → Bool × O) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ o, snisNum w X o n ω

/-- The self-normalized importance-resampling decoder's conditional output law
given the first `n` episodes: `P̂_n(o) = (N_o / w(o)) / Σ_{o'} (N_{o'} / w(o'))`,
i.e. the law of the outcome of a consistent episode selected with probability
proportional to `1 / w`; the fallback `δ_{o0}` when no episode is consistent. -/
noncomputable def snisLaw (w : O → ℝ) (X : ℕ → Ω → Bool × O) (o0 : O) (n : ℕ) (ω : Ω)
    (o : O) : ℝ :=
  if snisDen w X n ω = 0 then (if o = o0 then 1 else 0)
  else snisNum w X o n ω / snisDen w X n ω

/-- The standing hypotheses on the episode-summary sequence `X`: measurable,
pairwise independent, identically distributed, and with the consistent part of
the law of one episode given by the splicing identity `w o * T o`.  (The law of
the inconsistent part is unconstrained: no decoder below uses it.) -/
structure IIDEpisodes (μ : Measure Ω) (w T : O → ℝ) (X : ℕ → Ω → Bool × O) : Prop where
  measurable : ∀ i, Measurable (X i)
  indep : Pairwise fun i j => IndepFun (X i) (X j) μ
  ident : ∀ i, IdentDistrib (X i) (X 0) μ μ
  law : ∀ o, μ.real (X 0 ⁻¹' {(true, o)}) = w o * T o

theorem integral_weightInd_comp [IsProbabilityMeasure μ] {w T : O → ℝ} {X : ℕ → Ω → Bool × O}
    (h : IIDEpisodes μ w T X) {o : O} (hw : w o ≠ 0) :
    μ[weightInd w o ∘ X 0] = T o := by
  have hset : MeasurableSet (X 0 ⁻¹' {(true, o)}) :=
    h.measurable 0 (measurableSet_singleton _)
  have hfun : weightInd w o ∘ X 0 =
      fun ω => (1 / w o) * (X 0 ⁻¹' {(true, o)}).indicator 1 ω := by
    funext ω
    by_cases hω : X 0 ω = (true, o)
    · simp [weightInd, hω]
    · simp [weightInd, hω]
  rw [hfun, integral_const_mul, integral_indicator_one hset, h.law o]
  field_simp

/-- **Etemadi's strong law on the numerators.**  Almost surely,
`(N_o / w(o)) / n → w(o) T(o) / w(o) = T(o)`. -/
theorem ae_tendsto_snisNum_div [IsProbabilityMeasure μ] {w T : O → ℝ}
    {X : ℕ → Ω → Bool × O} (h : IIDEpisodes μ w T X) (hw : ∀ o, 0 < w o) (o : O) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => snisNum w X o n ω / n) atTop (𝓝 (T o)) := by
  have hm : Measurable (weightInd w o) := measurable_weightInd w o
  have hint : Integrable (weightInd w o ∘ X 0) μ := by
    refine Integrable.of_bound (hm.comp (h.measurable 0)).aestronglyMeasurable (1 / w o)
      (ae_of_all _ fun ω => ?_)
    simp only [Function.comp, weightInd, Real.norm_eq_abs]
    split_ifs
    · exact le_of_eq (abs_of_pos (one_div_pos.2 (hw o)))
    · simp only [abs_zero]
      exact (one_div_pos.2 (hw o)).le
  have hindep : Pairwise fun i j => (weightInd w o ∘ X i) ⟂ᵢ[μ] (weightInd w o ∘ X j) :=
    fun i j hij => (h.indep hij).comp hm hm
  have hident : ∀ i, IdentDistrib (weightInd w o ∘ X i) (weightInd w o ∘ X 0) μ μ :=
    fun i => (h.ident i).comp hm
  have := strong_law_ae_real (fun i => weightInd w o ∘ X i) hint hindep hident
  rw [integral_weightInd_comp h (hw o).ne'] at this
  exact this

/-- **The resampling limit, coordinatewise.**  Almost surely, the self-normalized
estimator converges to `T` at every outcome. -/
theorem ae_tendsto_snisLaw [IsProbabilityMeasure μ] {w T : O → ℝ} {X : ℕ → Ω → Bool × O}
    (h : IIDEpisodes μ w T X) (hw : ∀ o, 0 < w o) (hT : ∑ o, T o = 1) (o0 : O) :
    ∀ᵐ ω ∂μ, ∀ o, Tendsto (fun n : ℕ => snisLaw w X o0 n ω o) atTop (𝓝 (T o)) := by
  have hall : ∀ᵐ ω ∂μ, ∀ o, Tendsto (fun n : ℕ => snisNum w X o n ω / n) atTop (𝓝 (T o)) :=
    ae_all_iff.2 fun o => ae_tendsto_snisNum_div h hw o
  filter_upwards [hall] with ω hω
  have hden : Tendsto (fun n : ℕ => snisDen w X n ω / n) atTop (𝓝 1) := by
    have : Tendsto (fun n : ℕ => ∑ o, snisNum w X o n ω / n) atTop (𝓝 (∑ o, T o)) :=
      tendsto_finsetSum _ fun o _ => hω o
    rw [hT] at this
    refine this.congr fun n => ?_
    simp [snisDen, Finset.sum_div]
  have hne : ∀ᶠ n : ℕ in atTop, snisDen w X n ω ≠ 0 := by
    filter_upwards [hden.eventually_ne one_ne_zero] with n hn
    intro h0
    apply hn
    simp [h0]
  intro o
  have hdiv : Tendsto (fun n : ℕ => (snisNum w X o n ω / n) / (snisDen w X n ω / n))
      atTop (𝓝 (T o / 1)) :=
    (hω o).div hden one_ne_zero
  rw [div_one] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [hne, eventually_ne_atTop 0] with n hn hn0
  simp only [snisLaw, if_neg hn]
  rw [div_div_div_cancel_right₀ (Nat.cast_ne_zero.2 hn0)]

/-- **The resampling limit in total variation.**  Almost surely,
`TV(P̂_n, T) → 0`. -/
theorem ae_tendsto_tvDist_snisLaw [IsProbabilityMeasure μ] {w T : O → ℝ}
    {X : ℕ → Ω → Bool × O} (h : IIDEpisodes μ w T X) (hw : ∀ o, 0 < w o)
    (hT : ∑ o, T o = 1) (o0 : O) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => tvDist (snisLaw w X o0 n ω) T) atTop (𝓝 0) := by
  filter_upwards [ae_tendsto_snisLaw h hw hT o0] with ω hω
  have : Tendsto (fun n : ℕ => (1 / 2 : ℝ) * ∑ o, |snisLaw w X o0 n ω o - T o|) atTop
      (𝓝 ((1 / 2 : ℝ) * ∑ o : O, |T o - T o|)) :=
    (tendsto_finsetSum _ fun o _ =>
      (continuous_abs.tendsto _).comp ((hω o).sub tendsto_const_nhds)).const_mul _
  simpa [tvDist] using this

/-! ### The decoder's output law -/

theorem snisNum_nonneg {w : O → ℝ} (hw : ∀ o, 0 < w o) (X : ℕ → Ω → Bool × O) (o : O)
    (n : ℕ) (ω : Ω) : 0 ≤ snisNum w X o n ω :=
  Finset.sum_nonneg fun _ _ => weightInd_nonneg hw o _

theorem snisNum_le_snisDen {w : O → ℝ} (hw : ∀ o, 0 < w o) (X : ℕ → Ω → Bool × O) (o : O)
    (n : ℕ) (ω : Ω) : snisNum w X o n ω ≤ snisDen w X n ω :=
  Finset.single_le_sum (fun o' _ => snisNum_nonneg hw X o' n ω) (Finset.mem_univ o)

theorem snisLaw_nonneg {w : O → ℝ} (hw : ∀ o, 0 < w o) (X : ℕ → Ω → Bool × O) (o0 : O)
    (n : ℕ) (ω : Ω) (o : O) : 0 ≤ snisLaw w X o0 n ω o := by
  unfold snisLaw
  split_ifs
  · exact zero_le_one
  · exact le_rfl
  · exact div_nonneg (snisNum_nonneg hw X o n ω)
      ((snisNum_nonneg hw X o n ω).trans (snisNum_le_snisDen hw X o n ω))

theorem snisLaw_le_one {w : O → ℝ} (hw : ∀ o, 0 < w o) (X : ℕ → Ω → Bool × O) (o0 : O)
    (n : ℕ) (ω : Ω) (o : O) : snisLaw w X o0 n ω o ≤ 1 := by
  unfold snisLaw
  split_ifs
  · exact le_rfl
  · exact zero_le_one
  · exact div_le_one_of_le₀ (snisNum_le_snisDen hw X o n ω)
      ((snisNum_nonneg hw X o n ω).trans (snisNum_le_snisDen hw X o n ω))

theorem measurable_snisNum {w : O → ℝ} {X : ℕ → Ω → Bool × O} (hX : ∀ i, Measurable (X i))
    (o : O) (n : ℕ) : Measurable (snisNum w X o n) :=
  Finset.measurable_sum _ fun i _ => (measurable_weightInd w o).comp (hX i)

theorem measurable_snisDen {w : O → ℝ} {X : ℕ → Ω → Bool × O} (hX : ∀ i, Measurable (X i))
    (n : ℕ) : Measurable (snisDen w X n) :=
  Finset.measurable_sum _ fun o _ => measurable_snisNum hX o n

theorem measurable_snisLaw {w : O → ℝ} {X : ℕ → Ω → Bool × O} (hX : ∀ i, Measurable (X i))
    (o0 : O) (n : ℕ) (o : O) : Measurable fun ω => snisLaw w X o0 n ω o := by
  unfold snisLaw
  exact Measurable.ite (measurable_snisDen hX n (measurableSet_singleton 0)) measurable_const
    ((measurable_snisNum hX o n).div (measurable_snisDen hX n))

/-- The importance-resampling decoder's output law after `n` episodes: the
expectation over transcripts of its conditional output law `snisLaw`. -/
noncomputable def snisOutputLaw (μ : Measure Ω) (w : O → ℝ) (X : ℕ → Ω → Bool × O) (o0 : O)
    (n : ℕ) (o : O) : ℝ :=
  ∫ ω, snisLaw w X o0 n ω o ∂μ

/-- **The paper's claim, literally**: the importance-resampling decoder's output
law converges to `T` (bounded convergence from the almost-sure limit). -/
theorem tendsto_snisOutputLaw [IsProbabilityMeasure μ] {w T : O → ℝ} {X : ℕ → Ω → Bool × O}
    (h : IIDEpisodes μ w T X) (hw : ∀ o, 0 < w o) (hT : ∑ o, T o = 1) (o0 o : O) :
    Tendsto (fun n : ℕ => snisOutputLaw μ w X o0 n o) atTop (𝓝 (T o)) := by
  have := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n ω => snisLaw w X o0 n ω o) (f := fun _ => T o) (fun _ => (1 : ℝ))
    (fun n => (measurable_snisLaw h.measurable o0 n o).aestronglyMeasurable)
    (integrable_const 1)
    (fun n => ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [snisLaw_nonneg hw X o0 n ω o], snisLaw_le_one hw X o0 n ω o⟩)
    ((ae_tendsto_snisLaw h hw hT o0).mono fun ω hω => hω o)
  simpa [snisOutputLaw, integral_const] using this

/-- The output law converges to `T` in total variation. -/
theorem tendsto_tvDist_snisOutputLaw [IsProbabilityMeasure μ] {w T : O → ℝ}
    {X : ℕ → Ω → Bool × O} (h : IIDEpisodes μ w T X) (hw : ∀ o, 0 < w o)
    (hT : ∑ o, T o = 1) (o0 : O) :
    Tendsto (fun n : ℕ => tvDist (snisOutputLaw μ w X o0 n) T) atTop (𝓝 0) := by
  have : Tendsto (fun n : ℕ => (1 / 2 : ℝ) * ∑ o, |snisOutputLaw μ w X o0 n o - T o|) atTop
      (𝓝 ((1 / 2 : ℝ) * ∑ o : O, |T o - T o|)) :=
    (tendsto_finsetSum _ fun o _ =>
      (continuous_abs.tendsto _).comp
        ((tendsto_snisOutputLaw h hw hT o0 o).sub tendsto_const_nhds)).const_mul _
  simpa [tvDist] using this

end Asymptotic

/-! ## The hypotheses are satisfiable: the i.i.d. episode process -/

section Construction

open MeasureTheory ProbabilityTheory

variable [MeasurableSpace O] [MeasurableSingletonClass O]

/-- The tilted per-episode law as a measure on `Bool × O`. -/
noncomputable def tiltedMeasure (w T R : O → ℝ) : Measure (Bool × O) :=
  ∑ a : Bool × O, ENNReal.ofReal (tiltedLaw w T R a) • Measure.dirac a

theorem tiltedMeasure_singleton (w T R : O → ℝ) (a : Bool × O) :
    tiltedMeasure w T R {a} = ENNReal.ofReal (tiltedLaw w T R a) := by
  simp [tiltedMeasure, Finset.sum_apply, Set.indicator_apply]

theorem isProbabilityMeasure_tiltedMeasure {w T R : O → ℝ} (hw : ∀ o, 0 ≤ w o)
    (hw1 : ∀ o, w o ≤ 1) (hT : IsDist T) (hR : IsDist R) :
    IsProbabilityMeasure (tiltedMeasure w T R) := by
  constructor
  simp only [tiltedMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun a _ => tiltedLaw_nonneg hw hw1 hT hR a,
    sum_tiltedLaw hR.2, ENNReal.ofReal_one]

/-- The i.i.d. episode process: the infinite product of `tiltedMeasure w T R` on
`ℕ → Bool × O`. -/
noncomputable def episodeMeasure (w T R : O → ℝ) : Measure (ℕ → Bool × O) :=
  Measure.infinitePi fun _ : ℕ => tiltedMeasure w T R

/-- The coordinate process: episode `i` is the `i`-th coordinate. -/
def coord : ℕ → (ℕ → Bool × O) → Bool × O := fun i ω => ω i

theorem isProbabilityMeasure_episodeMeasure {w T R : O → ℝ} (hw : ∀ o, 0 ≤ w o)
    (hw1 : ∀ o, w o ≤ 1) (hT : IsDist T) (hR : IsDist R) :
    IsProbabilityMeasure (episodeMeasure w T R) := by
  have := isProbabilityMeasure_tiltedMeasure hw hw1 hT hR
  unfold episodeMeasure
  infer_instance

/-- **The hypotheses of the limit theorems are satisfiable**: the coordinate
process under `episodeMeasure` is an `IIDEpisodes` sequence. -/
theorem iidEpisodes_episodeMeasure {w T R : O → ℝ} (hw : ∀ o, 0 ≤ w o) (hw1 : ∀ o, w o ≤ 1)
    (hT : IsDist T) (hR : IsDist R) :
    IIDEpisodes (episodeMeasure w T R) w T (coord (O := O)) := by
  have := isProbabilityMeasure_tiltedMeasure hw hw1 hT hR
  refine ⟨fun i => measurable_pi_apply i, ?_, ?_, ?_⟩
  · intro i j hij
    exact (iIndepFun_infinitePi (P := fun _ : ℕ => tiltedMeasure w T R)
      (X := fun _ : ℕ => (id : Bool × O → Bool × O)) fun _ => measurable_id).indepFun hij
  · intro i
    exact ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable, by
      show (episodeMeasure w T R).map (fun ω => ω i) = (episodeMeasure w T R).map (fun ω => ω 0)
      rw [episodeMeasure, Measure.infinitePi_map_eval, Measure.infinitePi_map_eval]⟩
  · intro o
    change ((episodeMeasure w T R) ((fun ω : ℕ → Bool × O => ω 0) ⁻¹' {(true, o)})).toReal
      = w o * T o
    rw [← Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton _),
      episodeMeasure, Measure.infinitePi_map_eval, tiltedMeasure_singleton, tiltedLaw_true,
      ENNReal.toReal_ofReal (mul_nonneg (hw o) (hT.1 o))]

/-- **The resampling limit on the concrete i.i.d. process**: almost surely,
`TV(P̂_n, T) → 0`. -/
theorem ae_tendsto_tvDist_snisLaw_episodeMeasure {w T R : O → ℝ} (hw : ∀ o, 0 < w o)
    (hw1 : ∀ o, w o ≤ 1) (hT : IsDist T) (hR : IsDist R) (o0 : O) :
    ∀ᵐ ω ∂(episodeMeasure w T R),
      Tendsto (fun n : ℕ => tvDist (snisLaw w coord o0 n ω) T) atTop (𝓝 0) := by
  have := isProbabilityMeasure_episodeMeasure (fun o => (hw o).le) hw1 hT hR
  exact ae_tendsto_tvDist_snisLaw (iidEpisodes_episodeMeasure (fun o => (hw o).le) hw1 hT hR)
    hw hT.2 o0

/-- **The paper's claim on the concrete i.i.d. process**: the
importance-resampling decoder's output law converges to `T` in total variation. -/
theorem tendsto_tvDist_snisOutputLaw_episodeMeasure {w T R : O → ℝ} (hw : ∀ o, 0 < w o)
    (hw1 : ∀ o, w o ≤ 1) (hT : IsDist T) (hR : IsDist R) (o0 : O) :
    Tendsto (fun n : ℕ => tvDist (snisOutputLaw (episodeMeasure w T R) w coord o0 n) T)
      atTop (𝓝 0) := by
  have := isProbabilityMeasure_episodeMeasure (fun o => (hw o).le) hw1 hT hR
  exact tendsto_tvDist_snisOutputLaw (iidEpisodes_episodeMeasure (fun o => (hw o).le) hw1 hT hR)
    hw hT.2 o0

end Construction

end ImportanceResampling
end IdExp
