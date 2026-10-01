import Formal.ConvexPotentialPolytopeAdmissibility
import Formal.QuadraticScoringRule
import Formal.CrossingDecisionWitnesses

/-!
# Proper scoring rules, Savage's entropy, and strict Blackwell monotonicity

A scoring rule pays `S q θ` for reporting the probability vector `q` when the
world is `θ`.  It is *proper* if honest reporting maximizes expected score
and *strictly proper* if it does so uniquely.  Savage's entropy
`G_S(p) = Σ_θ p_θ S p θ` is then convex, strictly convex for strictly proper
rules, and the Bayes value of the finite decision problem "report the prior
or a posterior" is exactly the expected posterior potential `Σ_x m_x G_S(π_x)`.
The Brier score has entropy `‖p‖²` (squared posterior movement) and the log
score has entropy `−H(p)` (information gain).

The main theorem is a characterization on a finite world class: a posterior
potential strictly preserves Blackwell domination for every full-support
prior **iff** it is strictly convex on the simplex.  The forward direction is
the equality case of data processing; the converse builds, from any failure
of strict convexity at `p ≠ p'`, a three-signal experiment with posteriors
`p, p', uniform` whose two-signal merge is strictly dominated (witnessed by
a two-decision unit-range task) yet scores at least as well.
-/

namespace IdExp

open Finset

noncomputable section

set_option linter.unusedSectionVars false

/-! ## Scoring rules and Savage's entropy -/

section Rules

variable {Θ : Type*} [Fintype Θ]

/-- A scoring rule: the payoff for reporting `q` when the world is `θ`. -/
abbrev ScoringRule (Θ : Type*) := (Θ → ℝ) → Θ → ℝ

/-- Expected score of the report `q` under the belief `p`. -/
def expectedScore (S : ScoringRule Θ) (p q : Θ → ℝ) : ℝ := ∑ θ, p θ * S q θ

/-- Savage's entropy: the expected score of honest reporting. -/
def scoringEntropy (S : ScoringRule Θ) (p : Θ → ℝ) : ℝ := expectedScore S p p

/-- Honest reporting is optimal. -/
def IsProper (S : ScoringRule Θ) : Prop :=
  ∀ p ∈ stdSimplex ℝ Θ, ∀ q ∈ stdSimplex ℝ Θ, expectedScore S p q ≤ expectedScore S p p

/-- Honest reporting is uniquely optimal. -/
def IsStrictlyProper (S : ScoringRule Θ) : Prop :=
  IsProper S ∧ ∀ p ∈ stdSimplex ℝ Θ, ∀ q ∈ stdSimplex ℝ Θ, p ≠ q →
    expectedScore S p q < expectedScore S p p

theorem expectedScore_add_smul (S : ScoringRule Θ) (a b : ℝ) (p p' q : Θ → ℝ) :
    expectedScore S (a • p + b • p') q = a * expectedScore S p q + b * expectedScore S p' q := by
  unfold expectedScore
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun θ _ => by ring

theorem smul_add_smul_ne_left {p p' : Θ → ℝ} (hne : p ≠ p') {a b : ℝ} (hb : 0 < b)
    (hab : a + b = 1) : a • p + b • p' ≠ p := by
  intro h
  apply hne
  funext θ
  have h1 := congrFun h θ
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1
  have ha : a = 1 - b := by linarith
  rw [ha] at h1
  have h2 : b * (p' θ - p θ) = 0 := by linear_combination h1
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd h hb.ne'
  · linarith

theorem smul_add_smul_ne_right {p p' : Θ → ℝ} (hne : p ≠ p') {a b : ℝ} (ha : 0 < a)
    (hab : a + b = 1) : a • p + b • p' ≠ p' := by
  intro h
  apply hne
  funext θ
  have h1 := congrFun h θ
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1
  have hb : b = 1 - a := by linarith
  rw [hb] at h1
  have h2 : a * (p θ - p' θ) = 0 := by linear_combination h1
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd h ha.ne'
  · linarith

/-- **Proper rules have convex entropy.** -/
theorem convexOn_scoringEntropy (S : ScoringRule Θ) (hS : IsProper S) :
    ConvexOn ℝ (stdSimplex ℝ Θ) (scoringEntropy S) := by
  refine ⟨convex_stdSimplex ℝ Θ, ?_⟩
  intro p hp p' hp' a b ha hb hab
  have hm : a • p + b • p' ∈ stdSimplex ℝ Θ := convex_stdSimplex ℝ Θ hp hp' ha hb hab
  show expectedScore S (a • p + b • p') (a • p + b • p') ≤
    a • scoringEntropy S p + b • scoringEntropy S p'
  rw [expectedScore_add_smul]
  have h1 := hS p hp _ hm
  have h2 := hS p' hp' _ hm
  simp only [smul_eq_mul, scoringEntropy]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

/-- **Strictly proper rules have strictly convex entropy.** -/
theorem strictConvexOn_scoringEntropy (S : ScoringRule Θ) (hS : IsStrictlyProper S) :
    StrictConvexOn ℝ (stdSimplex ℝ Θ) (scoringEntropy S) := by
  refine ⟨convex_stdSimplex ℝ Θ, ?_⟩
  intro p hp p' hp' hne a b ha hb hab
  have hm : a • p + b • p' ∈ stdSimplex ℝ Θ := convex_stdSimplex ℝ Θ hp hp' ha.le hb.le hab
  show expectedScore S (a • p + b • p') (a • p + b • p') <
    a • scoringEntropy S p + b • scoringEntropy S p'
  rw [expectedScore_add_smul]
  have h1 := hS.2 p hp _ hm (smul_add_smul_ne_left hne hb hab).symm
  have h2 := hS.2 p' hp' _ hm (smul_add_smul_ne_right hne ha hab).symm
  simp only [smul_eq_mul, scoringEntropy]
  nlinarith [mul_lt_mul_of_pos_left h1 ha, mul_lt_mul_of_pos_left h2 hb]

end Rules

/-! ## The report problem -/

section Report

variable {Θ X : Type*} [Fintype Θ] [Fintype X]

/-- Candidate reports: the prior, or the posterior at a signal (the prior at a
null signal, so every candidate lies in the simplex). -/
def scoreReport (α : Θ → ℝ) (E : FiniteExperiment Θ X) : Option X → Θ → ℝ
  | none => α
  | some x => if finiteBayesMass α E x = 0 then α else finiteBayesPosterior α E x

theorem scoreReport_mem_simplex (α : Θ → ℝ) (hα : IsDist α) (E : FiniteExperiment Θ X)
    (hE : IsFiniteExperiment E) (d : Option X) : scoreReport α E d ∈ stdSimplex ℝ Θ := by
  cases d with
  | none => exact hα
  | some x =>
    show (if finiteBayesMass α E x = 0 then α else finiteBayesPosterior α E x) ∈ stdSimplex ℝ Θ
    split_ifs with hx
    · exact hα
    · exact finiteBayesPosterior_mem_simplex α E hα.1 (fun θ x => (hE θ).1 x) x hx

/-- The report problem of a scoring rule as a finite decision problem. -/
def reportProblem (S : ScoringRule Θ) (α : Θ → ℝ) (E : FiniteExperiment Θ X) (θ : Θ)
    (d : Option X) : ℝ :=
  S (scoreReport α E d) θ

/-- The score at a signal is the predictive mass times the posterior expected utility. -/
theorem finiteDecisionScore_eq_mass_mul (α : Θ → ℝ) (hα : IsDist α) (E : FiniteExperiment Θ X)
    (hE : IsFiniteExperiment E) {D : Type*} [Fintype D] (u : Θ → D → ℝ) (x : X) (d : D) :
    finiteDecisionScore E α u x d =
      finiteBayesMass α E x * ∑ θ, finiteBayesPosterior α E x θ * u θ d := by
  unfold finiteDecisionScore
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro θ _
  have h := finiteBayesPosterior_mul_mass α E hα.1 (fun θ x => (hE θ).1 x) x θ
  have hm : finiteBayesMass α E x = ∑ c, α c * E c x := rfl
  rw [hm, ← h]
  ring

/-- **The report problem's value is the entropy potential** for any proper rule. -/
theorem finiteBayesValue_reportProblem (S : ScoringRule Θ) (hS : IsProper S) (α : Θ → ℝ)
    (hα : IsDist α) (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E) :
    finiteBayesValue E α (reportProblem S α E) =
      finiteBayesPotential (scoringEntropy S) α E := by
  unfold finiteBayesValue finiteBayesPotential
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : finiteBayesMass α E x = 0
  · rw [hx, zero_mul]
    apply le_antisymm
    · apply Finset.sup'_le
      intro d _
      rw [finiteDecisionScore_eq_mass_mul α hα E hE, hx, zero_mul]
    · refine le_trans (le_of_eq ?_) (Finset.le_sup' _ (Finset.mem_univ (none : Option X)))
      rw [finiteDecisionScore_eq_mass_mul α hα E hE, hx, zero_mul]
  · have hpost := finiteBayesPosterior_mem_simplex α E hα.1 (fun θ x => (hE θ).1 x) x hx
    have hm0 := finiteBayesMass_nonneg α E hα.1 (fun θ x => (hE θ).1 x) x
    apply le_antisymm
    · apply Finset.sup'_le
      intro d _
      rw [finiteDecisionScore_eq_mass_mul α hα E hE]
      exact mul_le_mul_of_nonneg_left (hS _ hpost _ (scoreReport_mem_simplex α hα E hE d)) hm0
    · refine le_trans (le_of_eq ?_) (Finset.le_sup' _ (Finset.mem_univ (some x)))
      rw [finiteDecisionScore_eq_mass_mul α hα E hE]
      simp only [reportProblem, scoreReport, if_neg hx]
      rfl

end Report

/-! ## Examples: the Brier and log scores -/

section Examples

variable {Θ : Type*} [Fintype Θ]

/-- The Brier score `2 q_θ − ‖q‖²`. -/
def brierScore (q : Θ → ℝ) (θ : Θ) : ℝ := 2 * q θ - posteriorQuadraticPotential q

theorem expectedScore_brier {p : Θ → ℝ} (hp : IsDist p) (q : Θ → ℝ) :
    expectedScore brierScore p q =
      posteriorQuadraticPotential p - posteriorQuadraticPotential (p - q) := by
  unfold expectedScore brierScore posteriorQuadraticPotential
  have h1 : ∑ θ, p θ * (2 * q θ - ∑ c, (q c)^2) =
      2 * ∑ θ, p θ * q θ - (∑ θ, p θ) * ∑ c, (q c)^2 := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro θ _
    ring
  rw [h1, hp.2]
  simp only [Pi.sub_apply]
  have h2 : ∑ θ, (p θ - q θ)^2 = ∑ θ, (p θ)^2 - 2 * ∑ θ, p θ * q θ + ∑ θ, (q θ)^2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro θ _
    ring
  rw [h2]
  ring

theorem posteriorQuadraticPotential_zero : posteriorQuadraticPotential (0 : Θ → ℝ) = 0 := by
  simp [posteriorQuadraticPotential]

/-- **The Brier score is strictly proper.** -/
theorem brierScore_strictlyProper : IsStrictlyProper (brierScore (Θ := Θ)) := by
  refine ⟨fun p hp q _ => ?_, fun p hp q _ hne => ?_⟩
  · rw [expectedScore_brier hp, expectedScore_brier hp, sub_self, posteriorQuadraticPotential_zero]
    have : 0 ≤ posteriorQuadraticPotential (p - q) := Finset.sum_nonneg fun θ _ => sq_nonneg _
    linarith
  · rw [expectedScore_brier hp, expectedScore_brier hp, sub_self, posteriorQuadraticPotential_zero]
    have : 0 < posteriorQuadraticPotential (p - q) := by
      obtain ⟨θ₀, hθ₀⟩ := Function.ne_iff.1 hne
      apply Finset.sum_pos' (fun θ _ => sq_nonneg _)
      exact ⟨θ₀, Finset.mem_univ _, sq_pos_iff.2 (sub_ne_zero.2 hθ₀)⟩
    linarith

/-- Savage's entropy of the Brier score is squared posterior movement. -/
theorem scoringEntropy_brier {p : Θ → ℝ} (hp : IsDist p) :
    scoringEntropy brierScore p = posteriorQuadraticPotential p := by
  unfold scoringEntropy
  rw [expectedScore_brier hp, sub_self, posteriorQuadraticPotential_zero, sub_zero]

/-- The log score `log q_θ`. -/
def logScore (q : Θ → ℝ) (θ : Θ) : ℝ := Real.log (q θ)

theorem logScore_term_le {pθ qθ : ℝ} (hp : 0 ≤ pθ) (hq : 0 < qθ) :
    pθ * Real.log qθ - pθ * Real.log pθ ≤ qθ - pθ := by
  rcases hp.lt_or_eq with hpθ | hpθ
  · have hne := hpθ.ne'
    have hdiv : 0 < qθ / pθ := div_pos hq hpθ
    have h := Real.log_le_sub_one_of_pos hdiv
    rw [Real.log_div hq.ne' hne] at h
    have h2 := mul_le_mul_of_nonneg_left h hpθ.le
    have h3 : pθ * (qθ / pθ - 1) = qθ - pθ := by field_simp
    rw [mul_sub] at h2
    linarith
  · rw [← hpθ]
    simp
    exact hq.le

/-- **Gibbs' inequality**: on positive reports the log score is proper. -/
theorem expectedScore_logScore_le {p q : Θ → ℝ} (hp : IsDist p) (hq : IsDist q)
    (hqpos : ∀ θ, 0 < q θ) : expectedScore logScore p q ≤ expectedScore logScore p p := by
  unfold expectedScore logScore
  have := Finset.sum_le_sum fun θ (_ : θ ∈ Finset.univ) => logScore_term_le (hp.1 θ) (hqpos θ)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hq.2, hp.2] at this
  linarith

/-- On positive beliefs and reports the log score is strictly proper. -/
theorem expectedScore_logScore_lt {p q : Θ → ℝ} (hp : IsDist p) (hq : IsDist q)
    (hppos : ∀ θ, 0 < p θ) (hqpos : ∀ θ, 0 < q θ) (hne : p ≠ q) :
    expectedScore logScore p q < expectedScore logScore p p := by
  unfold expectedScore logScore
  obtain ⟨θ₀, hθ₀⟩ := Function.ne_iff.1 hne
  have hstrict : p θ₀ * Real.log (q θ₀) - p θ₀ * Real.log (p θ₀) < q θ₀ - p θ₀ := by
    have hne0 := (hppos θ₀).ne'
    have hdiv : 0 < q θ₀ / p θ₀ := div_pos (hqpos θ₀) (hppos θ₀)
    have hne1 : q θ₀ / p θ₀ ≠ 1 := by
      intro h
      apply hθ₀
      field_simp at h
      linarith
    have h := Real.log_lt_sub_one_of_pos hdiv hne1
    rw [Real.log_div (hqpos θ₀).ne' hne0] at h
    have h2 := mul_lt_mul_of_pos_left h (hppos θ₀)
    have h3 : p θ₀ * (q θ₀ / p θ₀ - 1) = q θ₀ - p θ₀ := by field_simp
    rw [mul_sub] at h2
    linarith
  have hsum := Finset.sum_lt_sum
    (fun θ (_ : θ ∈ Finset.univ) => logScore_term_le (hp.1 θ) (hqpos θ))
    ⟨θ₀, Finset.mem_univ _, hstrict⟩
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hq.2, hp.2] at hsum
  linarith

/-- Savage's entropy of the log score is minus the Shannon entropy. -/
theorem scoringEntropy_logScore (p : Θ → ℝ) : scoringEntropy logScore p = -ent p := by
  unfold scoringEntropy expectedScore logScore ent
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro θ _
  rw [Real.negMulLog]
  ring

/-- Information gain is the log-score entropy potential plus the prior entropy. -/
theorem finiteBayesInformation_eq_logScore_potential {X : Type*} [Fintype X] (α : Θ → ℝ)
    (E : FiniteExperiment Θ X) :
    finiteBayesInformation α E = finiteBayesPotential (scoringEntropy logScore) α E + ent α := by
  unfold finiteBayesInformation finiteBayesPotential
  simp only [scoringEntropy_logScore, mul_neg, Finset.sum_neg_distrib]
  ring

end Examples

/-! ## Characterization: strict monotonicity ⟺ strict convexity -/

section Characterization

variable {Θ : Type*} [Fintype Θ] [Nonempty Θ] [DecidableEq Θ]

theorem uniformPrior_pos (θ : Θ) : 0 < uniformPrior Θ θ := by
  unfold uniformPrior
  have : (0 : ℝ) < Fintype.card Θ := by exact_mod_cast Fintype.card_pos
  positivity

theorem sum_uniformPrior : ∑ θ, uniformPrior Θ θ = 1 := by
  unfold uniformPrior
  have : (Fintype.card Θ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- Numerators of the three-signal tie witness: `a p / 2`, `(1−a) p' / 2`, `u / 2`. -/
def tieNum (p p' : Θ → ℝ) (a : ℝ) (θ : Θ) : Fin 3 → ℝ :=
  ![a / 2 * p θ, (1 - a) / 2 * p' θ, 1 / 2 * uniformPrior Θ θ]

/-- The tie-witness prior: half the mixture, half uniform (full support). -/
def tiePrior (p p' : Θ → ℝ) (a : ℝ) (θ : Θ) : ℝ :=
  (a * p θ + (1 - a) * p' θ + uniformPrior Θ θ) / 2

/-- The three-signal tie witness experiment, with posteriors `p`, `p'`, uniform. -/
def tieExperiment (p p' : Θ → ℝ) (a : ℝ) : FiniteExperiment Θ (Fin 3) :=
  fun θ x => tieNum p p' a θ x / tiePrior p p' a θ

/-- Merge the first two signals. -/
def mergeTwo : Fin 3 → Fin 2 → ℝ := fun x y => ![![(1 : ℝ), 0], ![1, 0], ![0, 1]] x y

theorem tieNum_sum (p p' : Θ → ℝ) (a : ℝ) (θ : Θ) :
    ∑ x, tieNum p p' a θ x = tiePrior p p' a θ := by
  simp [tieNum, tiePrior, Fin.sum_univ_three]
  ring

theorem tiePrior_pos {p p' : Θ → ℝ} (hp : IsDist p) (hp' : IsDist p') {a : ℝ} (ha : 0 ≤ a)
    (ha1 : a ≤ 1) (θ : Θ) : 0 < tiePrior p p' a θ := by
  have h1 : 0 ≤ a * p θ := mul_nonneg ha (hp.1 θ)
  have h2 : 0 ≤ (1 - a) * p' θ := mul_nonneg (by linarith) (hp'.1 θ)
  have h3 := uniformPrior_pos (Θ := Θ) θ
  unfold tiePrior
  linarith

theorem tiePrior_isDist {p p' : Θ → ℝ} (hp : IsDist p) (hp' : IsDist p') {a : ℝ} (ha : 0 ≤ a)
    (ha1 : a ≤ 1) : IsDist (tiePrior p p' a) := by
  refine ⟨fun θ => (tiePrior_pos hp hp' ha ha1 θ).le, ?_⟩
  unfold tiePrior
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, hp.2, hp'.2, sum_uniformPrior]
  ring

theorem tieNum_nonneg {p p' : Θ → ℝ} (hp : IsDist p) (hp' : IsDist p') {a : ℝ} (ha : 0 ≤ a)
    (ha1 : a ≤ 1) (θ : Θ) (x : Fin 3) : 0 ≤ tieNum p p' a θ x := by
  have h1 := hp.1 θ
  have h2 := hp'.1 θ
  have h3 := (uniformPrior_pos (Θ := Θ) θ).le
  fin_cases x <;> simp [tieNum] <;> nlinarith

theorem tieExperiment_valid {p p' : Θ → ℝ} (hp : IsDist p) (hp' : IsDist p') {a : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) : IsFiniteExperiment (tieExperiment p p' a) := by
  intro θ
  have hpos := tiePrior_pos hp hp' ha ha1 θ
  refine ⟨fun x => div_nonneg (tieNum_nonneg hp hp' ha ha1 θ x) hpos.le, ?_⟩
  unfold tieExperiment
  rw [← Finset.sum_div, tieNum_sum, div_self hpos.ne']

theorem tie_mul {p p' : Θ → ℝ} (hp : IsDist p) (hp' : IsDist p') {a : ℝ} (ha : 0 ≤ a)
    (ha1 : a ≤ 1) (θ : Θ) (x : Fin 3) :
    tiePrior p p' a θ * tieExperiment p p' a θ x = tieNum p p' a θ x := by
  have hne := (tiePrior_pos hp hp' ha ha1 θ).ne'
  unfold tieExperiment
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ hne]

/-- Column sums of the numerators: the predictive masses `a/2, (1−a)/2, 1/2`. -/
theorem tieNum_col_sum {p p' : Θ → ℝ} (hp : IsDist p) (hp' : IsDist p') (a : ℝ) (x : Fin 3) :
    ∑ θ, tieNum p p' a θ x = ![a / 2, (1 - a) / 2, 1 / 2] x := by
  fin_cases x <;>
    simp [tieNum, ← Finset.mul_sum, hp.2, hp'.2, sum_uniformPrior]

theorem tieMass {p p' : Θ → ℝ} (hp : IsDist p) (hp' : IsDist p') {a : ℝ} (ha : 0 ≤ a)
    (ha1 : a ≤ 1) (x : Fin 3) :
    finiteBayesMass (tiePrior p p' a) (tieExperiment p p' a) x = ![a / 2, (1 - a) / 2, 1 / 2] x := by
  unfold finiteBayesMass
  simp_rw [tie_mul hp hp' ha ha1]
  exact tieNum_col_sum hp hp' a x

theorem tiePosterior_zero {p p' : Θ → ℝ} (hp : IsDist p) (hp' : IsDist p') {a : ℝ} (ha : 0 < a)
    (ha1 : a ≤ 1) : finiteBayesPosterior (tiePrior p p' a) (tieExperiment p p' a) 0 = p := by
  funext θ
  unfold finiteBayesPosterior
  have hm := tieMass hp hp' ha.le ha1 0
  unfold finiteBayesMass at hm
  rw [hm, tie_mul hp hp' ha.le ha1]
  simp [tieNum]
  field_simp

theorem tiePosterior_one {p p' : Θ → ℝ} (hp : IsDist p) (hp' : IsDist p') {a : ℝ} (ha : 0 ≤ a)
    (ha1 : a < 1) : finiteBayesPosterior (tiePrior p p' a) (tieExperiment p p' a) 1 = p' := by
  funext θ
  unfold finiteBayesPosterior
  have hm := tieMass hp hp' ha ha1.le 1
  unfold finiteBayesMass at hm
  rw [hm, tie_mul hp hp' ha ha1.le]
  have hne : (1 - a) ≠ 0 := by linarith
  simp [tieNum]
  field_simp

theorem tiePosterior_two {p p' : Θ → ℝ} (hp : IsDist p) (hp' : IsDist p') {a : ℝ} (ha : 0 ≤ a)
    (ha1 : a ≤ 1) :
    finiteBayesPosterior (tiePrior p p' a) (tieExperiment p p' a) 2 = uniformPrior Θ := by
  funext θ
  unfold finiteBayesPosterior
  have hm := tieMass hp hp' ha ha1 2
  unfold finiteBayesMass at hm
  rw [hm, tie_mul hp hp' ha ha1]
  simp [tieNum] <;> ring

/-- The potential of the tie witness. -/
theorem tiePotential (Φ : (Θ → ℝ) → ℝ) {p p' : Θ → ℝ} (hp : IsDist p) (hp' : IsDist p')
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    finiteBayesPotential Φ (tiePrior p p' a) (tieExperiment p p' a) =
      a / 2 * Φ p + (1 - a) / 2 * Φ p' + 1 / 2 * Φ (uniformPrior Θ) := by
  unfold finiteBayesPotential
  rw [Fin.sum_univ_three, tieMass hp hp' ha.le ha1.le, tieMass hp hp' ha.le ha1.le,
    tieMass hp hp' ha.le ha1.le, tiePosterior_zero hp hp' ha ha1.le,
    tiePosterior_one hp hp' ha.le ha1, tiePosterior_two hp hp' ha.le ha1.le]
  simp

theorem mergeTwo_stochastic : mergeTwo ∈ stochasticRules (Fin 3) (Fin 2) := by
  intro x _
  refine ⟨fun y => ?_, ?_⟩
  · fin_cases x <;> fin_cases y <;> simp [mergeTwo]
  · fin_cases x <;> simp [mergeTwo, Fin.sum_univ_two]

/-- The merged experiment's rows. -/
theorem mergedRow_zero (p p' : Θ → ℝ) (a : ℝ) (θ : Θ) :
    finiteDecisionLaw (tieExperiment p p' a) mergeTwo θ 0 =
      tieExperiment p p' a θ 0 + tieExperiment p p' a θ 1 := by
  unfold finiteDecisionLaw mergeTwo
  simp [Fin.sum_univ_three]

theorem mergedRow_one (p p' : Θ → ℝ) (a : ℝ) (θ : Θ) :
    finiteDecisionLaw (tieExperiment p p' a) mergeTwo θ 1 = tieExperiment p p' a θ 2 := by
  unfold finiteDecisionLaw mergeTwo
  simp [Fin.sum_univ_three]

theorem merged_mul_zero {p p' : Θ → ℝ} (hp : IsDist p) (hp' : IsDist p') {a : ℝ} (ha : 0 ≤ a)
    (ha1 : a ≤ 1) (θ : Θ) :
    tiePrior p p' a θ * finiteDecisionLaw (tieExperiment p p' a) mergeTwo θ 0 =
      1 / 2 * (a * p θ + (1 - a) * p' θ) := by
  rw [mergedRow_zero, mul_add, tie_mul hp hp' ha ha1, tie_mul hp hp' ha ha1]
  simp [tieNum]
  ring

theorem merged_mul_one {p p' : Θ → ℝ} (hp : IsDist p) (hp' : IsDist p') {a : ℝ} (ha : 0 ≤ a)
    (ha1 : a ≤ 1) (θ : Θ) :
    tiePrior p p' a θ * finiteDecisionLaw (tieExperiment p p' a) mergeTwo θ 1 =
      tieNum p p' a θ 2 := by
  rw [mergedRow_one, tie_mul hp hp' ha ha1]

theorem mergedMass_zero {p p' : Θ → ℝ} (hp : IsDist p) (hp' : IsDist p') {a : ℝ} (ha : 0 ≤ a)
    (ha1 : a ≤ 1) :
    finiteBayesMass (tiePrior p p' a) (finiteDecisionLaw (tieExperiment p p' a) mergeTwo) 0 =
      1 / 2 := by
  unfold finiteBayesMass
  simp_rw [merged_mul_zero hp hp' ha ha1]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp.2, hp'.2]
  ring

theorem mergedMass_one {p p' : Θ → ℝ} (hp : IsDist p) (hp' : IsDist p') {a : ℝ} (ha : 0 ≤ a)
    (ha1 : a ≤ 1) :
    finiteBayesMass (tiePrior p p' a) (finiteDecisionLaw (tieExperiment p p' a) mergeTwo) 1 =
      1 / 2 := by
  unfold finiteBayesMass
  simp_rw [merged_mul_one hp hp' ha ha1]
  have := tieNum_col_sum hp hp' a 2
  simpa using this

theorem mergedPosterior_zero {p p' : Θ → ℝ} (hp : IsDist p) (hp' : IsDist p') {a : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    finiteBayesPosterior (tiePrior p p' a) (finiteDecisionLaw (tieExperiment p p' a) mergeTwo) 0 =
      a • p + (1 - a) • p' := by
  funext θ
  unfold finiteBayesPosterior
  have hm := mergedMass_zero hp hp' ha ha1
  unfold finiteBayesMass at hm
  rw [hm, merged_mul_zero hp hp' ha ha1]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp

theorem mergedPosterior_one {p p' : Θ → ℝ} (hp : IsDist p) (hp' : IsDist p') {a : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    finiteBayesPosterior (tiePrior p p' a) (finiteDecisionLaw (tieExperiment p p' a) mergeTwo) 1 =
      uniformPrior Θ := by
  funext θ
  unfold finiteBayesPosterior
  have hm := mergedMass_one hp hp' ha ha1
  unfold finiteBayesMass at hm
  rw [hm, merged_mul_one hp hp' ha ha1]
  simp [tieNum] <;> ring

/-- The potential of the merged experiment. -/
theorem mergedPotential (Φ : (Θ → ℝ) → ℝ) {p p' : Θ → ℝ} (hp : IsDist p) (hp' : IsDist p')
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    finiteBayesPotential Φ (tiePrior p p' a) (finiteDecisionLaw (tieExperiment p p' a) mergeTwo) =
      1 / 2 * Φ (a • p + (1 - a) • p') + 1 / 2 * Φ (uniformPrior Θ) := by
  unfold finiteBayesPotential
  rw [Fin.sum_univ_two, mergedMass_zero hp hp' ha ha1, mergedMass_one hp hp' ha ha1,
    mergedPosterior_zero hp hp' ha ha1, mergedPosterior_one hp hp' ha ha1]

/-- The two-decision witness task: answer whether the world is `θ₀` (payoff one if right),
or take the safe payoff `t`. -/
def witnessTask (θ₀ : Θ) (t : ℝ) : Θ → Fin 2 → ℝ :=
  fun θ d => if d = 0 then (if θ = θ₀ then 1 else 0) else t

theorem witnessTask_unit (θ₀ : Θ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (θ : Θ) (d : Fin 2) :
    witnessTask θ₀ t θ d ∈ Set.Icc (0 : ℝ) 1 := by
  unfold witnessTask
  split_ifs <;> constructor <;> linarith

/-- Scores of the tie witness under the task. -/
theorem tieScore_zero {p p' : Θ → ℝ} (hp : IsDist p) (hp' : IsDist p') {a : ℝ} (ha : 0 ≤ a)
    (ha1 : a ≤ 1) (θ₀ : Θ) (t : ℝ) (x : Fin 3) :
    finiteDecisionScore (tieExperiment p p' a) (tiePrior p p' a) (witnessTask θ₀ t) x 0 =
      tieNum p p' a θ₀ x := by
  unfold finiteDecisionScore witnessTask
  simp_rw [tie_mul hp hp' ha ha1]
  simp

theorem tieScore_one {p p' : Θ → ℝ} (hp : IsDist p) (hp' : IsDist p') {a : ℝ} (ha : 0 ≤ a)
    (ha1 : a ≤ 1) (θ₀ : Θ) (t : ℝ) (x : Fin 3) :
    finiteDecisionScore (tieExperiment p p' a) (tiePrior p p' a) (witnessTask θ₀ t) x 1 =
      t * ![a / 2, (1 - a) / 2, 1 / 2] x := by
  unfold finiteDecisionScore witnessTask
  simp_rw [tie_mul hp hp' ha ha1]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [h10, ↓reduceIte]
  rw [← Finset.sum_mul, tieNum_col_sum hp hp' a x, mul_comm]

theorem mergedScore_zero_zero {p p' : Θ → ℝ} (hp : IsDist p) (hp' : IsDist p') {a : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (θ₀ : Θ) (t : ℝ) :
    finiteDecisionScore (finiteDecisionLaw (tieExperiment p p' a) mergeTwo) (tiePrior p p' a)
      (witnessTask θ₀ t) 0 0 = 1 / 2 * (a * p θ₀ + (1 - a) * p' θ₀) := by
  unfold finiteDecisionScore witnessTask
  simp_rw [merged_mul_zero hp hp' ha ha1]
  simp

theorem mergedScore_zero_one {p p' : Θ → ℝ} (hp : IsDist p) (hp' : IsDist p') {a : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (θ₀ : Θ) (t : ℝ) :
    finiteDecisionScore (finiteDecisionLaw (tieExperiment p p' a) mergeTwo) (tiePrior p p' a)
      (witnessTask θ₀ t) 0 1 = t / 2 := by
  unfold finiteDecisionScore witnessTask
  simp_rw [merged_mul_zero hp hp' ha ha1]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [h10, ↓reduceIte]
  rw [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, hp.2, hp'.2]
  ring

theorem mergedScore_one {p p' : Θ → ℝ} (hp : IsDist p) (hp' : IsDist p') {a : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (θ₀ : Θ) (t : ℝ) (d : Fin 2) :
    finiteDecisionScore (finiteDecisionLaw (tieExperiment p p' a) mergeTwo) (tiePrior p p' a)
      (witnessTask θ₀ t) 1 d =
      finiteDecisionScore (tieExperiment p p' a) (tiePrior p p' a) (witnessTask θ₀ t) 2 d := by
  unfold finiteDecisionScore
  simp_rw [mergedRow_one]

/-- **The merged experiment is strictly dominated**: the witness task separates them. -/
theorem merged_value_lt {p p' : Θ → ℝ} (hp : IsDist p) (hp' : IsDist p') {a : ℝ} (ha : 0 < a)
    (ha1 : a < 1) {θ₀ : Θ} (hlt : p θ₀ < p' θ₀) :
    finiteBayesValue (finiteDecisionLaw (tieExperiment p p' a) mergeTwo) (tiePrior p p' a)
        (witnessTask θ₀ ((p θ₀ + p' θ₀) / 2)) <
      finiteBayesValue (tieExperiment p p' a) (tiePrior p p' a)
        (witnessTask θ₀ ((p θ₀ + p' θ₀) / 2)) := by
  set t := (p θ₀ + p' θ₀) / 2 with ht
  have ha0 := ha.le
  have ha1' := ha1.le
  unfold finiteBayesValue
  rw [Fin.sum_univ_three, Fin.sum_univ_two]
  -- the shared uniform-signal term
  have hshared : Finset.univ.sup' Finset.univ_nonempty
      (finiteDecisionScore (finiteDecisionLaw (tieExperiment p p' a) mergeTwo) (tiePrior p p' a)
        (witnessTask θ₀ t) 1) =
      Finset.univ.sup' Finset.univ_nonempty
        (finiteDecisionScore (tieExperiment p p' a) (tiePrior p p' a) (witnessTask θ₀ t) 2) := by
    congr 1
    funext d
    exact mergedScore_one hp hp' ha0 ha1' θ₀ t d
  rw [hshared]
  -- the key constant
  set K : ℝ := t * (a / 2) + (1 - a) / 2 * p' θ₀ with hK
  have hE0 : t * (a / 2) ≤ Finset.univ.sup' Finset.univ_nonempty
      (finiteDecisionScore (tieExperiment p p' a) (tiePrior p p' a) (witnessTask θ₀ t) 0) := by
    refine le_trans (le_of_eq ?_) (Finset.le_sup' _ (Finset.mem_univ (1 : Fin 2)))
    rw [tieScore_one hp hp' ha0 ha1']
    simp
  have hE1 : (1 - a) / 2 * p' θ₀ ≤ Finset.univ.sup' Finset.univ_nonempty
      (finiteDecisionScore (tieExperiment p p' a) (tiePrior p p' a) (witnessTask θ₀ t) 1) := by
    refine le_trans (le_of_eq ?_) (Finset.le_sup' _ (Finset.mem_univ (0 : Fin 2)))
    rw [tieScore_zero hp hp' ha0 ha1']
    simp [tieNum]
  have hF0 : Finset.univ.sup' Finset.univ_nonempty
      (finiteDecisionScore (finiteDecisionLaw (tieExperiment p p' a) mergeTwo) (tiePrior p p' a)
        (witnessTask θ₀ t) 0) < K := by
    have hd0 : finiteDecisionScore (finiteDecisionLaw (tieExperiment p p' a) mergeTwo)
        (tiePrior p p' a) (witnessTask θ₀ t) 0 0 < K := by
      rw [mergedScore_zero_zero hp hp' ha0 ha1']
      have : a * p θ₀ < a * t := mul_lt_mul_of_pos_left (by rw [ht]; linarith) ha
      rw [hK]; linarith
    have hd1 : finiteDecisionScore (finiteDecisionLaw (tieExperiment p p' a) mergeTwo)
        (tiePrior p p' a) (witnessTask θ₀ t) 0 1 < K := by
      rw [mergedScore_zero_one hp hp' ha0 ha1']
      have : (1 - a) * t < (1 - a) * p' θ₀ :=
        mul_lt_mul_of_pos_left (by rw [ht]; linarith) (by linarith)
      rw [hK]; linarith
    rw [Finset.sup'_lt_iff]
    intro d _
    fin_cases d
    · exact hd0
    · exact hd1
  linarith

/-- **From a failure of strict convexity, a strictly dominated tie.** -/
theorem exists_dominated_tie_of_not_strict (Φ : (Θ → ℝ) → ℝ) {p p' : Θ → ℝ} (hp : IsDist p)
    (hp' : IsDist p') {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {θ₀ : Θ} (hlt : p θ₀ < p' θ₀)
    (hge : a * Φ p + (1 - a) * Φ p' ≤ Φ (a • p + (1 - a) • p')) :
    ∃ α : Θ → ℝ, IsDist α ∧ (∀ θ, 0 < α θ) ∧
      ∃ (E : FiniteExperiment Θ (Fin 3)) (F : FiniteExperiment Θ (Fin 2)),
        IsFiniteExperiment E ∧ finiteDeficiency E F = 0 ∧
        finiteBayesPotential Φ α E ≤ finiteBayesPotential Φ α F ∧ 0 < finiteDeficiency F E := by
  have hE := tieExperiment_valid hp hp' ha.le ha1.le
  have hF : IsFiniteExperiment (finiteDecisionLaw (tieExperiment p p' a) mergeTwo) :=
    finiteDecisionLaw_valid _ hE _ mergeTwo_stochastic
  refine ⟨tiePrior p p' a, tiePrior_isDist hp hp' ha.le ha1.le, tiePrior_pos hp hp' ha.le ha1.le,
    tieExperiment p p' a, finiteDecisionLaw (tieExperiment p p' a) mergeTwo, hE, ?_, ?_, ?_⟩
  · exact finiteDeficiency_eq_zero_of_finiteBlackwellLE _ _ ⟨mergeTwo, mergeTwo_stochastic, rfl⟩
  · rw [tiePotential Φ hp hp' ha ha1, mergedPotential Φ hp hp' ha.le ha1.le]
    linarith
  · have hp0 : 0 ≤ p θ₀ := hp.1 θ₀
    have hp1 : p' θ₀ ≤ 1 :=
      (Finset.single_le_sum (fun c _ => hp'.1 c) (Finset.mem_univ θ₀)).trans_eq hp'.2
    have hgap := finiteBayesValue_sub_le_finiteDeficiency
      (finiteDecisionLaw (tieExperiment p p' a) mergeTwo) (tieExperiment p p' a) hF hE
      (tiePrior p p' a) (tiePrior_isDist hp hp' ha.le ha1.le)
      (witnessTask θ₀ ((p θ₀ + p' θ₀) / 2))
      (witnessTask_unit θ₀ (by linarith) (by linarith))
    have hval := merged_value_lt hp hp' ha ha1 hlt
    linarith

/-- **Strict monotonicity forces strict convexity.** -/
theorem strictConvexOn_of_potential_strict (Φ : (Θ → ℝ) → ℝ)
    (hstrict : ∀ α : Θ → ℝ, IsDist α → (∀ θ, 0 < α θ) →
      ∀ (E : FiniteExperiment Θ (Fin 3)) (F : FiniteExperiment Θ (Fin 2)),
        IsFiniteExperiment E → finiteDeficiency E F = 0 →
          finiteBayesPotential Φ α E ≤ finiteBayesPotential Φ α F → finiteDeficiency F E = 0) :
    StrictConvexOn ℝ (stdSimplex ℝ Θ) Φ := by
  refine ⟨convex_stdSimplex ℝ Θ, ?_⟩
  intro p hp p' hp' hne a b ha hb hab
  by_contra hge
  have hge := not_lt.1 hge
  simp only [smul_eq_mul] at hge
  have hb' : b = 1 - a := by linarith
  subst hb'
  obtain ⟨θ₀, hθ₀⟩ := Function.ne_iff.1 hne
  rcases lt_or_gt_of_ne hθ₀ with hlt | hlt
  · obtain ⟨α, hα, hpos, E, F, hE, h0, hle, hpos'⟩ :=
      exists_dominated_tie_of_not_strict Φ hp hp' ha (by linarith) hlt hge
    exact absurd (hstrict α hα hpos E F hE h0 hle) hpos'.ne'
  · have hge' : (1 - a) * Φ p' + (1 - (1 - a)) * Φ p ≤ Φ ((1 - a) • p' + (1 - (1 - a)) • p) := by
      have e1 : (1 - (1 - a)) = a := by ring
      rw [e1, add_comm ((1 - a) • p') (a • p), add_comm ((1 - a) * Φ p') (a * Φ p)]
      exact hge
    obtain ⟨α, hα, hpos, E, F, hE, h0, hle, hpos'⟩ :=
      exists_dominated_tie_of_not_strict Φ hp' hp (by linarith : 0 < 1 - a)
        (by linarith : 1 - a < 1) hlt hge'
    exact absurd (hstrict α hα hpos E F hE h0 hle) hpos'.ne'

/-- **Characterization.**  A posterior potential strictly preserves Blackwell
domination for every full-support prior iff it is strictly convex on the
simplex.  (The forward direction holds for all finite alphabets; three and two
signals suffice for the converse.) -/
theorem strictConvexOn_iff_potential_strict (Φ : (Θ → ℝ) → ℝ) :
    StrictConvexOn ℝ (stdSimplex ℝ Θ) Φ ↔
      ∀ α : Θ → ℝ, IsDist α → (∀ θ, 0 < α θ) →
        ∀ (E : FiniteExperiment Θ (Fin 3)) (F : FiniteExperiment Θ (Fin 2)),
          IsFiniteExperiment E → finiteDeficiency E F = 0 →
            finiteBayesPotential Φ α E ≤ finiteBayesPotential Φ α F →
              finiteDeficiency F E = 0 :=
  ⟨fun hΦ α hα hpos E F hE h0 hle =>
      potential_strict_of_deficiency_eq_zero Φ hΦ α hα hpos E hE F h0 hle,
    strictConvexOn_of_potential_strict Φ⟩

/-- **Strictly proper rules score strictly monotonically**: the report problem
of a strictly proper rule strictly preserves Blackwell domination under any
full-support prior. -/
theorem reportProblem_strict {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (S : ScoringRule Θ) (hS : IsStrictlyProper S) (α : Θ → ℝ) (hα : IsDist α)
    (hpos : ∀ θ, 0 < α θ) (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (F : FiniteExperiment Θ Y) (hF : IsFiniteExperiment F) (h0 : finiteDeficiency E F = 0)
    (hle : finiteBayesValue E α (reportProblem S α E) ≤ finiteBayesValue F α (reportProblem S α F)) :
    finiteDeficiency F E = 0 := by
  rw [finiteBayesValue_reportProblem S hS.1 α hα E hE,
    finiteBayesValue_reportProblem S hS.1 α hα F hF] at hle
  exact potential_strict_of_deficiency_eq_zero _ (strictConvexOn_scoringEntropy S hS) α hα hpos E hE
    F h0 hle

end Characterization

end

end IdExp
