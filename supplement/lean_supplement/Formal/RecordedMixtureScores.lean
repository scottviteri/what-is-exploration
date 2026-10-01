import Formal.MixturePurposeValue
import Formal.CrossingMixtureAudit
import Formal.InformationDeficiencyContinuity

/-!
# Recording the label makes posterior scores linear

For the recorded-label mixture `E_p` (sample a collector `i ∼ p`, keep the
label and the signal) the posterior after `(i, x)` is the posterior of `E_i`
after `x`, and the predictive mass is `p_i` times that of `E_i`.  Hence every
posterior-potential score, in particular information gain and squared
posterior movement, is linear: `S(E_p) = Σ_i p_i S(E_i)`.

This is the sentence "a policy choosing `A` with probability `r` and
recording its choice has each posterior score equal to the corresponding
mixture of the pure scores" of the crossing example, and it gives the
example's two remaining selection rules exactly: information gain uniquely
selects `r = 0` (pure `B`) and squared posterior movement uniquely selects
`r = 1` (pure `A`), while the native audit uniquely selects `r = 1/2`
(`CrossingMixtureAudit`).
-/

namespace IdExp

open Finset

noncomputable section

set_option linter.unusedSectionVars false

section Linear

variable {Θ X : Type*} [Fintype Θ] [Fintype X] {ι : Type*} [Fintype ι]

theorem finiteBayesMass_mixtureCollector (α : Θ → ℝ) (E : ι → FiniteExperiment Θ X)
    (p : ι → ℝ) (i : ι) (x : X) :
    finiteBayesMass α (mixtureCollector E p) (i, x) = p i * finiteBayesMass α (E i) x := by
  unfold finiteBayesMass mixtureCollector
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun θ _ => by ring

theorem finiteBayesPosterior_mixtureCollector (α : Θ → ℝ) (E : ι → FiniteExperiment Θ X)
    (p : ι → ℝ) (i : ι) (x : X) (hi : p i ≠ 0) :
    finiteBayesPosterior α (mixtureCollector E p) (i, x) = finiteBayesPosterior α (E i) x := by
  funext θ
  unfold finiteBayesPosterior mixtureCollector
  have hden : (∑ c, α c * (p i * E i c x)) = p i * ∑ c, α c * E i c x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  show α θ * (p i * E i θ x) / ∑ c, α c * (p i * E i c x) = α θ * E i θ x / ∑ c, α c * E i c x
  rw [hden]
  by_cases hm : (∑ c, α c * E i c x) = 0
  · rw [hm, mul_zero, div_zero, div_zero]
  · field_simp

/-- **Posterior-potential scores are linear in recorded-label mixtures.** -/
theorem finiteBayesPotential_mixtureCollector (Φ : (Θ → ℝ) → ℝ) (α : Θ → ℝ)
    (E : ι → FiniteExperiment Θ X) (p : ι → ℝ) :
    finiteBayesPotential Φ α (mixtureCollector E p) =
      ∑ i, p i * finiteBayesPotential Φ α (E i) := by
  unfold finiteBayesPotential
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [finiteBayesMass_mixtureCollector]
  by_cases hi : p i = 0
  · rw [hi, zero_mul, zero_mul, zero_mul]
  · rw [finiteBayesPosterior_mixtureCollector α E p i x hi]
    ring

/-- **Information gain is linear in recorded-label mixtures.** -/
theorem finiteBayesInformation_mixtureCollector (α : Θ → ℝ) (E : ι → FiniteExperiment Θ X)
    {p : ι → ℝ} (hp : IsDist p) :
    finiteBayesInformation α (mixtureCollector E p) =
      ∑ i, p i * finiteBayesInformation α (E i) := by
  unfold finiteBayesInformation
  rw [finiteBayesPotential_mixtureCollector]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp.2, one_mul]

/-- **Squared posterior movement is linear in recorded-label mixtures.** -/
theorem quadraticPosteriorScore_mixtureCollector (α : Θ → ℝ) (E : ι → FiniteExperiment Θ X)
    {p : ι → ℝ} (hp : IsDist p) :
    quadraticPosteriorScore α (mixtureCollector E p) =
      ∑ i, p i * quadraticPosteriorScore α (E i) := by
  unfold quadraticPosteriorScore
  rw [finiteBayesPotential_mixtureCollector]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp.2, one_mul]

end Linear

/-! ## The crossing example's three selection rules -/

section Crossing

/-- The recorded mixture of the crossing example is a recorded-label mixture. -/
theorem recordedMixture_eq_mixtureCollector (r : ℝ) :
    recordedMixture r = mixtureCollector ![testA, testB] ![r, 1 - r] := by
  funext θ z
  obtain ⟨c, o⟩ := z
  fin_cases c <;> simp [recordedMixture, mixtureCollector]

theorem crossingWeights_isDist {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : IsDist ![r, 1 - r] := by
  refine ⟨fun c => ?_, ?_⟩
  · fin_cases c <;> simp <;> linarith
  · simp [Fin.sum_univ_two]

/-- Information gain of the recorded mixture: `r·h₂(3/10) + (1−r)·h₂(2/5)`. -/
theorem information_recordedMixture {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    finiteBayesInformation crossingPrior (recordedMixture r) =
      r * Real.binEntropy (3 / 10) + (1 - r) * Real.binEntropy (2 / 5) := by
  rw [recordedMixture_eq_mixtureCollector,
    finiteBayesInformation_mixtureCollector _ _ (crossingWeights_isDist hr0 hr1)]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [show finiteBayesInformation crossingPrior testA = Real.binEntropy (3 / 10) from
    information_crossingA, show finiteBayesInformation crossingPrior testB =
    Real.binEntropy (2 / 5) from information_crossingB]

/-- Squared posterior movement of the recorded mixture: `r·57/175 + (1−r)·97/300`. -/
theorem quadratic_recordedMixture {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    quadraticPosteriorScore crossingPrior (recordedMixture r) =
      r * (57 / 175) + (1 - r) * (97 / 300) := by
  rw [recordedMixture_eq_mixtureCollector,
    quadraticPosteriorScore_mixtureCollector _ _ (crossingWeights_isDist hr0 hr1)]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [show quadraticPosteriorScore crossingPrior testA = 57 / 175 from quadratic_crossingA,
    show quadraticPosteriorScore crossingPrior testB = 97 / 300 from quadratic_crossingB]

/-- **Information gain uniquely selects the pure `B` collector (`r = 0`).** -/
theorem information_selects_B {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    finiteBayesInformation crossingPrior (recordedMixture r) ≤
      finiteBayesInformation crossingPrior (recordedMixture 0) ∧
    (finiteBayesInformation crossingPrior (recordedMixture r) =
      finiteBayesInformation crossingPrior (recordedMixture 0) ↔ r = 0) := by
  rw [information_recordedMixture hr0 hr1, information_recordedMixture le_rfl zero_le_one]
  have hgap : Real.binEntropy (3 / 10) < Real.binEntropy (2 / 5) := by
    have := information_prefers_crossingB
    rwa [information_crossingA, information_crossingB] at this
  constructor
  · nlinarith
  · constructor
    · intro h
      nlinarith
    · rintro rfl
      ring

/-- **Squared posterior movement uniquely selects the pure `A` collector (`r = 1`).** -/
theorem quadratic_selects_A {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    quadraticPosteriorScore crossingPrior (recordedMixture r) ≤
      quadraticPosteriorScore crossingPrior (recordedMixture 1) ∧
    (quadraticPosteriorScore crossingPrior (recordedMixture r) =
      quadraticPosteriorScore crossingPrior (recordedMixture 1) ↔ r = 1) := by
  rw [quadratic_recordedMixture hr0 hr1, quadratic_recordedMixture zero_le_one le_rfl]
  constructor
  · nlinarith
  · constructor
    · intro h
      nlinarith
    · rintro rfl
      ring

end Crossing

end

end IdExp
