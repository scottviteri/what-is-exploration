import Formal.PosteriorMovement

/-!
The countable-world Bayes identity for the literal posterior Hellinger and
Absolute rewards, including null observations. This closes the summation step
between posterior movement and the expected predictive formula; it does not
change either objective or assume positive likelihoods.
-/
noncomputable section
namespace IdExp.PosteriorMovement
open MeasureTheory Finset Set

theorem loss_bounds (kind : Kind) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    0 ≤ loss kind x y ∧ loss kind x y ≤ 2 := by
  cases kind
  · simp only [loss]
    have hsx := Real.sq_sqrt hx.1
    have hsy := Real.sq_sqrt hy.1
    have hp := mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)
    exact ⟨sq_nonneg _, by nlinarith [hx.2, hy.2]⟩
  · exact ⟨abs_nonneg _, abs_le.mpr (by constructor <;> linarith [hx.1, hx.2, hy.1, hy.2])⟩

theorem loss_nonneg_le_add (kind : Kind) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ loss kind x y ∧ loss kind x y ≤ x + y := by
  cases kind
  · simp only [loss]
    have hsx := Real.sq_sqrt hx
    have hsy := Real.sq_sqrt hy
    have hp := mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)
    exact ⟨sq_nonneg _, by nlinarith⟩
  · exact ⟨abs_nonneg _, abs_le.mpr (by constructor <;> linarith)⟩

/-- The literal world-coordinate distance is a convergent series, so the real
`tsum` in the expectation is not relying on the non-summable default. -/
theorem posterior_distance_summable {Θ : Type*} (kind : Kind)
    (p q : FullLabelBrierReport Θ) : Summable (fun θ => loss kind (p θ) (q θ)) :=
  Summable.of_nonneg_of_le
    (fun θ => (loss_nonneg_le_add kind (p.nonneg θ) (q.nonneg θ)).1)
    (fun θ => (loss_nonneg_le_add kind (p.nonneg θ) (q.nonneg θ)).2)
    (p.summable.add q.summable)

variable {Θ O : Type*} [Countable Θ] [MeasurableSpace Θ]
  [MeasurableSingletonClass Θ] [Fintype O]
variable (kind : Kind) (μ : Measure Θ) [IsProbabilityMeasure μ]
  (E : FiniteExperiment Θ O) (hE : IsFiniteExperiment E)

include hE

theorem predictive_loss_integrable (o : O) :
    Integrable (fun θ => loss kind (E θ o) (priorSignalMass μ E o)) μ := by
  have hq (θ : Θ) : E θ o ∈ Icc (0 : ℝ) 1 :=
    ⟨(hE θ).1 o, (single_le_sum (fun x _ => (hE θ).1 x) (mem_univ o)).trans_eq (hE θ).2⟩
  have hm := CountableBrier.mass_valid μ E hE
  have hb : priorSignalMass μ E o ∈ Icc (0 : ℝ) 1 :=
    ⟨hm.1 o, (single_le_sum (fun x _ => hm.1 x) (mem_univ o)).trans_eq hm.2⟩
  apply (integrable_const (2 : ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun θ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (loss_bounds kind (hq θ) hb).1]
    exact (loss_bounds kind (hq θ) hb).2

/-- The weighted coordinate identity is valid even at a null observation or a
zero-prior world. The posterior is the actual Bayesian posterior measure. -/
theorem posterior_loss_coordinate (o : O) (θ : Θ) :
    priorSignalMass μ E o *
      loss kind (CountableBrier.posterior μ E hE o θ) (μ.real {θ}) =
    μ.real {θ} * loss kind (E θ o) (priorSignalMass μ E o) := by
  have hm := (CountableBrier.mass_valid μ E hE).1 o
  have hb : 0 ≤ μ.real {θ} := measureReal_nonneg
  by_cases hz : priorSignalMass μ E o = 0
  · have hj := CountableBrier.mass_mul_posterior μ E hE o θ
    rw [hz, zero_mul] at hj
    rcases mul_eq_zero.mp hj.symm with hb0 | hq0
    · simp [hz, hb0]
    · simp [hz, hq0]
  · have hp : CountableBrier.posterior μ E hE o θ =
        μ.real {θ} * E θ o / priorSignalMass μ E o := by
      apply (eq_div_iff hz).2
      simpa [mul_comm] using CountableBrier.mass_mul_posterior μ E hE o θ
    rw [hp]
    exact bayes_coordinate_identity kind _ _ _ hb ((hE θ).1 o) (lt_of_le_of_ne hm (Ne.symm hz))

/-- Exact countable posterior-movement expectation equals the expected
predictive divergence used by the alarm and finite-world calculations. -/
theorem expected_posterior_movement_eq_reward :
    (∑ o, priorSignalMass μ E o *
      ∑' θ, loss kind (CountableBrier.posterior μ E hE o θ) (μ.real {θ})) =
    reward kind μ E := by
  unfold reward coordinate
  apply sum_congr rfl
  intro o _
  change _ = ∫ θ, loss kind (E θ o) (priorSignalMass μ E o) ∂μ
  rw [integral_countable (predictive_loss_integrable kind μ E hE o), ← tsum_mul_left]
  apply tsum_congr
  intro θ
  simpa only [smul_eq_mul] using posterior_loss_coordinate kind μ E hE o θ

/-- The same formula with the world integral outside the finite observation
sum, as in the displayed source-faithfulness identity in the manuscript. -/
theorem expected_posterior_movement_eq_integral :
    (∑ o, priorSignalMass μ E o *
      ∑' θ, loss kind (CountableBrier.posterior μ E hE o θ) (μ.real {θ})) =
    ∫ θ, ∑ o, loss kind (E θ o) (priorSignalMass μ E o) ∂μ := by
  rw [expected_posterior_movement_eq_reward kind μ E hE,
    integral_finsetSum _ (fun o _ => predictive_loss_integrable kind μ E hE o)]
  rfl

/-- Literal double-sum form used in the paper, with no unproved exchange of
an infinite world sum and a finite observation sum. -/
theorem expected_posterior_movement_eq_sum :
    (∑ o, priorSignalMass μ E o *
      ∑' θ, loss kind (CountableBrier.posterior μ E hE o θ) (μ.real {θ})) =
    ∑' θ, μ.real {θ} * ∑ o, loss kind (E θ o) (priorSignalMass μ E o) := by
  rw [expected_posterior_movement_eq_integral kind μ E hE,
    integral_countable (integrable_finsetSum _
      (fun o _ => predictive_loss_integrable kind μ E hE o))]
  rfl

end IdExp.PosteriorMovement
