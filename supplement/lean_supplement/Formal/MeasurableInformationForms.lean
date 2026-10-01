import Formal.InfiniteInformationGain
import Formal.ReverseDecoderPinsker

/-!
# Finite-output information on arbitrary measurable world classes

The posterior-density definition agrees with the integrated log-ratio and
signal-entropy formulas. Measurable finite probability rows supply all
integrability premises. Null predictive signals vanish almost everywhere;
no topology, support, or atom-mass hypothesis on the worlds is imposed.
-/

namespace IdExp

open MeasureTheory Set Finset

noncomputable section

variable {Θ X Y : Type*} [MeasurableSpace Θ] [Fintype X] [Fintype Y]

theorem integrable_measurableFiniteExperiment_coordinate
    (μ : Measure Θ) [IsFiniteMeasure μ] (E : FiniteExperiment Θ X)
    (hE : IsFiniteExperiment E) (hm : ∀ x, Measurable (fun θ => E θ x)) (x : X) :
    Integrable (fun θ => E θ x) μ := by
  apply Integrable.of_bound (hm x).aestronglyMeasurable 1
  filter_upwards [] with θ
  rw [Real.norm_eq_abs, abs_of_nonneg ((hE θ).1 x)]
  exact (single_le_sum (fun z _ => (hE θ).1 z) (mem_univ x)).trans_eq (hE θ).2

theorem integrable_continuous_unit_composition
    (μ : Measure Θ) [IsFiniteMeasure μ] (f : Θ → ℝ) (hm : Measurable f)
    (hf : ∀ θ, f θ ∈ Set.Icc (0 : ℝ) 1) (φ : ℝ → ℝ) (hφ : Continuous φ) :
    Integrable (fun θ => φ (f θ)) μ := by
  obtain ⟨B, hB⟩ := ((isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).image hφ.norm).bddAbove
  apply Integrable.of_bound (hφ.measurable.comp hm).aestronglyMeasurable B
  filter_upwards [] with θ
  exact hB ⟨f θ, hf θ, rfl⟩

theorem integrable_finiteExperiment_mul_log
    (μ : Measure Θ) [IsFiniteMeasure μ] (E : FiniteExperiment Θ X)
    (hE : IsFiniteExperiment E) (hm : ∀ x, Measurable (fun θ => E θ x)) (x : X) :
    Integrable (fun θ => E θ x * Real.log (E θ x)) μ :=
  integrable_continuous_unit_composition μ _ (hm x)
    (fun θ => ⟨(hE θ).1 x,
      (single_le_sum (fun z _ => (hE θ).1 z) (mem_univ x)).trans_eq (hE θ).2⟩)
    _ Real.continuous_mul_log

theorem integrable_finiteExperiment_ent
    (μ : Measure Θ) [IsFiniteMeasure μ] (E : FiniteExperiment Θ X)
    (hE : IsFiniteExperiment E) (hm : ∀ x, Measurable (fun θ => E θ x)) :
    Integrable (fun θ => ent (E θ)) μ := by
  apply integrable_finsetSum
  intro x _
  apply (integrable_finiteExperiment_mul_log μ E hE hm x).neg.congr
  filter_upwards [] with θ
  simp [Real.negMulLog]

theorem mul_log_div_eq (x m : ℝ) (hm : m ≠ 0) :
    x * Real.log (x / m) = x * Real.log x - x * Real.log m := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.log_div hx hm]; ring

theorem integrable_finiteExperiment_log_ratio
    (μ : Measure Θ) [IsFiniteMeasure μ] (E : FiniteExperiment Θ X)
    (hE : IsFiniteExperiment E) (hm : ∀ x, Measurable (fun θ => E θ x))
    (x : X) (m : ℝ) : Integrable (fun θ => E θ x * Real.log (E θ x / m)) μ := by
  by_cases hm0 : m = 0
  · simp [hm0]
  · simp_rw [mul_log_div_eq _ _ hm0]
    exact (integrable_finiteExperiment_mul_log μ E hE hm x).sub
      ((integrable_measurableFiniteExperiment_coordinate μ E hE hm x).mul_const _)

theorem priorSignalMass_zero_ae (μ : Measure Θ) [IsFiniteMeasure μ]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (hm : ∀ x, Measurable (fun θ => E θ x)) (x : X)
    (hx : priorSignalMass μ E x = 0) : (fun θ => E θ x) =ᵐ[μ] 0 :=
  (integral_eq_zero_iff_of_nonneg (fun θ => (hE θ).1 x)
    (integrable_measurableFiniteExperiment_coordinate μ E hE hm x)).mp hx

theorem infinitePriorInformation_eq_integral_finiteKL
    (μ : Measure Θ) [IsFiniteMeasure μ] (E : FiniteExperiment Θ X)
    (hE : IsFiniteExperiment E) (hm : ∀ x, Measurable (fun θ => E θ x)) :
    infinitePriorInformation μ E = ∫ θ, finiteKL (E θ) (priorSignalMass μ E) ∂μ := by
  unfold infinitePriorInformation priorSignalPotential finiteKL densityInformationPotential
  rw [integral_finsetSum _ (fun x _ => integrable_finiteExperiment_log_ratio μ E hE hm x _)]
  apply sum_congr rfl
  intro x _
  by_cases hx : priorSignalMass μ E x = 0
  · simp [hx]
  · rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with θ
    simp only [priorSignalDensity, if_neg hx]
    field_simp

theorem infinitePriorInformation_eq_ent_mass_sub
    (μ : Measure Θ) [IsFiniteMeasure μ] (E : FiniteExperiment Θ X)
    (hE : IsFiniteExperiment E) (hm : ∀ x, Measurable (fun θ => E θ x)) :
    infinitePriorInformation μ E = ent (priorSignalMass μ E) - ∫ θ, ent (E θ) ∂μ := by
  rw [infinitePriorInformation_eq_integral_finiteKL μ E hE hm]
  have hterm (x : X) : (∫ θ, E θ x * Real.log (E θ x / priorSignalMass μ E x) ∂μ) =
      (∫ θ, E θ x * Real.log (E θ x) ∂μ) -
        priorSignalMass μ E x * Real.log (priorSignalMass μ E x) := by
    by_cases hx : priorSignalMass μ E x = 0
    · have he := priorSignalMass_zero_ae μ E hE hm x hx
      have hz : (∫ θ, E θ x * Real.log (E θ x) ∂μ) = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [he] with θ hθ
        simp [hθ]
      simp [hx, hz]
    · simp_rw [mul_log_div_eq _ _ hx]
      rw [integral_sub (integrable_finiteExperiment_mul_log μ E hE hm x)
        ((integrable_measurableFiniteExperiment_coordinate μ E hE hm x).mul_const _),
        integral_mul_const]
      rfl
  have hneg (x : X) : Integrable (fun θ => Real.negMulLog (E θ x)) μ := by
    apply (integrable_finiteExperiment_mul_log μ E hE hm x).neg.congr
    filter_upwards [] with θ
    simp [Real.negMulLog]
  unfold finiteKL ent
  rw [integral_finsetSum _ (fun x _ => integrable_finiteExperiment_log_ratio μ E hE hm x _),
    integral_finsetSum _ (fun x _ => hneg x)]
  simp_rw [hterm, Real.negMulLog, neg_mul, integral_neg]
  rw [sum_sub_distrib, sum_neg_distrib, sum_neg_distrib]
  ring

omit [Fintype Y] in
theorem measurable_finiteDecisionLaw (E : FiniteExperiment Θ X)
    (hm : ∀ x, Measurable (fun θ => E θ x)) (G : X → Y → ℝ) (y : Y) :
    Measurable (fun θ => finiteDecisionLaw E G θ y) :=
  Finset.measurable_sum _ fun x _ => (hm x).mul_const _

end
end IdExp
