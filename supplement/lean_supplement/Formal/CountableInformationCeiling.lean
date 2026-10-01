import Formal.MeasurableInformationForms
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! Finite-signal information is bounded by the integrable surprisal of an
atomic prior. The bound applies to every experiment, including randomized
history-dependent causal records. Information is the existing posterior-density
functional, connected to the finite-KL integral, not a replacement score. -/
namespace IdExp
open MeasureTheory Finset Set Filter
noncomputable section
variable {Θ S : Type*} [MeasurableSpace Θ] [MeasurableSingletonClass Θ]
  [Fintype S]

theorem priorSignalMass_ge_atom (μ : Measure Θ) [IsProbabilityMeasure μ]
    (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E)
    (hm : ∀ s, Measurable (fun θ => E θ s)) (θ : Θ) (s : S) :
    μ.real {θ} * E θ s ≤ priorSignalMass μ E s := by
  have h := setIntegral_le_integral
    (integrable_measurableFiniteExperiment_coordinate μ E hE hm s)
    (Eventually.of_forall (fun η => (hE η).1 s)) (s := {θ})
  simpa [integral_singleton, smul_eq_mul, priorSignalMass, measureReal_def] using h

theorem finiteKL_prior_bounds (μ : Measure Θ) [IsProbabilityMeasure μ]
    (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E)
    (hm : ∀ s, Measurable (fun θ => E θ s)) (θ : Θ)
    (hp : 0 < μ.real {θ}) :
    0 ≤ finiteKL (E θ) (priorSignalMass μ E) ∧
    finiteKL (E θ) (priorSignalMass μ E) ≤ -Real.log (μ.real {θ}) := by
  have hmass := priorSignalMass_isDist μ E hE
    (integrable_measurableFiniteExperiment_coordinate μ E hE hm)
  have hac : ∀ s, priorSignalMass μ E s = 0 → E θ s = 0 := by
    intro s hs
    have h := priorSignalMass_ge_atom μ E hE hm θ s
    rw [hs] at h
    have := (hE θ).1 s
    nlinarith
  constructor
  · have h := finiteTV_sq_le_finiteKL_half (E θ) (priorSignalMass μ E) (hE θ) hmass hac
    nlinarith [sq_nonneg (finiteTV (E θ) (priorSignalMass μ E))]
  · calc
      finiteKL (E θ) (priorSignalMass μ E) ≤
          ∑ s, E θ s * (-Real.log (μ.real {θ})) := by
        apply sum_le_sum
        intro s _
        by_cases hz : E θ s = 0
        · simp [hz]
        have he : 0 < E θ s := lt_of_le_of_ne ((hE θ).1 s) (Ne.symm hz)
        have hl := priorSignalMass_ge_atom μ E hE hm θ s
        have hmp : 0 < priorSignalMass μ E s := lt_of_lt_of_le (mul_pos hp he) hl
        apply mul_le_mul_of_nonneg_left _ he.le
        calc
          Real.log (E θ s / priorSignalMass μ E s) ≤ Real.log (1 / μ.real {θ}) := by
            apply Real.log_le_log (div_pos he hmp)
            apply (div_le_div_iff₀ hmp hp).mpr
            nlinarith
          _ = -Real.log (μ.real {θ}) := by rw [one_div, Real.log_inv]
      _ = -Real.log (μ.real {θ}) := by rw [← sum_mul, (hE θ).2, one_mul]

theorem integrable_finiteKL_prior (μ : Measure Θ) [IsProbabilityMeasure μ]
    (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E)
    (hm : ∀ s, Measurable (fun θ => E θ s)) :
    Integrable (fun θ => finiteKL (E θ) (priorSignalMass μ E)) μ := by
  exact integrable_finsetSum _ (fun s _ => integrable_finiteExperiment_log_ratio μ E hE hm s _)

theorem information_le_atomic_entropy (μ : Measure Θ) [IsProbabilityMeasure μ]
    (hp : ∀ θ, 0 < μ.real {θ})
    (hi : Integrable (fun θ => -Real.log (μ.real {θ})) μ)
    (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E)
    (hm : ∀ s, Measurable (fun θ => E θ s)) :
    infinitePriorInformation μ E ≤ ∫ θ, -Real.log (μ.real {θ}) ∂μ := by
  rw [infinitePriorInformation_eq_integral_finiteKL μ E hE hm]
  exact integral_mono (integrable_finiteKL_prior μ E hE hm) hi
    (fun θ => (finiteKL_prior_bounds μ E hE hm θ (hp θ)).2)
end
end IdExp
