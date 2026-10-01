import Formal.InfiniteInformationGain
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-! Actual posterior probability measures and Mathlib KL divergence.
This identifies the density-based information functional with expected
finite KL, rather than relying on an informal entropy interpretation. -/

set_option maxHeartbeats 1000000

namespace IdExp

open MeasureTheory InformationTheory Set Finset

variable {Θ X : Type*} [MeasurableSpace Θ] [Fintype X]

/-- The posterior as a probability measure, using the prior at a null signal. -/
noncomputable def priorPosteriorMeasure (μ : Measure Θ) (E : FiniteExperiment Θ X) (x : X) :
    Measure Θ := μ.withDensity (fun θ => ENNReal.ofReal (priorSignalDensity μ E x θ))

theorem priorPosteriorMeasure_probability (μ : Measure Θ) [IsProbabilityMeasure μ]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (hi : ∀ x, Integrable (fun θ => E θ x) μ) (x : X) :
    IsProbabilityMeasure (priorPosteriorMeasure μ E x) := by
  constructor
  rw [priorPosteriorMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (priorSignalDensity_integrable μ E hi x)
      (Filter.Eventually.of_forall (priorSignalDensity_nonneg μ E hE x)),
    priorSignalDensity_integral_one]
  norm_num

theorem priorPosteriorMeasure_absolutelyContinuous (μ : Measure Θ)
    (E : FiniteExperiment Θ X) (x : X) : priorPosteriorMeasure μ E x ≪ μ :=
  withDensity_absolutelyContinuous _ _

variable [TopologicalSpace Θ] [OpensMeasurableSpace Θ]

/-- The actual posterior's Radon-Nikodym density is the normalized finite
likelihood, almost everywhere under the prior. -/
theorem priorPosteriorMeasure_rnDeriv (μ : Measure Θ) [IsProbabilityMeasure μ]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (hc : ∀ x, Continuous (fun θ => E θ x)) (x : X) :
    (fun θ => ((priorPosteriorMeasure μ E x).rnDeriv μ θ).toReal) =ᵐ[μ]
      priorSignalDensity μ E x := by
  have hd := priorSignalDensity_mem_boundedContinuousDensityDomain μ E hE hc x
  have hr := Measure.rnDeriv_withDensity μ hd.1.measurable.ennreal_ofReal
  filter_upwards [hr] with θ hθ
  simpa [priorPosteriorMeasure, ENNReal.toReal_ofReal (priorSignalDensity_nonneg μ E hE x θ)]
    using congrArg ENNReal.toReal hθ

/-- No infinite KL is hidden by taking its real value: every finite-signal
posterior has finite KL relative to its prior, including the null convention. -/
theorem priorPosteriorMeasure_klDiv_ne_top (μ : Measure Θ) [IsProbabilityMeasure μ]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (hc : ∀ x, Continuous (fun θ => E θ x)) (x : X) :
    klDiv (priorPosteriorMeasure μ E x) μ ≠ ⊤ := by
  let _ := priorPosteriorMeasure_probability μ E hE
    (integrable_finiteExperiment_coordinate μ E hE hc) x
  have hac := priorPosteriorMeasure_absolutelyContinuous μ E x
  apply klDiv_ne_top hac
  apply (integrable_klFun_rnDeriv_iff hac).mp
  have hd := priorSignalDensity_mem_boundedContinuousDensityDomain μ E hE hc x
  have hi := ((integrable_density_mul_log μ hd).add (integrable_const 1)).sub
    (priorSignalDensity_integrable μ E (integrable_finiteExperiment_coordinate μ E hE hc) x)
  apply hi.congr
  filter_upwards [priorPosteriorMeasure_rnDeriv μ E hE hc x] with θ hθ
  simp [klFun, hθ]

/-- The integral of f log f is exactly Mathlib's KL for the actual posterior. -/
theorem priorPosteriorMeasure_klDiv_toReal (μ : Measure Θ) [IsProbabilityMeasure μ]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (hc : ∀ x, Continuous (fun θ => E θ x)) (x : X) :
    (klDiv (priorPosteriorMeasure μ E x) μ).toReal =
      densityInformationPotential μ (priorSignalDensity μ E x) := by
  let _ := priorPosteriorMeasure_probability μ E hE
    (integrable_finiteExperiment_coordinate μ E hE hc) x
  rw [toReal_klDiv_eq_integral_klFun (priorPosteriorMeasure_absolutelyContinuous μ E x)]
  have he : (fun θ => klFun ((priorPosteriorMeasure μ E x).rnDeriv μ θ).toReal) =ᵐ[μ]
      (fun θ => priorSignalDensity μ E x θ * Real.log (priorSignalDensity μ E x θ) + 1 -
        priorSignalDensity μ E x θ) := by
    filter_upwards [priorPosteriorMeasure_rnDeriv μ E hE hc x] with θ hθ
    simp [klFun, hθ]
  rw [integral_congr_ae he]
  have hi := integrable_density_mul_log μ
    (priorSignalDensity_mem_boundedContinuousDensityDomain μ E hE hc x)
  have hs := integral_sub (hi.add (integrable_const 1))
    (priorSignalDensity_integrable μ E (integrable_finiteExperiment_coordinate μ E hE hc) x)
  have ha := integral_add hi (integrable_const 1)
  simp only [Pi.add_apply] at hs ha
  rw [hs, ha, priorSignalDensity_integral_one]
  simp [densityInformationPotential]

/-- Literal expected posterior KL, with finiteness established separately. -/
theorem infinitePriorInformation_eq_expected_klDiv
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (hc : ∀ x, Continuous (fun θ => E θ x)) :
    infinitePriorInformation μ E =
      ∑ x, priorSignalMass μ E x * (klDiv (priorPosteriorMeasure μ E x) μ).toReal := by
  simp_rw [priorPosteriorMeasure_klDiv_toReal μ E hE hc]
  rfl

end IdExp
