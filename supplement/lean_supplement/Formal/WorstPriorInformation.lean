import Formal.InfinitePosteriorKL

/-! Raw worst-prior information gain is zero. The adversarial prior in
uniform decision regret is a different role from the prior defining an
intrinsic information reward. -/

namespace IdExp

open MeasureTheory Set Finset

variable {Θ X : Type*} [TopologicalSpace Θ] [MeasurableSpace Θ]
  [OpensMeasurableSpace Θ] [Fintype X]

theorem infinitePriorInformation_nonneg (μ : Measure Θ) [IsProbabilityMeasure μ]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (hc : ∀ x, Continuous (fun θ => E θ x)) : 0 ≤ infinitePriorInformation μ E := by
  rw [infinitePriorInformation_eq_expected_klDiv μ E hE hc]
  apply Finset.sum_nonneg
  intro x _
  exact mul_nonneg (integral_nonneg (fun θ => (hE θ).1 x)) ENNReal.toReal_nonneg

/-- A point-mass prior already knows the world. Null-signal posteriors use
the prior itself, so they cause no undefined entropy subtraction. -/
theorem infinitePriorInformation_dirac [MeasurableSingletonClass Θ]
    (E : FiniteExperiment Θ X) (θ : Θ) :
    infinitePriorInformation (Measure.dirac θ) E = 0 := by
  unfold infinitePriorInformation priorSignalPotential densityInformationPotential
  apply Finset.sum_eq_zero
  intro x _
  simp only [integral_dirac]
  have hd : priorSignalDensity (Measure.dirac θ) E x θ = 1 := by
    simp only [priorSignalDensity, priorSignalMass, integral_dirac]
    split_ifs with h
    · rfl
    · exact div_self h
  rw [hd]
  simp

/-- This infimum ranges over all actual probability measures, on an arbitrary
nonempty topological world class with continuous finite-signal laws. -/
theorem sInf_priorInformation_eq_zero [Nonempty Θ] [MeasurableSingletonClass Θ]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (hc : ∀ x, Continuous (fun θ => E θ x)) :
    sInf {c : ℝ | ∃ μ : Measure Θ, IsProbabilityMeasure μ ∧ c = infinitePriorInformation μ E} = 0 := by
  let S : Set ℝ := {c | ∃ μ : Measure Θ, IsProbabilityMeasure μ ∧ c = infinitePriorInformation μ E}
  have hzero : 0 ∈ S :=
    ⟨Measure.dirac (Classical.arbitrary Θ), inferInstance, (infinitePriorInformation_dirac E _).symm⟩
  have hb : ∀ c ∈ S, 0 ≤ c := by
    rintro c ⟨μ, hμ, rfl⟩
    let _ := hμ
    exact infinitePriorInformation_nonneg μ E hE hc
  exact le_antisymm (csInf_le ⟨0, hb⟩ hzero) (le_csInf ⟨0, hzero⟩ hb)

end IdExp
