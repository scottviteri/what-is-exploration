import Formal.MeasureDeficiency

/-!
# From measurable finite probability rows to a Markov kernel

This adapter imposes measurability on the parameterized rows, without assuming
a finite world class or any localization or causal structure.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace IdExp

variable {Θ X Y : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
  [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]

/-- Measurable finite probability rows determine a genuine Markov kernel,
even when the parameter space is uncountable. -/
noncomputable def measurableRowKernel (T : FiniteExperiment Θ Y)
    (hT : IsFiniteExperiment T) (hm : ∀ y, Measurable (fun θ => T θ y)) :
    FiniteMarkovKernel Θ Y where
  toKernel := {
    toFun := fun θ => (rowExperiment T θ : Measure Y)
    measurable' := by
      have heq : (fun θ => (rowExperiment T θ : Measure Y)) =
          fun θ => ∑ y, ENNReal.ofReal (T θ y) • Measure.dirac y := by
        funext θ
        rw [← Measure.sum_smul_dirac (rowExperiment T θ : Measure Y),
          Measure.sum_fintype]
        simp only [rowExperiment, finiteMeasureOfRow_singleton]
      rw [heq]
      exact Finset.measurable_sum _ fun y _ => (hm y).ennreal_ofReal.smul_measure _ }
  isMarkov := ⟨fun θ => isProbabilityMeasure_finiteMeasureOfRow _ (hT θ)⟩

end IdExp
