import Formal.CountableAtoms
import Formal.MeasureDeficiencyCore

/-!
# Exact-label deficiency on an uncountable class

This completes `prop:countable-atoms` in the causal-first paper.  The old
atom argument rules out exact garbling.  Here it is connected to the actual
measure-experiment deficiency: every Markov decoder has worst-world error
one, and the infimum of those errors is exactly one.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace IdExp

variable {Ω Θ X : Type*}

/-- The variation of a difference of mutually singular positive measures is
their sum.  No probability normalization is needed for this identity. -/
theorem totalVariation_sub_of_mutuallySingular [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : μ ⟂ₘ ν) :
    (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation = μ + ν := by
  let j : JordanDecomposition Ω :=
    { posPart := μ
      negPart := ν
      posPart_finite := inferInstance
      negPart_finite := inferInstance
      mutuallySingular := h }
  change j.toSignedMeasure.totalVariation = μ + ν
  rw [SignedMeasure.totalVariation,
    JordanDecomposition.toJordanDecomposition_toSignedMeasure]

/-- Mutually singular probability laws are at total-variation distance one. -/
theorem finiteMeasureTV_eq_one_of_mutuallySingular [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : μ ⟂ₘ ν) : finiteMeasureTV μ ν = 1 := by
  unfold finiteMeasureTV
  rw [totalVariation_sub_of_mutuallySingular μ ν h, measureReal_def,
    Measure.add_apply, measure_univ, measure_univ]
  norm_num

/-- The full-revelation experiment, bundled for measure-level deficiency. -/
noncomputable def exactLabelExperiment (Θ : Type*) [MeasurableSpace Θ] :
    Θ → FiniteMeasure Θ :=
  fun θ => ⟨Measure.dirac θ, inferInstance⟩

/-- Every finite-signal decoder misses some world completely. -/
theorem exists_exactLabel_decode_error_one
    [MeasurableSpace Θ] [MeasurableSingletonClass Θ]
    [MeasurableSpace X] [MeasurableSingletonClass X] [Fintype X]
    (hΘ : ¬ Countable Θ) (E : Θ → FiniteMeasure X)
    (hE : ∀ θ, IsProbabilityMeasure (E θ : Measure X))
    (G : FiniteMarkovKernel X Θ) :
    ∃ θ, finiteMeasureTV (finiteMarkovDecode G (E θ) : Measure Θ)
      (exactLabelExperiment Θ θ : Measure Θ) = 1 := by
  let : IsMarkovKernel G.toKernel := G.isMarkov
  obtain ⟨θ, hθ⟩ : ∃ θ, θ ∉ ⋃ x, atoms (G.toKernel x) := by
    by_contra! hall
    apply hΘ
    exact countable_univ_iff.mp ((countable_iUnion_atoms G.toKernel).mono
      (fun θ _ => hall θ))
  have := hE θ
  have := isProbabilityMeasure_finiteMarkovDecode G (E θ)
  have : IsProbabilityMeasure (exactLabelExperiment Θ θ : Measure Θ) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.dirac θ))
  refine ⟨θ, finiteMeasureTV_eq_one_of_mutuallySingular _ _ ?_⟩
  change (G.toKernel ∘ₘ (E θ : Measure X)) ⟂ₘ Measure.dirac θ
  exact (mutuallySingular_dirac_bind (E θ : Measure X) G.toKernel hθ).symm

/-- A finite-outcome experiment on an uncountable class has exact-label
directed deficiency exactly one, not merely a nonattained zero decoder. -/
theorem finiteMeasureDeficiency_exactLabel_eq_one
    [MeasurableSpace Θ] [MeasurableSingletonClass Θ] [Nonempty Θ]
    [MeasurableSpace X] [MeasurableSingletonClass X] [Fintype X]
    (hΘ : ¬ Countable Θ) (E : Θ → FiniteMeasure X)
    (hE : ∀ θ, IsProbabilityMeasure (E θ : Measure X)) :
    finiteMeasureDeficiency E (exactLabelExperiment Θ) = 1 := by
  have hF : ∀ θ, IsProbabilityMeasure (exactLabelExperiment Θ θ : Measure Θ) :=
    fun _ => inferInstanceAs (IsProbabilityMeasure (Measure.dirac _))
  apply le_antisymm
  · exact finiteMeasureDeficiency_le_one_of_prob E (exactLabelExperiment Θ) hE hF
  · apply le_csInf
      (finiteMeasureDeficiencyCandidates_nonempty_of_prob E (exactLabelExperiment Θ) hE hF)
    rintro c ⟨G, hG⟩
    obtain ⟨θ, hθ⟩ := exists_exactLabel_decode_error_one hΘ E hE G
    exact hθ ▸ hG θ

end IdExp
