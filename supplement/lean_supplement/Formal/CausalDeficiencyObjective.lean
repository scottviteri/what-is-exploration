import Formal.DeficiencyObjective
import Formal.CausalFiniteRecovery

/-!
# Exact completeness of the causal full-revelation deficiency objective

This module proves the negative randomized-deficiency clause of the paper's
finite attained-top objective theorem on the literal causal trajectory laws.
Native sufficiency is equivalent to maximizing this objective only when full
revelation is attainable. Finiteness alone does not supply that hypothesis.

The finite-prefix objectives also converge to the terminal objective for
every policy, not just at identifying policies. This is a statement about
complete undiscounted optimization; no claim is made about greedy rewards or
discounted optimization.
-/

namespace IdExp

open MeasureTheory ProbabilityTheory Filter Topology

variable {Θ : Type*} [Fintype Θ] [Nonempty Θ] [DecidableEq Θ]
  [MeasurableSpace Θ] [MeasurableSingletonClass Θ]
  {A O : Type*} [Fintype A] [Fintype O] [Nonempty A] [Nonempty O]
  [MeasurableSpace A] [MeasurableSpace O]
  [MeasurableSingletonClass A] [MeasurableSingletonClass O]

/-- Complete-path negative randomized deficiency to full revelation. -/
noncomputable def causalFullRevelationObjective
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) : ℝ :=
  negativeExactLabelDeficiency (causalPathExperiment Qs hQ π)

omit [Fintype Θ] [DecidableEq Θ] [MeasurableSingletonClass Θ] in
theorem causalFullRevelationObjective_nonpos
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) : causalFullRevelationObjective Qs hQ π ≤ 0 :=
  negativeExactLabelDeficiency_nonpos _
    (isProbabilityMeasure_causalPathExperiment' Qs hQ π)

omit [DecidableEq Θ] in
/-- Identification is exactly value zero, without an attainability premise. -/
theorem causalFullRevelationObjective_eq_zero_iff_exactlyIdentifies
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) :
    causalFullRevelationObjective Qs hQ π = 0 ↔ CausalExactlyIdentifies Qs hQ π :=
  negativeExactLabelDeficiency_eq_zero_iff_decoder _
    (isProbabilityMeasure_causalPathExperiment' Qs hQ π)

/-- Full revelation is attainable exactly when zero is an attained maximum
of the complete-path objective. -/
theorem causalFullRevelationObjective_isGreatest_zero_iff_attainable
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ)) :
    IsGreatest (Set.range (causalFullRevelationObjective Qs hQ)) 0 ↔
      CausalFullRevelationAttainable Qs hQ := by
  rw [causalFullRevelationAttainable_iff_exactlyIdentifies Qs hQ]
  constructor
  · rintro ⟨⟨π, hπ⟩, _⟩
    exact ⟨π, (causalFullRevelationObjective_eq_zero_iff_exactlyIdentifies Qs hQ π).1 hπ⟩
  · rintro ⟨π, hπ⟩
    refine ⟨⟨π, (causalFullRevelationObjective_eq_zero_iff_exactlyIdentifies Qs hQ π).2 hπ⟩, ?_⟩
    rintro _ ⟨σ, rfl⟩
    exact causalFullRevelationObjective_nonpos Qs hQ σ

theorem causalFullRevelationObjective_maximizer_iff_exactlyIdentifies
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hattain : CausalFullRevelationAttainable Qs hQ) (π : ValidCausalPolicy A O) :
    (∀ σ, causalFullRevelationObjective Qs hQ σ ≤ causalFullRevelationObjective Qs hQ π) ↔
      CausalExactlyIdentifies Qs hQ π := by
  exact negativeExactLabelDeficiency_maximizer_iff
    (causalPathExperiment Qs hQ) (isProbabilityMeasure_causalPathExperiment' Qs hQ)
    ((causalFullRevelationAttainable_iff_exactlyIdentifies Qs hQ).1 hattain) π

/-- The precise argmax statement for item 3 of the attained-top objective
theorem: the maximizing policies are exactly the natively sufficient ones
under the stated full-revelation attainability hypothesis. -/
theorem causalFullRevelationObjective_argmax_eq_nativelySufficient
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hattain : CausalFullRevelationAttainable Qs hQ) :
    {π | ∀ σ, causalFullRevelationObjective Qs hQ σ ≤ causalFullRevelationObjective Qs hQ π} =
      {π | CausalNativelySufficient Qs π} := by
  ext π
  exact (causalFullRevelationObjective_maximizer_iff_exactlyIdentifies Qs hQ hattain π).trans
    (causalNativelySufficient_iff_exactlyIdentifies_of_attainable Qs hQ hattain π).symm

/-- Every finite-class policy has prefix-continuous full-revelation
deficiency, including policies whose terminal error is strictly positive. -/
theorem causalPrefix_labelDeficiency_tendsto_terminal
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) :
    Tendsto (fun t => finiteDeficiency (causalFiniteExperiment π.1 Qs t)
      (finiteLabelExperiment Θ)) atTop
      (𝓝 (finiteMeasureDeficiency (causalPathExperiment Qs hQ π) (exactLabelExperiment Θ))) := by
  have hP := isProbabilityMeasure_causalPathExperiment' Qs hQ π
  have hL := isProbabilityMeasure_exactLabelExperiment (Θ := Θ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (show Tendsto
      (fun t => finiteMeasureDeficiency (causalTraceMeasureExperiment Qs hQ π t)
        (causalPathExperiment Qs hQ π) +
          finiteMeasureDeficiency (causalPathExperiment Qs hQ π) (exactLabelExperiment Θ))
      atTop (𝓝 _) from by
        simpa using (tendsto_causalPrefixDeficiency Qs hQ π).add_const
          (finiteMeasureDeficiency (causalPathExperiment Qs hQ π) (exactLabelExperiment Θ)))
  · intro t
    simpa only [finiteMeasureDeficiency_causalTrace_exactLabel_eq_finiteLabel] using
      finiteMeasureDeficiency_path_le_trace Qs hQ π t (exactLabelExperiment Θ) hL
  · intro t
    simpa only [finiteMeasureDeficiency_causalTrace_exactLabel_eq_finiteLabel] using
      finiteMeasureDeficiency_triangle_of_prob
        (causalTraceMeasureExperiment Qs hQ π t) (causalPathExperiment Qs hQ π)
        (exactLabelExperiment Θ)
        (isProbabilityMeasure_causalTraceMeasureExperiment' Qs hQ π t) hP hL

theorem causalPrefix_negativeLabelDeficiency_tendsto_objective
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) :
    Tendsto (fun t => -finiteDeficiency (causalFiniteExperiment π.1 Qs t)
      (finiteLabelExperiment Θ)) atTop (𝓝 (causalFullRevelationObjective Qs hQ π)) :=
  (causalPrefix_labelDeficiency_tendsto_terminal Qs hQ π).neg

end IdExp
