import Formal.FiniteBayes

/-!
# The calibrated terminal posterior

The posterior given the whole sample is a conditional class distribution.
This module proves its simplex, prior-mean, and certainty/calibration
properties on arbitrary measurable sample spaces. It needs no POMDP,
identifiability assumption, or finite-prefix representation.
-/

namespace IdExp

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

set_option linter.unusedSectionVars false

variable {Θ Ω : Type*} [Fintype Θ] [MeasurableSpace Θ]
  [MeasurableSingletonClass Θ] [mΩ : MeasurableSpace Ω]

/-- Posterior conditional on the entire sample, not on the hidden label.
The argument order gives the probability vector at a joint-space point. -/
noncomputable def finiteBayesLimitPosterior (α : Θ → ℝ) (μ : Θ → Measure Ω)
    (x : Θ × Ω) (θ : Θ) : ℝ :=
  ((finiteBayesJoint α μ)[finiteBayesClassInd θ |
    MeasurableSpace.comap (Prod.snd : Θ × Ω → Ω) mΩ]) x

theorem measurable_finiteBayesLimitPosterior (α : Θ → ℝ) (μ : Θ → Measure Ω) :
    Measurable (finiteBayesLimitPosterior α μ) := by
  apply measurable_pi_lambda
  intro θ
  exact (stronglyMeasurable_condExp.mono
    (measurable_iff_comap_le.1 measurable_snd)).measurable

theorem integrable_finiteBayesLimitPosterior (α : Θ → ℝ) (μ : Θ → Measure Ω)
    (θ : Θ) :
    Integrable (fun x => finiteBayesLimitPosterior α μ x θ) (finiteBayesJoint α μ) :=
  integrable_condExp

theorem sum_finiteBayesClassInd (x : Θ × Ω) :
    ∑ θ, finiteBayesClassInd θ x = 1 := by
  classical
  have hterm : ∀ θ, finiteBayesClassInd θ x = if x.1 = θ then 1 else 0 := by
    intro θ
    by_cases h : x.1 = θ
    · rw [if_pos h]
      exact Set.indicator_of_mem (s := Prod.fst ⁻¹' ({θ} : Set Θ)) h _
    · rw [if_neg h]
      exact Set.indicator_of_notMem (s := Prod.fst ⁻¹' ({θ} : Set Θ)) h _
  simp_rw [hterm]
  simp

theorem ae_sum_finiteBayesLimitPosterior (α : Θ → ℝ) (hα : IsDist α)
    (μ : Θ → Measure Ω) (hμ : ∀ θ, IsProbabilityMeasure (μ θ)) :
    ∀ᵐ x ∂finiteBayesJoint α μ, ∑ θ, finiteBayesLimitPosterior α μ x θ = 1 := by
  have := isProbabilityMeasure_finiteBayesJoint hα μ hμ
  let m := MeasurableSpace.comap (Prod.snd : Θ × Ω → Ω) mΩ
  have hm : m ≤ (Prod.instMeasurableSpace : MeasurableSpace (Θ × Ω)) :=
    measurable_iff_comap_le.1 measurable_snd
  have hsum := condExp_finsetSum (μ := finiteBayesJoint α μ)
    (s := (Finset.univ : Finset Θ)) (f := fun θ => finiteBayesClassInd (Ω := Ω) θ)
    (fun θ _ => integrable_finiteBayesClassInd _ θ) m
  have h1 : (∑ θ, finiteBayesClassInd (Ω := Ω) θ) =
      fun _ : Θ × Ω => (1 : ℝ) := by
    funext x
    rw [Finset.sum_apply]
    exact sum_finiteBayesClassInd x
  rw [h1, condExp_const hm] at hsum
  filter_upwards [hsum] with x hx
  simpa only [Finset.sum_apply, finiteBayesLimitPosterior, m] using hx.symm

theorem ae_isDist_finiteBayesLimitPosterior (α : Θ → ℝ) (hα : IsDist α)
    (μ : Θ → Measure Ω) (hμ : ∀ θ, IsProbabilityMeasure (μ θ)) :
    ∀ᵐ x ∂finiteBayesJoint α μ, IsDist (finiteBayesLimitPosterior α μ x) := by
  have hnonneg : ∀ θ, 0 ≤ᵐ[finiteBayesJoint α μ]
      (fun x => finiteBayesLimitPosterior α μ x θ) := by
    intro θ
    apply condExp_nonneg
    filter_upwards with x
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
  filter_upwards [ae_all_iff.2 hnonneg, ae_sum_finiteBayesLimitPosterior α hα μ hμ]
    with x hx hsum
  exact ⟨hx, hsum⟩

theorem finiteBayesJoint_class (α : Θ → ℝ) (μ : Θ → Measure Ω)
    (hμ : ∀ θ, IsProbabilityMeasure (μ θ)) (θ : Θ) :
    finiteBayesJoint α μ (Prod.fst ⁻¹' ({θ} : Set Θ)) = ENNReal.ofReal (α θ) := by
  classical
  have : ∀ θ, IsProbabilityMeasure (μ θ) := hμ
  rw [finiteBayesJoint_apply α μ (measurableSet_finiteBayesClass θ)]
  rw [Finset.sum_eq_single θ]
  · have heq : Prod.mk θ ⁻¹' (Prod.fst ⁻¹' ({θ} : Set Θ)) = (Set.univ : Set Ω) := by
      ext ω
      simp
    simp [heq]
  · intro η _ hη
    have heq : Prod.mk η ⁻¹' (Prod.fst ⁻¹' ({θ} : Set Θ)) = (∅ : Set Ω) := by
      ext ω
      simp [hη]
    simp [heq]
  · simp

/-- The posterior mean equals the prior, with no acquisition assumption. -/
theorem integral_finiteBayesLimitPosterior (α : Θ → ℝ) (hα : IsDist α)
    (μ : Θ → Measure Ω) (hμ : ∀ θ, IsProbabilityMeasure (μ θ)) (θ : Θ) :
    ∫ x, finiteBayesLimitPosterior α μ x θ ∂finiteBayesJoint α μ = α θ := by
  have := isProbabilityMeasure_finiteBayesJoint hα μ hμ
  have hm := measurable_iff_comap_le.1
    (measurable_snd : Measurable (Prod.snd : Θ × Ω → Ω))
  simp only [finiteBayesLimitPosterior]
  rw [integral_condExp hm, finiteBayesClassInd,
    integral_indicator (measurableSet_finiteBayesClass θ), setIntegral_const,
    smul_eq_mul, mul_one, Measure.real, finiteBayesJoint_class α μ hμ θ,
    ENNReal.toReal_ofReal (hα.1 θ)]

/-- Posterior certainty about a label is almost surely correct. -/
theorem ae_class_eq_of_finiteBayesLimitPosterior_one
    (α : Θ → ℝ) (hα : IsDist α) (μ : Θ → Measure Ω)
    (hμ : ∀ θ, IsProbabilityMeasure (μ θ)) (θ : Θ) :
    ∀ᵐ x ∂finiteBayesJoint α μ,
      finiteBayesLimitPosterior α μ x θ = 1 → x.1 = θ := by
  have := isProbabilityMeasure_finiteBayesJoint hα μ hμ
  let m := MeasurableSpace.comap (Prod.snd : Θ × Ω → Ω) mΩ
  have hm : m ≤ (Prod.instMeasurableSpace : MeasurableSpace (Θ × Ω)) :=
    measurable_iff_comap_le.1 measurable_snd
  let S : Set (Θ × Ω) := {x | finiteBayesLimitPosterior α μ x θ = 1}
  have hSm : MeasurableSet[m] S :=
    stronglyMeasurable_condExp.measurable (measurableSet_singleton (1 : ℝ))
  have hS : @MeasurableSet (Θ × Ω) Prod.instMeasurableSpace S := hm _ hSm
  have hind := integrable_finiteBayesClassInd (finiteBayesJoint α μ) θ
  have hkey : ∫ x in S, finiteBayesLimitPosterior α μ x θ ∂finiteBayesJoint α μ =
      ∫ x in S, finiteBayesClassInd θ x ∂finiteBayesJoint α μ :=
    setIntegral_condExp hm hind hSm
  have hzero : ∫ x in S, (1 - finiteBayesClassInd θ x) ∂finiteBayesJoint α μ = 0 := by
    rw [integral_sub (integrable_const 1) hind.integrableOn, ← hkey]
    rw [setIntegral_congr_fun hS (fun x (hx : finiteBayesLimitPosterior α μ x θ = 1) => hx)]
    exact sub_self _
  have hnonneg : 0 ≤ᵐ[(finiteBayesJoint α μ).restrict S]
      (fun x => 1 - finiteBayesClassInd θ x) := by
    filter_upwards with x
    by_cases hx : x.1 = θ
    · rw [show finiteBayesClassInd θ x = 1 from
        Set.indicator_of_mem (s := Prod.fst ⁻¹' ({θ} : Set Θ)) hx _]
      norm_num
    · rw [show finiteBayesClassInd θ x = 0 from
        Set.indicator_of_notMem (s := Prod.fst ⁻¹' ({θ} : Set Θ)) hx _]
      norm_num
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnonneg
    ((integrable_const 1).sub hind).integrableOn).1 hzero
  have hae' := (ae_restrict_iff' hS).1 hae
  filter_upwards [hae'] with x hx hpost
  have heq := hx hpost
  by_contra hne
  rw [show finiteBayesClassInd θ x = 0 from
    Set.indicator_of_notMem (s := Prod.fst ⁻¹' ({θ} : Set Θ)) hne _] at heq
  norm_num at heq

end IdExp
