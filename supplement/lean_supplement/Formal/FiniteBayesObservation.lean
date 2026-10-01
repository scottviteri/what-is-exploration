import Formal.FiniteBayes
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Integrating statistics of finite observations

An arbitrary function of a finite measurable observation is integrable under
a finite measure. On a finite-prior joint experiment its integral is exactly
the mixture-weighted finite sum. Observed atoms have positive mixture mass
almost surely, even when some prior weights vanish.
-/

namespace IdExp

open MeasureTheory Set
open scoped ENNReal

variable {Θ S Ω : Type*} [Fintype Θ] [Fintype S]
  [MeasurableSpace Θ] [MeasurableSingletonClass Θ]
  [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace Ω]

theorem integrable_comp_finiteObservation (μ : Measure Ω) [IsFiniteMeasure μ]
    (p : Ω → S) (hp : Measurable p) (g : S → ℝ) :
    Integrable (fun ω => g (p ω)) μ :=
  (Integrable.of_finite (μ := μ.map p) (f := g)).comp_measurable hp

theorem integral_comp_finiteObservation (μ : Measure Ω) [IsFiniteMeasure μ]
    (p : Ω → S) (hp : Measurable p) (g : S → ℝ) :
    ∫ ω, g (p ω) ∂μ = ∑ s, (μ (p ⁻¹' {s})).toReal * g s := by
  rw [← integral_map hp.aemeasurable (measurable_of_finite g).aestronglyMeasurable,
    integral_fintype Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro s _
  simp [Measure.real, Measure.map_apply hp (measurableSet_singleton s), smul_eq_mul]

theorem integral_finiteBayesObservation (α : Θ → ℝ) (hα : IsDist α)
    (μ : Θ → Measure Ω) (hμ : ∀ θ, IsProbabilityMeasure (μ θ))
    (p : Ω → S) (hp : Measurable p) (E : Θ → S → ℝ)
    (hE : ∀ θ s, 0 ≤ E θ s)
    (hmass : ∀ θ s, μ θ (p ⁻¹' {s}) = ENNReal.ofReal (E θ s)) (g : S → ℝ) :
    ∫ x : Θ × Ω, g (p x.2) ∂finiteBayesJoint α μ =
      ∑ s, finiteBayesMass α E s * g s := by
  letI := isProbabilityMeasure_finiteBayesJoint hα μ hμ
  rw [integral_comp_finiteObservation (finiteBayesJoint α μ)
    (fun x : Θ × Ω => p x.2) (hp.comp measurable_snd) g]
  apply Finset.sum_congr rfl
  intro s _
  rw [finiteBayesJoint_atom α μ p hp E hα.1 hE hmass]
  change (ENNReal.ofReal (finiteBayesMass α E s)).toReal * g s = _
  rw [ENNReal.toReal_ofReal (finiteBayesMass_nonneg α E hα.1 hE s)]

theorem ae_finiteBayesObservation_mass_pos (α : Θ → ℝ)
    (μ : Θ → Measure Ω) (p : Ω → S) (hp : Measurable p) (E : Θ → S → ℝ)
    (hα : ∀ θ, 0 ≤ α θ) (hE : ∀ θ s, 0 ≤ E θ s)
    (hmass : ∀ θ s, μ θ (p ⁻¹' {s}) = ENNReal.ofReal (E θ s)) :
    ∀ᵐ x : Θ × Ω ∂finiteBayesJoint α μ, 0 < finiteBayesMass α E (p x.2) := by
  have hall : ∀ s, ∀ᵐ x : Θ × Ω ∂finiteBayesJoint α μ,
      p x.2 = s → 0 < finiteBayesMass α E s := by
    intro s
    by_cases hs : 0 < finiteBayesMass α E s
    · exact Filter.Eventually.of_forall fun _ _ => hs
    · have hz : finiteBayesMass α E s = 0 :=
        le_antisymm (le_of_not_gt hs) (finiteBayesMass_nonneg α E hα hE s)
      have hnull : finiteBayesJoint α μ ((fun x : Θ × Ω => p x.2) ⁻¹' {s}) = 0 := by
        rw [finiteBayesJoint_atom α μ p hp E hα hE hmass]
        change ENNReal.ofReal (finiteBayesMass α E s) = 0
        simp [hz]
      have hae : ∀ᵐ x : Θ × Ω ∂finiteBayesJoint α μ,
          x ∉ ((fun x : Θ × Ω => p x.2) ⁻¹' {s}) := by
        apply ae_iff.2
        simpa only [not_not, Set.ofPred_mem_eq] using hnull
      filter_upwards [hae] with x hx
      exact fun heq => False.elim (hx heq)
  filter_upwards [ae_all_iff.2 hall] with x hx
  exact hx (p x.2) rfl

end IdExp
