import Formal.PulseBrierScore
import Formal.InfinitePosteriorKL
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Actual countable Bayes posterior behind the pulse Brier optimum

The finite-signal full-label Brier reporting optimum is exactly the expected
unweighted sum of squared singleton masses of the actual Bayes posterior.
Consequently the complete prefix-potential gain has a globally maximizing WAIT
policy strictly finitarily dominated by QUERY, under the full-support geometric
prior. `PulseBrierMovement` supplies the squared-posterior-movement series identity.
-/

namespace IdExp

open MeasureTheory Finset Set Filter Topology
noncomputable section

namespace FullLabelBrierReport

variable {Θ : Type*} [Countable Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ]

/-- Every countable probability measure gives its full-label probability report. -/
def ofMeasure (μ : Measure Θ) [IsProbabilityMeasure μ] : FullLabelBrierReport Θ where
  probability θ := μ.real {θ}
  nonneg _ := measureReal_nonneg
  summable := by
    apply summable_of_sum_le (fun θ => (measureReal_nonneg : 0 ≤ μ.real {θ}))
      (c := (1 : ℝ))
    intro s
    rw [sum_measureReal_singleton]
    exact measureReal_le_one
  sum_one := by
    have h := integral_countable (integrable_const (1 : ℝ) (μ := μ))
    simpa [smul_eq_mul] using h.symm

end FullLabelBrierReport

namespace PulseBrierScore

variable {S : Type*} [Fintype S]

theorem coordinate_le_one (E : FiniteExperiment World S) (hE : IsFiniteExperiment E)
    (θ : World) (s : S) : E θ s ≤ 1 := by
  have h := Finset.single_le_sum (fun x _ => (hE θ).1 x) (Finset.mem_univ s)
  rwa [(hE θ).2] at h

theorem likelihood_integrable (E : FiniteExperiment World S) (hE : IsFiniteExperiment E)
    (s : S) : Integrable (fun θ => E θ s) prior := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
  exact Eventually.of_forall fun θ => by
    rw [Real.norm_eq_abs, abs_of_nonneg ((hE θ).1 s)]
    exact coordinate_le_one E hE θ s

theorem prior_positive_atoms (θ : World) : 0 < prior {θ} := by
  have hr : 0 < prior.real {θ} := by
    cases θ with
    | none => rw [waitingQueryGeometricPrior_none]; norm_num
    | some k => rw [waitingQueryGeometricPrior_some]; positivity
  exact (ENNReal.toReal_pos_iff.mp hr).1

/-- The actual Bayes posterior, with the existing prior-at-null convention. -/
def posteriorReport (E : FiniteExperiment World S) (hE : IsFiniteExperiment E)
    (s : S) : Report := by
  letI := priorPosteriorMeasure_probability prior E hE (likelihood_integrable E hE) s
  exact FullLabelBrierReport.ofMeasure (priorPosteriorMeasure prior E s)

theorem posteriorReport_apply (E : FiniteExperiment World S) (hE : IsFiniteExperiment E)
    (s : S) (θ : World) :
    posteriorReport E hE s θ = priorSignalDensity prior E s θ * prior.real {θ} := by
  change (priorPosteriorMeasure prior E s).real {θ} = _
  rw [measureReal_def, priorPosteriorMeasure,
    withDensity_apply _ (measurableSet_singleton θ), lintegral_singleton,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (priorSignalDensity_nonneg prior E hE s θ)]
  rfl

/-- Explicit Bayes formula away from null records, on all countably many labels. -/
theorem posteriorReport_bayes (E : FiniteExperiment World S) (hE : IsFiniteExperiment E)
    (s : S) (hs : priorSignalMass prior E s ≠ 0) (θ : World) :
    posteriorReport E hE s θ = prior.real {θ} * E θ s / priorSignalMass prior E s := by
  rw [posteriorReport_apply]
  simp only [priorSignalDensity, if_neg hs]
  ring

theorem likelihood_score_integrable (E : FiniteExperiment World S) (hE : IsFiniteExperiment E)
    (s : S) (q : Report) : Integrable (fun θ => E θ s * q.score θ) prior := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
  apply Eventually.of_forall
  intro θ
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ((hE θ).1 s)]
  calc E θ s * |q.score θ| ≤ E θ s * 1 :=
        mul_le_mul_of_nonneg_left (abs_le.mpr (q.score_bounds θ)) ((hE θ).1 s)
    _ ≤ 1 := by simpa using coordinate_le_one E hE θ s

/-- Integrating a report against a likelihood equals its actual posterior average. -/
theorem likelihood_score_posterior (E : FiniteExperiment World S) (hE : IsFiniteExperiment E)
    (s : S) (q : Report) :
    (∫ θ, E θ s * q.score θ ∂prior) =
      priorSignalMass prior E s * (∑' θ, posteriorReport E hE s θ * q.score θ) := by
  rw [integral_countable (likelihood_score_integrable E hE s q), ← tsum_mul_left]
  apply tsum_congr
  intro θ
  simp only [smul_eq_mul]
  by_cases hs : priorSignalMass prior E s = 0
  · have hz := priorSignalMass_zero_of_positive_atoms prior prior_positive_atoms E hE
      (likelihood_integrable E hE) s hs θ
    simp [hs, hz]
  · rw [posteriorReport_bayes E hE s hs]
    field_simp

/-- The actual expected full-label posterior quadratic potential. -/
def posteriorPotential (E : FiniteExperiment World S) (hE : IsFiniteExperiment E) : ℝ :=
  ∑ s, priorSignalMass prior E s * (posteriorReport E hE s).potential

theorem ruleValue_posterior_identity (E : FiniteExperiment World S)
    (hE : IsFiniteExperiment E) (r : S → Report) :
    ruleValue E r = posteriorPotential E hE -
      ∑ s, priorSignalMass prior E s *
        ∑' θ, (posteriorReport E hE s θ - r s θ) ^ 2 := by
  unfold ruleValue rulePayoff
  rw [integral_finsetSum _ (fun s _ => likelihood_score_integrable E hE s (r s))]
  simp_rw [likelihood_score_posterior E hE,
    FullLabelBrierReport.proper_identity, mul_sub]
  rw [Finset.sum_sub_distrib]
  rfl

/-- Reporting the actual posterior attains the maximum over all reports. -/
theorem posteriorReport_value (E : FiniteExperiment World S) (hE : IsFiniteExperiment E) :
    ruleValue E (posteriorReport E hE) = posteriorPotential E hE := by
  rw [ruleValue_posterior_identity E hE]
  simp

/-- Complete equality between the full-label scoring optimum and Bayes potential. -/
theorem experimentScore_eq_posteriorPotential (E : FiniteExperiment World S)
    (hE : IsFiniteExperiment E) : experimentScore E = posteriorPotential E hE := by
  apply le_antisymm
  · have : Nonempty (S → Report) := ⟨fun _ => FullLabelBrierReport.point none⟩
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨r, rfl⟩
    rw [ruleValue_posterior_identity E hE]
    have hn : 0 ≤ ∑ s, priorSignalMass prior E s *
        ∑' θ, (posteriorReport E hE s θ - r s θ) ^ 2 :=
      Finset.sum_nonneg fun s _ =>
        mul_nonneg ((priorSignalMass_isDist prior E hE (likelihood_integrable E hE)).1 s)
          (tsum_nonneg fun θ => sq_nonneg _)
    linarith
  · rw [← posteriorReport_value E hE]
    exact ruleValue_le_experimentScore E hE _

/-- Ordinary full-label prior collision probability; no feature weights occur. -/
def priorPotential : ℝ := (FullLabelBrierReport.ofMeasure prior).potential

/-- Complete full-posterior quadratic gain, using actual causal finite records. -/
def completePosteriorGain (π : ValidCausalPolicy Bool Bool) : ℝ :=
  (sSup (Set.range (fun t => posteriorPotential
    (causalBehaviorFiniteExperiment π.1 pulseBehavior t)
    (causalBehaviorFiniteExperiment_valid π.1 π.2 pulseBehavior t)))) - priorPotential

theorem completePosteriorGain_eq (π : ValidCausalPolicy Bool Bool) :
    completePosteriorGain π = completeScore π - priorPotential := by
  have he : (fun t => posteriorPotential
      (causalBehaviorFiniteExperiment π.1 pulseBehavior t)
      (causalBehaviorFiniteExperiment_valid π.1 π.2 pulseBehavior t)) = prefixScore π := by
    funext t
    exact (experimentScore_eq_posteriorPotential _
      (causalBehaviorFiniteExperiment_valid π.1 π.2 pulseBehavior t)).symm
  unfold completePosteriorGain
  rw [he]
  rfl

/-- A globally optimal complete full-label posterior Brier gain with a feasible
strict improvement in the actual finite-prefix process order. -/
theorem posterior_gain_dominated_maximizer :
    (∀ π : ValidCausalPolicy Bool Bool,
      completePosteriorGain π ≤ completePosteriorGain (pulsePolicy false)) ∧
    CausalBehaviorFinitaryDominates pulseBehavior (pulsePolicy true) (pulsePolicy false) ∧
      ¬ CausalBehaviorFinitaryDominates pulseBehavior (pulsePolicy false) (pulsePolicy true) := by
  refine ⟨?_, pulse_query_strictly_dominates_wait⟩
  intro π
  simp only [completePosteriorGain_eq]
  exact sub_le_sub_right (dominated_maximizer.1 π) priorPotential

end PulseBrierScore
end
end IdExp
