import Formal.PosteriorGarblingStrict
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Actual priors instantiate infinite-world strict posterior comparison

Predictive masses are literal integrals under the prior. Posterior functions
are likelihood-ratio densities, with the prior itself used at null signals.
Null-signal factorization is discharged either by positive mass at every
singleton, or by continuous likelihoods and full topological support.
No finite or countable world assumption is imposed on the continuity route.
-/

set_option maxHeartbeats 1000000

namespace IdExp

open MeasureTheory Finset Set

variable {Θ X Y : Type*} [MeasurableSpace Θ] [Fintype X] [Fintype Y]

noncomputable def priorSignalMass (μ : Measure Θ) (E : FiniteExperiment Θ X) (x : X) : ℝ :=
  ∫ θ, E θ x ∂μ

noncomputable def priorSignalDensity (μ : Measure Θ) (E : FiniteExperiment Θ X)
    (x : X) (θ : Θ) : ℝ :=
  if priorSignalMass μ E x = 0 then 1 else E θ x / priorSignalMass μ E x

noncomputable def priorSignalPotential (μ : Measure Θ) (E : FiniteExperiment Θ X)
    (Φ : (Θ → ℝ) → ℝ) : ℝ :=
  ∑ x, priorSignalMass μ E x * Φ (priorSignalDensity μ E x)

/-- Predictive masses are a probability vector for a genuine prior and
integrable finite experiment. -/
theorem priorSignalMass_isDist (μ : Measure Θ) [IsProbabilityMeasure μ]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (hi : ∀ x, Integrable (fun θ => E θ x) μ) : IsDist (priorSignalMass μ E) := by
  constructor
  · intro x
    exact integral_nonneg fun θ => (hE θ).1 x
  · unfold priorSignalMass
    rw [← integral_finsetSum _ (fun x _ => hi x)]
    simp only [(hE _).2]
    simp

/-- Every signal posterior is an integrable unit-mass density, with the
prior itself assigned to a null signal. -/
theorem priorSignalDensity_integral_one (μ : Measure Θ) [IsProbabilityMeasure μ]
    (E : FiniteExperiment Θ X) (x : X) :
    ∫ θ, priorSignalDensity μ E x θ ∂μ = 1 := by
  by_cases hx : priorSignalMass μ E x = 0
  · simp [priorSignalDensity, hx]
  · simp only [priorSignalDensity, if_neg hx]
    rw [integral_div]
    exact div_self hx

theorem priorSignalDensity_integrable (μ : Measure Θ) [IsProbabilityMeasure μ]
    (E : FiniteExperiment Θ X) (hi : ∀ x, Integrable (fun θ => E θ x) μ) (x : X) :
    Integrable (priorSignalDensity μ E x) μ := by
  change Integrable (fun θ => if priorSignalMass μ E x = 0 then 1 else E θ x / priorSignalMass μ E x) μ
  by_cases hx : priorSignalMass μ E x = 0
  · simpa [hx] using (integrable_const (1 : ℝ) : Integrable (fun _ : Θ => (1 : ℝ)) μ)
  · simpa [hx] using (hi x).div_const (priorSignalMass μ E x)

theorem priorSignalDensity_nonneg (μ : Measure Θ) (E : FiniteExperiment Θ X)
    (hE : IsFiniteExperiment E) (x : X) (θ : Θ) : 0 ≤ priorSignalDensity μ E x θ := by
  unfold priorSignalDensity
  split_ifs
  · exact zero_le_one
  · exact div_nonneg ((hE θ).1 x) (integral_nonneg fun η => (hE η).1 x)

/-- A posterior density system under a prior whose null signals are null
at every world. The following theorems discharge that condition. -/
noncomputable def priorSignalSystem (μ : Measure Θ) [IsProbabilityMeasure μ]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (hi : ∀ x, Integrable (fun θ => E θ x) μ)
    (hz : ∀ x, priorSignalMass μ E x = 0 → ∀ θ, E θ x = 0) :
    SignalPosteriorSystem E where
  mass := priorSignalMass μ E
  mass_dist := priorSignalMass_isDist μ E hE hi
  density := priorSignalDensity μ E
  factor := by
    intro x θ
    by_cases hx : priorSignalMass μ E x = 0
    · simp [priorSignalDensity, hx, hz x hx θ]
    · simp only [priorSignalDensity, if_neg hx]
      field_simp

/-- An atomwise full-support prior sees every nonzero finite signal.
No finite-world assumption is needed. -/
theorem priorSignalMass_zero_of_positive_atoms
    (μ : Measure Θ) (hμ : ∀ θ, 0 < μ {θ})
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (hi : ∀ x, Integrable (fun θ => E θ x) μ)
    (x : X) (hx : priorSignalMass μ E x = 0) (θ : Θ) : E θ x = 0 := by
  have hae : (fun θ => E θ x) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun θ => (hE θ).1 x) (hi x)).mp hx
  have hn : μ {η | ¬ E η x = 0} = 0 := by simpa using ae_iff.mp hae
  by_contra he
  have hs : ({θ} : Set Θ) ⊆ {η | ¬ E η x = 0} := by
    intro η hη
    obtain rfl := Set.mem_singleton_iff.mp hη
    exact he
  have hle := measure_mono (μ := μ) hs
  rw [hn] at hle
  exact (not_le_of_gt (hμ θ)) hle

/-- Continuous finite probability coordinates are integrable under any
finite prior measure. -/
theorem integrable_finiteExperiment_coordinate
    [TopologicalSpace Θ] [OpensMeasurableSpace Θ]
    (μ : Measure Θ) [IsFiniteMeasure μ]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (hc : ∀ x, Continuous (fun θ => E θ x)) (x : X) :
    Integrable (fun θ => E θ x) μ := by
  apply (integrable_const (1 : ℝ)).mono' (hc x).measurable.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro θ
  rw [Real.norm_eq_abs, abs_of_nonneg ((hE θ).1 x)]
  have hs := Finset.single_le_sum (fun z _ => (hE θ).1 z) (mem_univ x)
  exact hs.trans_eq (hE θ).2

/-- Full topological support upgrades a zero integral to zero in every
world for continuous nonnegative finite likelihoods. -/
theorem priorSignalMass_zero_of_continuous
    [TopologicalSpace Θ] [OpensMeasurableSpace Θ]
    (μ : Measure Θ) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (hc : ∀ x, Continuous (fun θ => E θ x))
    (x : X) (hx : priorSignalMass μ E x = 0) (θ : Θ) : E θ x = 0 := by
  by_contra hne
  have hp := integral_pos_of_integrable_nonneg_nonzero (hc x)
    (integrable_finiteExperiment_coordinate μ E hE hc x)
    (fun θ => (hE θ).1 x) hne
  exact (ne_of_gt hp) hx

/-- A common garbling also garbles the literal prior-predictive masses. -/
theorem priorSignalMass_garbling
    (μ : Measure Θ) (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hi : ∀ x, Integrable (fun θ => E θ x) μ)
    (G : X → Y → ℝ) (hGF : finiteDecisionLaw E G = F) (y : Y) :
    ∑ x, priorSignalMass μ E x * G x y = priorSignalMass μ F y := by
  unfold priorSignalMass
  calc _ = ∑ x, ∫ θ, E θ x * G x y ∂μ := by simp_rw [integral_mul_const]
    _ = ∫ θ, ∑ x, E θ x * G x y ∂μ :=
      (integral_finsetSum _ (fun x _ => (hi x).mul_const _)).symm
    _ = _ := by rw [show (fun θ => ∑ x, E θ x * G x y) = (fun θ => F θ y) by
                      funext θ; exact congrFun (congrFun hGF θ) y]

/-- Infinite-world strict posterior-potential comparison under a continuous
finite experiment and a full-support prior. The potential acts on the actual
posterior densities relative to that prior. Null densities are the constant
one, so its convex domain can be a domain of probability densities. -/
theorem continuous_priorSignalPotential_lt_of_no_reverse
    [TopologicalSpace Θ] [OpensMeasurableSpace Θ] [Nonempty X]
    (μ : Measure Θ) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (hcE : ∀ x, Continuous (fun θ => E θ x))
    (hcF : ∀ y, Continuous (fun θ => F θ y))
    (G : X → Y → ℝ) (hG : G ∈ stochasticRules X Y)
    (hGF : finiteDecisionLaw E G = F)
    (Φ : (Θ → ℝ) → ℝ) (C : Set (Θ → ℝ)) (hΦ : StrictConvexOn ℝ C Φ)
    (hP : ∀ x, priorSignalDensity μ E x ∈ C)
    (hnot : ¬ ∃ R ∈ stochasticRules Y X, finiteDecisionLaw F R = E) :
    priorSignalPotential μ F Φ < priorSignalPotential μ E Φ := by
  let P := priorSignalSystem μ E hE (integrable_finiteExperiment_coordinate μ E hE hcE)
    (priorSignalMass_zero_of_continuous μ E hE hcE)
  let Q := priorSignalSystem μ F hF (integrable_finiteExperiment_coordinate μ F hF hcF)
    (priorSignalMass_zero_of_continuous μ F hF hcF)
  exact signalPosterior_potential_lt_of_no_reverse P Q G hG hGF
    (priorSignalMass_garbling μ E F (integrable_finiteExperiment_coordinate μ E hE hcE) G hGF)
    Φ C hΦ hP hnot

/-- The same strict conclusion for an atomwise full-support prior, including
countably infinite classes, with integrability stated explicitly. -/
theorem atomic_priorSignalPotential_lt_of_no_reverse
    [Nonempty X] (μ : Measure Θ) [IsProbabilityMeasure μ]
    (hμ : ∀ θ, 0 < μ {θ})
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (hiE : ∀ x, Integrable (fun θ => E θ x) μ)
    (hiF : ∀ y, Integrable (fun θ => F θ y) μ)
    (G : X → Y → ℝ) (hG : G ∈ stochasticRules X Y)
    (hGF : finiteDecisionLaw E G = F)
    (Φ : (Θ → ℝ) → ℝ) (C : Set (Θ → ℝ)) (hΦ : StrictConvexOn ℝ C Φ)
    (hP : ∀ x, priorSignalDensity μ E x ∈ C)
    (hnot : ¬ ∃ R ∈ stochasticRules Y X, finiteDecisionLaw F R = E) :
    priorSignalPotential μ F Φ < priorSignalPotential μ E Φ := by
  let P := priorSignalSystem μ E hE hiE (priorSignalMass_zero_of_positive_atoms μ hμ E hE hiE)
  let Q := priorSignalSystem μ F hF hiF (priorSignalMass_zero_of_positive_atoms μ hμ F hF hiF)
  exact signalPosterior_potential_lt_of_no_reverse P Q G hG hGF
    (priorSignalMass_garbling μ E F hiE G hGF) Φ C hΦ hP hnot

end IdExp
