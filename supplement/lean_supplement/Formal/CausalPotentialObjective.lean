import Formal.CausalPosteriorLimit
import Formal.PosteriorPotentialLimit

/-!
# Exact maxima of strictly convex causal posterior potentials

The objective uses the literal terminal posterior of the actual causal path
experiment. Its measurability, simplex membership, and prior mean are proved
properties, not input assumptions. Strict convexity makes equality with the
full-revelation bound equivalent to an almost-sure posterior vertex;
calibration and the causal posterior convergence theorem identify these
vertices with almost-sure class recovery.

Attainability is needed only to characterize global maximizing policies, not
to characterize equality with the full-revelation bound for one policy.
Continuity and strict convexity are required only on the class simplex.
-/

namespace IdExp

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

set_option linter.unusedSectionVars false

variable {Θ : Type*} [Fintype Θ] [DecidableEq Θ]

/-- A probability vector assigning mass one to a coordinate is that vertex. -/
theorem isDist_eq_single_of_eq_one {p : Θ → ℝ} (hp : IsDist p)
    {θ : Θ} (hθ : p θ = 1) : p = Pi.single θ 1 := by
  classical
  have hrest : ∑ η ∈ Finset.univ.erase θ, p η = 0 := by
    have hsum := Finset.sum_erase_add (Finset.univ (α := Θ)) p (Finset.mem_univ θ)
    rw [hp.2, hθ] at hsum
    linarith
  funext η
  by_cases hη : η = θ
  · subst η
    simpa using hθ
  · have hz : p η = 0 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun c _ => hp.1 c)).1 hrest η (Finset.mem_erase.mpr ⟨hη, Finset.mem_univ η⟩)
    simp [Pi.single_eq_of_ne hη, hz]

variable [Nonempty Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ]
  {A O : Type*} [Fintype A] [Fintype O] [Nonempty A] [Nonempty O]
  [MeasurableSpace A] [MeasurableSpace O]
  [MeasurableSingletonClass A] [MeasurableSingletonClass O]

/-- The Bayesian terminal vector is a vertex a.s. exactly when the actual
causal path identifies the world. The prior has full support; no assumption
that another policy can identify is made. -/
theorem ae_causalLimitPosterior_vertex_iff_exactlyIdentifies
    (α : Θ → ℝ) (hα : IsDist α) (hfs : FullSupport α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) :
    (∀ᵐ x ∂causalBayesJoint α Qs hQ π,
      ∃ θ, causalLimitPosterior α Qs hQ π x = Pi.single θ 1) ↔
        CausalExactlyIdentifies Qs hQ π := by
  have hlim := causalPosterior_tendsto_limit α hα Qs hQ π
  constructor
  · intro hv
    apply (causalPosteriorConcentrates_iff_exactlyIdentifies α hα hfs Qs hQ π).1
    apply (causalPosteriorConcentrates_iff_joint α hfs Qs hQ π).2
    have hcal : ∀ᵐ x ∂causalBayesJoint α Qs hQ π, ∀ θ,
        causalLimitPosterior α Qs hQ π x θ = 1 → x.1 = θ := by
      apply ae_all_iff.2
      intro θ
      exact ae_class_eq_of_finiteBayesLimitPosterior_one α hα _
        (isProbabilityMeasure_causalPathExperiment' Qs hQ π) θ
    filter_upwards [hv, hlim, hcal] with x hxv hxlim hxcal
    obtain ⟨θ, hθ⟩ := hxv
    have hone : causalLimitPosterior α Qs hQ π x θ = 1 := by simp [hθ]
    have htruth := hxcal θ hone
    have ht := (tendsto_pi_nhds.1 hxlim) x.1
    simpa only [htruth, hone] using ht
  · intro hid
    have hconc := (causalPosteriorConcentrates_iff_joint α hfs Qs hQ π).1
      ((causalPosteriorConcentrates_iff_exactlyIdentifies α hα hfs Qs hQ π).2 hid)
    have hdist := ae_isDist_finiteBayesLimitPosterior α hα _
      (isProbabilityMeasure_causalPathExperiment' Qs hQ π)
    filter_upwards [hlim, hconc, hdist] with x hxlim hxconc hxdist
    have hone : causalLimitPosterior α Qs hQ π x x.1 = 1 :=
      tendsto_nhds_unique ((tendsto_pi_nhds.1 hxlim) x.1) hxconc
    exact ⟨x.1, isDist_eq_single_of_eq_one hxdist hone⟩

/-- Expected terminal potential of the actual causal posterior. -/
noncomputable def causalTerminalPotential (F : (Θ → ℝ) → ℝ) (α : Θ → ℝ)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) : ℝ :=
  ∫ x, F (causalLimitPosterior α Qs hQ π x) ∂causalBayesJoint α Qs hQ π

/-- Terminal potential gain over the initial prior, the objective obtained
by complete expected conservative posterior movement. -/
noncomputable def causalPotentialObjective (F : (Θ → ℝ) → ℝ) (α : Θ → ℝ)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) : ℝ :=
  causalTerminalPotential F α Qs hQ π - F α

theorem causalTerminalPotential_le_full
    (F : (Θ → ℝ) → ℝ) (hF : ContinuousOn F (stdSimplex ℝ Θ))
    (hconvex : ConvexOn ℝ (stdSimplex ℝ Θ) F)
    (α : Θ → ℝ) (hα : IsDist α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) :
    causalTerminalPotential F α Qs hQ π ≤ ∑ θ, α θ * F (Pi.single θ 1) := by
  have : IsProbabilityMeasure (causalBayesJoint α Qs hQ π) :=
    isProbabilityMeasure_finiteBayesJoint hα _
    (isProbabilityMeasure_causalPathExperiment' Qs hQ π)
  exact integral_posteriorPotential_le_full (causalBayesJoint α Qs hQ π)
    F hF hconvex (causalLimitPosterior α Qs hQ π)
    (measurable_finiteBayesLimitPosterior α _).aemeasurable
    (ae_causalLimitPosterior_mem_simplex α hα Qs hQ π) α
    (integral_finiteBayesLimitPosterior α hα _
      (isProbabilityMeasure_causalPathExperiment' Qs hQ π))

theorem causalTerminalPotential_eq_full_iff_exactlyIdentifies
    (F : (Θ → ℝ) → ℝ) (hF : ContinuousOn F (stdSimplex ℝ Θ))
    (hstrict : StrictConvexOn ℝ (stdSimplex ℝ Θ) F)
    (α : Θ → ℝ) (hα : IsDist α) (hfs : FullSupport α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) :
    causalTerminalPotential F α Qs hQ π = (∑ θ, α θ * F (Pi.single θ 1)) ↔
      CausalExactlyIdentifies Qs hQ π := by
  have : IsProbabilityMeasure (causalBayesJoint α Qs hQ π) :=
    isProbabilityMeasure_finiteBayesJoint hα _
    (isProbabilityMeasure_causalPathExperiment' Qs hQ π)
  exact (integral_posteriorPotential_eq_full_iff (causalBayesJoint α Qs hQ π)
    F hF hstrict (causalLimitPosterior α Qs hQ π)
    (measurable_finiteBayesLimitPosterior α _).aemeasurable
    (ae_causalLimitPosterior_mem_simplex α hα Qs hQ π) α
    (integral_finiteBayesLimitPosterior α hα _
      (isProbabilityMeasure_causalPathExperiment' Qs hQ π))).trans
      (ae_causalLimitPosterior_vertex_iff_exactlyIdentifies α hα hfs Qs hQ π)

theorem causalPotentialObjective_le_full
    (F : (Θ → ℝ) → ℝ) (hF : ContinuousOn F (stdSimplex ℝ Θ))
    (hconvex : ConvexOn ℝ (stdSimplex ℝ Θ) F)
    (α : Θ → ℝ) (hα : IsDist α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) :
    causalPotentialObjective F α Qs hQ π ≤ (∑ θ, α θ * F (Pi.single θ 1)) - F α :=
  sub_le_sub_right (causalTerminalPotential_le_full F hF hconvex α hα Qs hQ π) _

theorem causalPotentialObjective_eq_full_iff_exactlyIdentifies
    (F : (Θ → ℝ) → ℝ) (hF : ContinuousOn F (stdSimplex ℝ Θ))
    (hstrict : StrictConvexOn ℝ (stdSimplex ℝ Θ) F)
    (α : Θ → ℝ) (hα : IsDist α) (hfs : FullSupport α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) :
    causalPotentialObjective F α Qs hQ π =
        (∑ θ, α θ * F (Pi.single θ 1)) - F α ↔ CausalExactlyIdentifies Qs hQ π := by
  rw [causalPotentialObjective, sub_left_inj]
  exact causalTerminalPotential_eq_full_iff_exactlyIdentifies F hF hstrict α hα hfs Qs hQ π

/-- Attainability is exactly attainment of the full-revelation upper bound. -/
theorem causalPotentialObjective_isGreatest_full_iff_attainable
    (F : (Θ → ℝ) → ℝ) (hF : ContinuousOn F (stdSimplex ℝ Θ))
    (hstrict : StrictConvexOn ℝ (stdSimplex ℝ Θ) F)
    (α : Θ → ℝ) (hα : IsDist α) (hfs : FullSupport α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ)) :
    IsGreatest (Set.range (causalPotentialObjective F α Qs hQ))
      ((∑ θ, α θ * F (Pi.single θ 1)) - F α) ↔
        CausalFullRevelationAttainable Qs hQ := by
  rw [causalFullRevelationAttainable_iff_exactlyIdentifies Qs hQ]
  constructor
  · rintro ⟨⟨π, hπ⟩, _⟩
    exact ⟨π, (causalPotentialObjective_eq_full_iff_exactlyIdentifies
      F hF hstrict α hα hfs Qs hQ π).1 hπ⟩
  · rintro ⟨π, hid⟩
    refine ⟨⟨π, (causalPotentialObjective_eq_full_iff_exactlyIdentifies
      F hF hstrict α hα hfs Qs hQ π).2 hid⟩, ?_⟩
    rintro _ ⟨σ, rfl⟩
    exact causalPotentialObjective_le_full F hF hstrict.convexOn α hα Qs hQ σ

/-- Complete exact optimization has exactly the identifying policies as
maximizers whenever full revelation is attainable. -/
theorem causalPotentialObjective_maximizer_iff_exactlyIdentifies
    (F : (Θ → ℝ) → ℝ) (hF : ContinuousOn F (stdSimplex ℝ Θ))
    (hstrict : StrictConvexOn ℝ (stdSimplex ℝ Θ) F)
    (α : Θ → ℝ) (hα : IsDist α) (hfs : FullSupport α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hattain : CausalFullRevelationAttainable Qs hQ) (π : ValidCausalPolicy A O) :
    (∀ σ, causalPotentialObjective F α Qs hQ σ ≤ causalPotentialObjective F α Qs hQ π) ↔
      CausalExactlyIdentifies Qs hQ π := by
  have hmax := (causalPotentialObjective_isGreatest_full_iff_attainable
    F hF hstrict α hα hfs Qs hQ).2 hattain
  constructor
  · intro h
    apply (causalPotentialObjective_eq_full_iff_exactlyIdentifies
      F hF hstrict α hα hfs Qs hQ π).1
    obtain ⟨σ, hσ⟩ := hmax.1
    exact le_antisymm (causalPotentialObjective_le_full
      F hF hstrict.convexOn α hα Qs hQ π) (hσ ▸ h σ)
  · intro hid σ
    rw [(causalPotentialObjective_eq_full_iff_exactlyIdentifies
      F hF hstrict α hα hfs Qs hQ π).2 hid]
    exact causalPotentialObjective_le_full F hF hstrict.convexOn α hα Qs hQ σ

theorem causalTerminalPotential_maximizer_iff_exactlyIdentifies
    (F : (Θ → ℝ) → ℝ) (hF : ContinuousOn F (stdSimplex ℝ Θ))
    (hstrict : StrictConvexOn ℝ (stdSimplex ℝ Θ) F)
    (α : Θ → ℝ) (hα : IsDist α) (hfs : FullSupport α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hattain : CausalFullRevelationAttainable Qs hQ) (π : ValidCausalPolicy A O) :
    (∀ σ, causalTerminalPotential F α Qs hQ σ ≤ causalTerminalPotential F α Qs hQ π) ↔
      CausalExactlyIdentifies Qs hQ π := by
  have h := causalPotentialObjective_maximizer_iff_exactlyIdentifies
    F hF hstrict α hα hfs Qs hQ hattain π
  simpa only [causalPotentialObjective, sub_le_sub_iff_right] using h

theorem causalPotentialObjective_argmax_eq_nativelySufficient
    (F : (Θ → ℝ) → ℝ) (hF : ContinuousOn F (stdSimplex ℝ Θ))
    (hstrict : StrictConvexOn ℝ (stdSimplex ℝ Θ) F)
    (α : Θ → ℝ) (hα : IsDist α) (hfs : FullSupport α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hattain : CausalFullRevelationAttainable Qs hQ) :
    {π | ∀ σ, causalPotentialObjective F α Qs hQ σ ≤ causalPotentialObjective F α Qs hQ π} =
      {π | CausalNativelySufficient Qs π} := by
  ext π
  exact (causalPotentialObjective_maximizer_iff_exactlyIdentifies
    F hF hstrict α hα hfs Qs hQ hattain π).trans
      (causalNativelySufficient_iff_exactlyIdentifies_of_attainable Qs hQ hattain π).symm

end IdExp
