import Formal.BregmanPotential

/-!
# Limits and exact tops of continuous posterior potentials

These are model-independent measure-theoretic completion lemmas for finite
posterior vectors. Continuity is required only on the simplex. The posterior
need belong to that simplex only almost surely, so the zero-on-null-signal
Bayes convention is allowed without redefining the posterior.

The mean-posterior and almost-sure convergence hypotheses are explicit here;
they are not replaced by a claim that every simplex-valued process is Bayesian.
`CausalPosteriorLimit` and `CausalPotentialObjective` instantiate these
hypotheses on the actual Bayesian terminal posterior.
-/

namespace IdExp

open MeasureTheory Filter Set
open scoped Topology

variable {Θ Ω : Type*} [Fintype Θ] [MeasurableSpace Ω]

/-- A continuous simplex potential composed with an a.e. simplex-valued
measurable posterior is integrable under every finite measure. -/
theorem integrable_simplex_potential (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : (Θ → ℝ) → ℝ) (hF : ContinuousOn F (stdSimplex ℝ Θ))
    (p : Ω → Θ → ℝ) (hpm : AEMeasurable p μ)
    (hp : ∀ᵐ ω ∂μ, p ω ∈ stdSimplex ℝ Θ) :
    Integrable (fun ω => F (p ω)) μ := by
  classical
  have hs : MeasurableSet (stdSimplex ℝ Θ) := (isCompact_stdSimplex ℝ Θ).isClosed.measurableSet
  have hm : Measurable ((stdSimplex ℝ Θ).piecewise F (fun _ => 0)) :=
    hF.measurable_piecewise continuous_const.continuousOn hs
  have hmeas : AEStronglyMeasurable (fun ω => F (p ω)) μ := by
    apply (hm.comp_aemeasurable hpm).aestronglyMeasurable.congr
    filter_upwards [hp] with ω hω
    simp [hω]
  obtain ⟨C, hC⟩ := (isCompact_stdSimplex ℝ Θ).exists_bound_of_continuousOn hF
  exact Integrable.of_bound hmeas C (hp.mono fun ω hω => hC _ hω)

/-- A bounded continuous simplex potential commutes with an a.s. posterior
limit. No differentiability, gradient bound, or full support is involved. -/
theorem tendsto_integral_simplex_potential (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : (Θ → ℝ) → ℝ) (hF : ContinuousOn F (stdSimplex ℝ Θ))
    (p : ℕ → Ω → Θ → ℝ) (pLimit : Ω → Θ → ℝ)
    (hpm : ∀ n, AEMeasurable (p n) μ)
    (hp : ∀ n, ∀ᵐ ω ∂μ, p n ω ∈ stdSimplex ℝ Θ)
    (hpLimit : ∀ᵐ ω ∂μ, pLimit ω ∈ stdSimplex ℝ Θ)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => p n ω) atTop (𝓝 (pLimit ω))) :
    Tendsto (fun n => ∫ ω, F (p n ω) ∂μ) atTop (𝓝 (∫ ω, F (pLimit ω) ∂μ)) := by
  obtain ⟨C, hC⟩ := (isCompact_stdSimplex ℝ Θ).exists_bound_of_continuousOn hF
  refine tendsto_integral_of_dominated_convergence (fun _ => C)
    (fun n => (integrable_simplex_potential μ F hF (p n) (hpm n) (hp n)).aestronglyMeasurable)
    (integrable_const C) (fun n => (hp n).mono fun ω hω => hC _ hω) ?_
  filter_upwards [ae_all_iff.2 hp, hpLimit, hlim] with ω hω hωLimit hωlim
  exact Filter.Tendsto.comp (hF (pLimit ω) hωLimit)
    (tendsto_nhdsWithin_iff.2 ⟨hωlim, Eventually.of_forall hω⟩)

section Strict

variable [DecidableEq Θ]

theorem continuousOn_posteriorPotentialGap (F : (Θ → ℝ) → ℝ)
    (hF : ContinuousOn F (stdSimplex ℝ Θ)) :
    ContinuousOn (posteriorPotentialGap F) (stdSimplex ℝ Θ) := by
  apply ContinuousOn.sub _ hF
  exact (continuous_finsetSum _ fun θ _ => (continuous_apply θ).mul continuous_const).continuousOn

/-- The expected full-revelation gap equals the full-revelation value at
the prior minus the expected posterior potential. -/
theorem integral_posteriorPotentialGap (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : (Θ → ℝ) → ℝ) (hF : ContinuousOn F (stdSimplex ℝ Θ))
    (p : Ω → Θ → ℝ) (hpm : AEMeasurable p μ)
    (hp : ∀ᵐ ω ∂μ, p ω ∈ stdSimplex ℝ Θ)
    (α : Θ → ℝ) (hmean : ∀ θ, ∫ ω, p ω θ ∂μ = α θ) :
    ∫ ω, posteriorPotentialGap F (p ω) ∂μ =
      (∑ θ, α θ * F (Pi.single θ 1)) - ∫ ω, F (p ω) ∂μ := by
  have hcoord (θ : Θ) : Integrable (fun ω => p ω θ) μ :=
    integrable_simplex_potential μ (fun q => q θ) (continuous_apply θ).continuousOn p hpm hp
  have hterm (θ : Θ) : Integrable (fun ω => p ω θ * F (Pi.single θ 1)) μ :=
    (hcoord θ).mul_const _
  simp only [posteriorPotentialGap]
  rw [integral_sub (integrable_finsetSum _ fun θ _ => hterm θ)
    (integrable_simplex_potential μ F hF p hpm hp),
    integral_finsetSum _ fun θ _ => hterm θ]
  simp_rw [integral_mul_const, hmean]

/-- Full revelation bounds every continuous convex posterior potential. -/
theorem integral_posteriorPotential_le_full (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : (Θ → ℝ) → ℝ) (hF : ContinuousOn F (stdSimplex ℝ Θ))
    (hconvex : ConvexOn ℝ (stdSimplex ℝ Θ) F)
    (p : Ω → Θ → ℝ) (hpm : AEMeasurable p μ)
    (hp : ∀ᵐ ω ∂μ, p ω ∈ stdSimplex ℝ Θ)
    (α : Θ → ℝ) (hmean : ∀ θ, ∫ ω, p ω θ ∂μ = α θ) :
    ∫ ω, F (p ω) ∂μ ≤ ∑ θ, α θ * F (Pi.single θ 1) := by
  have hnonneg := integral_nonneg_of_ae (hp.mono fun ω hω =>
    posteriorPotentialGap_nonneg F hconvex hω)
  rw [integral_posteriorPotentialGap μ F hF p hpm hp α hmean] at hnonneg
  exact sub_nonneg.mp hnonneg

/-- A continuous strictly convex posterior potential reaches its exact
full-revelation bound iff the posterior is almost surely a simplex vertex.
The required Bayesian content here is precisely the stated mean identity. -/
theorem integral_posteriorPotential_eq_full_iff (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : (Θ → ℝ) → ℝ) (hF : ContinuousOn F (stdSimplex ℝ Θ))
    (hstrict : StrictConvexOn ℝ (stdSimplex ℝ Θ) F)
    (p : Ω → Θ → ℝ) (hpm : AEMeasurable p μ)
    (hp : ∀ᵐ ω ∂μ, p ω ∈ stdSimplex ℝ Θ)
    (α : Θ → ℝ) (hmean : ∀ θ, ∫ ω, p ω θ ∂μ = α θ) :
    (∫ ω, F (p ω) ∂μ = ∑ θ, α θ * F (Pi.single θ 1)) ↔
      ∀ᵐ ω ∂μ, ∃ θ, p ω = Pi.single θ 1 := by
  have hnonneg : 0 ≤ᵐ[μ] (fun ω => posteriorPotentialGap F (p ω)) :=
    hp.mono fun ω hω => posteriorPotentialGap_nonneg F hstrict.convexOn hω
  have hint := integrable_simplex_potential μ (posteriorPotentialGap F)
    (continuousOn_posteriorPotentialGap F hF) p hpm hp
  have heq := integral_eq_zero_iff_of_nonneg_ae hnonneg hint
  rw [integral_posteriorPotentialGap μ F hF p hpm hp α hmean, sub_eq_zero] at heq
  constructor
  · intro h
    have hz := heq.1 h.symm
    filter_upwards [hp, hz] with ω hω hzω
    exact (posteriorPotentialGap_eq_zero_iff F hstrict hω).1 hzω
  · intro h
    apply Eq.symm
    apply heq.2
    filter_upwards [hp, h] with ω hω hv
    exact (posteriorPotentialGap_eq_zero_iff F hstrict hω).2 hv

end Strict

end IdExp
