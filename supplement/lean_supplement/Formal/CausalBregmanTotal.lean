import Formal.CausalBregman
import Formal.CausalPotentialObjective
import Formal.NonnegativeIntegralSeries

/-!
# The complete expected Bregman movement of an actual causal policy

Each reward is a function of one finite action-observation prefix. Therefore
it is measurable and integrable even when the chosen face derivatives have
no globally measurable or bounded extension. The finite bound may depend on
time. The complete-total theorem uses summable nonnegative expectations to
prove pathwise summability, integrability, and interchange with expectation.
-/

namespace IdExp

open MeasureTheory Filter
open scoped Topology

set_option linter.unusedSectionVars false

variable {Θ A O : Type*} [Fintype Θ] [Nonempty Θ] [DecidableEq Θ]
  [MeasurableSpace Θ] [MeasurableSingletonClass Θ]
  [Fintype A] [Fintype O] [Nonempty A] [Nonempty O]
  [MeasurableSpace A] [MeasurableSpace O]
  [MeasurableSingletonClass A] [MeasurableSingletonClass O]

/-- The step-`n` posterior movement as a function of the full next prefix.
The coarser posterior uses the same prefix with its last pair forgotten. -/
noncomputable def causalBregmanFiniteMovement (F : (Θ → ℝ) → ℝ)
    (dF : (Θ → ℝ) → (Θ → ℝ) →L[ℝ] ℝ) (α : Θ → ℝ)
    (Qs : Θ → CausalResponse A O) (π : ValidCausalPolicy A O)
    (n : ℕ) (w : CausalFiniteTrace A O (n + 1)) : ℝ :=
  facewiseBregman F dF (causalPosterior α Qs π (n + 1) w)
    (causalPosterior α Qs π n (Fin.init w))

/-- The actual posterior-movement random variable. The hidden label
coordinate is not used to compute the reward. -/
noncomputable def causalBregmanMovement (F : (Θ → ℝ) → ℝ)
    (dF : (Θ → ℝ) → (Θ → ℝ) →L[ℝ] ℝ) (α : Θ → ℝ)
    (Qs : Θ → CausalResponse A O) (π : ValidCausalPolicy A O)
    (n : ℕ) (x : Θ × CausalTraj A O) : ℝ :=
  causalBregmanFiniteMovement F dF α Qs π n (causalPrefixMap (n + 1) x.2)

/-- The finite-prefix presentation is literally the paper's
`D_F (rho_{n+1}, rho_n)` on one acquired trajectory. -/
theorem causalBregmanMovement_eq (F : (Θ → ℝ) → ℝ)
    (dF : (Θ → ℝ) → (Θ → ℝ) →L[ℝ] ℝ) (α : Θ → ℝ)
    (Qs : Θ → CausalResponse A O) (π : ValidCausalPolicy A O)
    (n : ℕ) (x : Θ × CausalTraj A O) :
    causalBregmanMovement F dF α Qs π n x =
      facewiseBregman F dF
        (causalPosterior α Qs π (n + 1) (causalPrefixMap (n + 1) x.2))
        (causalPosterior α Qs π n (causalPrefixMap n x.2)) := rfl

/-- No global measurability hypothesis on the face derivative is needed:
at this fixed time the reward factors through a finite signal. -/
theorem measurable_causalBregmanMovement (F : (Θ → ℝ) → ℝ)
    (dF : (Θ → ℝ) → (Θ → ℝ) →L[ℝ] ℝ) (α : Θ → ℝ)
    (Qs : Θ → CausalResponse A O) (π : ValidCausalPolicy A O) (n : ℕ) :
    Measurable (causalBregmanMovement F dF α Qs π n) :=
  (measurable_of_finite (causalBregmanFiniteMovement F dF α Qs π n)).comp
    ((measurable_causalPrefixMap (n + 1)).comp measurable_snd)

/-- Every fixed-time movement is integrable. Its finite bound depends on
the time and derivative values; no uniform gradient bound is assumed. -/
theorem integrable_causalBregmanMovement (F : (Θ → ℝ) → ℝ)
    (dF : (Θ → ℝ) → (Θ → ℝ) →L[ℝ] ℝ) (α : Θ → ℝ)
    (Qs : Θ → CausalResponse A O) (π : ValidCausalPolicy A O) (n : ℕ)
    (μ : Measure (Θ × CausalTraj A O)) [IsFiniteMeasure μ] :
    Integrable (causalBregmanMovement F dF α Qs π n) μ := by
  refine Integrable.of_bound
    (measurable_causalBregmanMovement F dF α Qs π n).aestronglyMeasurable
    (∑ w, ‖causalBregmanFiniteMovement F dF α Qs π n w‖) ?_
  filter_upwards with x
  exact Finset.single_le_sum (fun w _ => norm_nonneg _)
    (Finset.mem_univ (causalPrefixMap (n + 1) x.2))

/-- A positive-mass observed child stays on the parent's current support
face, so its literal movement is nonnegative. Null prefixes need not be
assigned an artificial normalized posterior. -/
theorem causalBregmanFiniteMovement_nonneg_of_mass_pos
    (F : (Θ → ℝ) → ℝ) (hF : ConvexOn ℝ (stdSimplex ℝ Θ) F)
    (dF : (Θ → ℝ) → (Θ → ℝ) →L[ℝ] ℝ) (hdF : HasFacewiseDerivative F dF)
    (α : Θ → ℝ) (hα : IsDist α) (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π : ValidCausalPolicy A O)
    (n : ℕ) (w : CausalFiniteTrace A O (n + 1))
    (hw : 0 < finiteBayesMass α (causalFiniteExperiment π.1 Qs (n + 1)) w) :
    0 ≤ causalBregmanFiniteMovement F dF α Qs π n w := by
  classical
  let E := causalFiniteExperiment π.1 Qs (n + 1)
  let B := causalFiniteExperiment π.1 Qs n
  have hE : ∀ θ s, 0 ≤ E θ s :=
    fun θ s => (causalFiniteExperiment_valid π.1 π.2 Qs hQ (n + 1) θ).1 s
  have hB : ∀ θ s, 0 ≤ B θ s :=
    fun θ s => (causalFiniteExperiment_valid π.1 π.2 Qs hQ n θ).1 s
  have href : IsFiniteRefinement E B Fin.init :=
    causalFiniteExperiment_isFiniteRefinement π.1 π.2 Qs hQ n
  exact facewiseBregman_nonneg F hF dF hdF
    (finiteBayesPosterior_mem_simplex α B hα.1 hB (Fin.init w)
      (finiteBayesMass_parent_pos α E B Fin.init hα.1 hE href w hw).ne')
    (finiteBayesPosterior_refinement_support α E B Fin.init hα.1 hE hB href w hw)

/-- Almost-sure nonnegativity under the actual Bayesian experiment, with
null prefixes discarded using their proved zero probability. -/
theorem ae_causalBregmanMovement_nonneg
    (F : (Θ → ℝ) → ℝ) (hF : ConvexOn ℝ (stdSimplex ℝ Θ) F)
    (dF : (Θ → ℝ) → (Θ → ℝ) →L[ℝ] ℝ) (hdF : HasFacewiseDerivative F dF)
    (α : Θ → ℝ) (hα : IsDist α) (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π : ValidCausalPolicy A O) (n : ℕ) :
    0 ≤ᵐ[causalBayesJoint α Qs hQ π]
      causalBregmanMovement F dF α Qs π n := by
  filter_upwards [ae_causalPrefix_mass_pos α hα Qs hQ π (n + 1)] with x hx
  exact causalBregmanFiniteMovement_nonneg_of_mass_pos F hF dF hdF α hα Qs hQ π
    n (causalPrefixMap (n + 1) x.2) hx

/-- The integral of the actual movement random variable equals the already
verified finite mixture increment. -/
theorem integral_causalBregmanMovement
    (F : (Θ → ℝ) → ℝ) (dF : (Θ → ℝ) → (Θ → ℝ) →L[ℝ] ℝ)
    (α : Θ → ℝ) (hα : IsDist α) (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π : ValidCausalPolicy A O) (n : ℕ) :
    (∫ x, causalBregmanMovement F dF α Qs π n x ∂causalBayesJoint α Qs hQ π) =
      finiteBayesBregmanIncrement F dF α (causalFiniteExperiment π.1 Qs (n + 1))
        (causalFiniteExperiment π.1 Qs n) Fin.init := by
  exact integral_causalPrefix_eq_sum α hα Qs hQ π (n + 1)
    (causalBregmanFiniteMovement F dF α Qs π n)

/-- The series of expected actual movements has its exact terminal value.
Unlike the earlier algebraic core, no expected-potential limit is assumed. -/
theorem causalBregman_hasSum_integral
    (F : (Θ → ℝ) → ℝ) (hF : ContinuousOn F (stdSimplex ℝ Θ))
    (hconvex : ConvexOn ℝ (stdSimplex ℝ Θ) F)
    (dF : (Θ → ℝ) → (Θ → ℝ) →L[ℝ] ℝ) (hdF : HasFacewiseDerivative F dF)
    (α : Θ → ℝ) (hα : IsDist α) (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π : ValidCausalPolicy A O) :
    HasSum (fun n => ∫ x, causalBregmanMovement F dF α Qs π n x
      ∂causalBayesJoint α Qs hQ π) (causalPotentialObjective F α Qs hQ π) := by
  simp_rw [integral_causalBregmanMovement F dF α hα Qs hQ π]
  exact causalBregman_hasSum_of_potential_tendsto F hconvex dF hdF α hα
    π.1 π.2 Qs hQ (causalTerminalPotential F α Qs hQ π)
    (tendsto_causalBayesPotential α hα Qs hQ π F hF)

/-- The pathwise complete, undiscounted movement total. Its a.s.
summability and integrability are proved below before taking its expectation. -/
noncomputable def causalBregmanTotal (F : (Θ → ℝ) → ℝ)
    (dF : (Θ → ℝ) → (Θ → ℝ) →L[ℝ] ℝ) (α : Θ → ℝ)
    (Qs : Θ → CausalResponse A O) (π : ValidCausalPolicy A O)
    (x : Θ × CausalTraj A O) : ℝ :=
  ∑' n, causalBregmanMovement F dF α Qs π n x

/-- The complete expected posterior-movement objective, defined from the
actual random total rather than from the terminal formula it will satisfy. -/
noncomputable def causalBregmanObjective (F : (Θ → ℝ) → ℝ)
    (dF : (Θ → ℝ) → (Θ → ℝ) →L[ℝ] ℝ) (α : Θ → ℝ)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) : ℝ :=
  ∫ x, causalBregmanTotal F dF α Qs π x ∂causalBayesJoint α Qs hQ π

/-- The actual infinite movement is a.s. summable, its total is integrable,
and expectation equals the terminal potential gain. No uniform bound or
global measurability of the derivatives, or full support of the prior, is
required for this identity. -/
theorem causalBregmanTotal_summable_integrable_identity
    (F : (Θ → ℝ) → ℝ) (hF : ContinuousOn F (stdSimplex ℝ Θ))
    (hconvex : ConvexOn ℝ (stdSimplex ℝ Θ) F)
    (dF : (Θ → ℝ) → (Θ → ℝ) →L[ℝ] ℝ) (hdF : HasFacewiseDerivative F dF)
    (α : Θ → ℝ) (hα : IsDist α) (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π : ValidCausalPolicy A O) :
    (∀ᵐ x ∂causalBayesJoint α Qs hQ π,
      Summable (fun n => causalBregmanMovement F dF α Qs π n x)) ∧
      Integrable (causalBregmanTotal F dF α Qs π) (causalBayesJoint α Qs hQ π) ∧
      causalBregmanObjective F dF α Qs hQ π = causalPotentialObjective F α Qs hQ π := by
  have := isProbabilityMeasure_causalBayesJoint α hα Qs hQ π
  exact integrable_tsum_of_nonneg_hasSum_integral (causalBayesJoint α Qs hQ π)
    (causalBregmanMovement F dF α Qs π)
    (fun n => integrable_causalBregmanMovement F dF α Qs π n _)
    (ae_causalBregmanMovement_nonneg F hconvex dF hdF α hα Qs hQ π)
    (causalPotentialObjective F α Qs hQ π)
    (causalBregman_hasSum_integral F hF hconvex dF hdF α hα Qs hQ π)

/-- The paper's literal expected infinite-sum identity on actual causal
posteriors. A.s. summability and integrability are supplied by the preceding
theorem, not presumed from the use of real-valued infinite sums. -/
theorem causalBregman_total_identity
    (F : (Θ → ℝ) → ℝ) (hF : ContinuousOn F (stdSimplex ℝ Θ))
    (hconvex : ConvexOn ℝ (stdSimplex ℝ Θ) F)
    (dF : (Θ → ℝ) → (Θ → ℝ) →L[ℝ] ℝ) (hdF : HasFacewiseDerivative F dF)
    (α : Θ → ℝ) (hα : IsDist α) (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π : ValidCausalPolicy A O) :
    (∫ x, ∑' n, facewiseBregman F dF
        (causalPosterior α Qs π (n + 1) (causalPrefixMap (n + 1) x.2))
        (causalPosterior α Qs π n (causalPrefixMap n x.2)) ∂causalBayesJoint α Qs hQ π) =
      (∫ x, F (causalLimitPosterior α Qs hQ π x) ∂causalBayesJoint α Qs hQ π) - F α := by
  simpa only [causalBregmanObjective, causalBregmanTotal, causalBregmanMovement_eq,
    causalPotentialObjective, causalTerminalPotential] using
    (causalBregmanTotal_summable_integrable_identity F hF hconvex dF hdF α hα Qs hQ π).2.2

theorem causalBregmanObjective_eq_potential
    (F : (Θ → ℝ) → ℝ) (hF : ContinuousOn F (stdSimplex ℝ Θ))
    (hconvex : ConvexOn ℝ (stdSimplex ℝ Θ) F)
    (dF : (Θ → ℝ) → (Θ → ℝ) →L[ℝ] ℝ) (hdF : HasFacewiseDerivative F dF)
    (α : Θ → ℝ) (hα : IsDist α) (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π : ValidCausalPolicy A O) :
    causalBregmanObjective F dF α Qs hQ π = causalPotentialObjective F α Qs hQ π :=
  (causalBregmanTotal_summable_integrable_identity F hF hconvex dF hdF α hα Qs hQ π).2.2

/-- Complete exact optimization of the actual expected movement total has
exactly the identifying policies as maximizers, under attainable full revelation. -/
theorem causalBregmanObjective_maximizer_iff_exactlyIdentifies
    (F : (Θ → ℝ) → ℝ) (hF : ContinuousOn F (stdSimplex ℝ Θ))
    (hstrict : StrictConvexOn ℝ (stdSimplex ℝ Θ) F)
    (dF : (Θ → ℝ) → (Θ → ℝ) →L[ℝ] ℝ) (hdF : HasFacewiseDerivative F dF)
    (α : Θ → ℝ) (hα : IsDist α) (hfs : FullSupport α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hattain : CausalFullRevelationAttainable Qs hQ) (π : ValidCausalPolicy A O) :
    (∀ σ, causalBregmanObjective F dF α Qs hQ σ ≤ causalBregmanObjective F dF α Qs hQ π) ↔
      CausalExactlyIdentifies Qs hQ π := by
  simp_rw [causalBregmanObjective_eq_potential F hF hstrict.convexOn dF hdF α hα Qs hQ]
  exact causalPotentialObjective_maximizer_iff_exactlyIdentifies F hF hstrict α hα hfs Qs hQ hattain π

theorem causalBregmanObjective_argmax_eq_nativelySufficient
    (F : (Θ → ℝ) → ℝ) (hF : ContinuousOn F (stdSimplex ℝ Θ))
    (hstrict : StrictConvexOn ℝ (stdSimplex ℝ Θ) F)
    (dF : (Θ → ℝ) → (Θ → ℝ) →L[ℝ] ℝ) (hdF : HasFacewiseDerivative F dF)
    (α : Θ → ℝ) (hα : IsDist α) (hfs : FullSupport α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hattain : CausalFullRevelationAttainable Qs hQ) :
    {π | ∀ σ, causalBregmanObjective F dF α Qs hQ σ ≤ causalBregmanObjective F dF α Qs hQ π} =
      {π | CausalNativelySufficient Qs π} := by
  ext π
  exact (causalBregmanObjective_maximizer_iff_exactlyIdentifies
    F hF hstrict dF hdF α hα hfs Qs hQ hattain π).trans
      (causalNativelySufficient_iff_exactlyIdentifies_of_attainable Qs hQ hattain π).symm

end IdExp
