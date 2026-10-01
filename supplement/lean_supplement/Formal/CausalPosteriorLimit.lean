import Formal.CausalPosterior
import Formal.TerminalPosterior
import Formal.FiniteBayesObservation
import Formal.FiniteBayesBregman
import Formal.PosteriorPotentialLimit

/-!
# Actual causal posterior limits and expectations

The full-sample posterior is the conditional class law given the infinite
recorded action-observation history. Lévy convergence of the generating
prefix filtration gives its almost-sure vector limit. Finite-prefix
potentials are literal expectations, and every continuous simplex
potential converges in expectation without a gradient bound.
-/

namespace IdExp

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

set_option linter.unusedSectionVars false

variable {Θ A O : Type*} [Fintype Θ] [Nonempty Θ] [DecidableEq Θ]
  [MeasurableSpace Θ] [MeasurableSingletonClass Θ]
  [Fintype A] [Fintype O] [Nonempty A] [Nonempty O]
  [MeasurableSpace A] [MeasurableSpace O]
  [MeasurableSingletonClass A] [MeasurableSingletonClass O]

/-- Joint prior/world and actual infinite causal-history law. -/
noncomputable def causalBayesJoint (α : Θ → ℝ) (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π : ValidCausalPolicy A O) :
    Measure (Θ × CausalTraj A O) :=
  finiteBayesJoint α (fun θ => (causalPathExperiment Qs hQ π θ : Measure _))

theorem isProbabilityMeasure_causalBayesJoint (α : Θ → ℝ) (hα : IsDist α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) : IsProbabilityMeasure (causalBayesJoint α Qs hQ π) :=
  isProbabilityMeasure_finiteBayesJoint hα _
    (isProbabilityMeasure_causalPathExperiment' Qs hQ π)

/-- Conditional class probabilities given the whole acquired history. -/
noncomputable def causalLimitPosterior (α : Θ → ℝ) (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π : ValidCausalPolicy A O) :
    (Θ × CausalTraj A O) → Θ → ℝ :=
  finiteBayesLimitPosterior α
    (fun θ => (causalPathExperiment Qs hQ π θ : Measure _))

theorem measurable_causalLimitPosterior (α : Θ → ℝ)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) : Measurable (causalLimitPosterior α Qs hQ π) :=
  measurable_finiteBayesLimitPosterior α _

theorem ae_causalLimitPosterior_mem_simplex (α : Θ → ℝ) (hα : IsDist α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) :
    ∀ᵐ x ∂causalBayesJoint α Qs hQ π,
      causalLimitPosterior α Qs hQ π x ∈ stdSimplex ℝ Θ :=
  ae_isDist_finiteBayesLimitPosterior α hα _
    (isProbabilityMeasure_causalPathExperiment' Qs hQ π)

theorem causalPosterior_tendsto_limit (α : Θ → ℝ) (hα : IsDist α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) :
    ∀ᵐ x ∂causalBayesJoint α Qs hQ π,
      Tendsto (fun t => causalPosterior α Qs π t (causalPrefixMap t x.2))
        atTop (𝓝 (causalLimitPosterior α Qs hQ π x)) := by
  have hcoord : ∀ θ, ∀ᵐ x ∂causalBayesJoint α Qs hQ π,
      Tendsto (fun t => causalPosterior α Qs π t (causalPrefixMap t x.2) θ)
        atTop (𝓝 (causalLimitPosterior α Qs hQ π x θ)) := by
    intro θ
    exact finiteBayesPosterior_tendsto_condExp α _ hα
      (isProbabilityMeasure_causalPathExperiment' Qs hQ π)
      (fun t => causalPrefixMap t) (fun t => measurable_causalPrefixMap t)
      (fun t => causalFiniteExperiment π.1 Qs t)
      (fun t θ w => (causalFiniteExperiment_valid π.1 π.2 Qs hQ t θ).1 w)
      (causalPathExperiment_prefix_mass Qs hQ π)
      (causalPrefixFiltration A O) (fun _ => rfl) iSup_causalPrefixFiltration θ
  filter_upwards [ae_all_iff.2 hcoord] with x hx
  exact tendsto_pi_nhds.2 hx

/-- Every finite-prefix statistic is integrable, regardless of its values
outside the finite set of posterior states visited at that horizon. -/
theorem integrable_causalPrefix (α : Θ → ℝ) (hα : IsDist α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) (t : ℕ) (g : CausalFiniteTrace A O t → ℝ) :
    Integrable (fun x : Θ × CausalTraj A O => g (causalPrefixMap t x.2))
      (causalBayesJoint α Qs hQ π) := by
  letI := isProbabilityMeasure_causalBayesJoint α hα Qs hQ π
  exact integrable_comp_finiteObservation _ _
    ((measurable_causalPrefixMap t).comp measurable_snd) g

theorem integral_causalPrefix_eq_sum (α : Θ → ℝ) (hα : IsDist α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) (t : ℕ) (g : CausalFiniteTrace A O t → ℝ) :
    ∫ x : Θ × CausalTraj A O, g (causalPrefixMap t x.2) ∂causalBayesJoint α Qs hQ π =
      ∑ w, finiteBayesMass α (causalFiniteExperiment π.1 Qs t) w * g w :=
  integral_finiteBayesObservation α hα _
    (isProbabilityMeasure_causalPathExperiment' Qs hQ π) _
    (measurable_causalPrefixMap t) _
    (fun θ w => (causalFiniteExperiment_valid π.1 π.2 Qs hQ t θ).1 w)
    (causalPathExperiment_prefix_mass Qs hQ π t) g

theorem ae_causalPrefix_mass_pos (α : Θ → ℝ) (hα : IsDist α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) (t : ℕ) :
    ∀ᵐ x : Θ × CausalTraj A O ∂causalBayesJoint α Qs hQ π,
      0 < finiteBayesMass α (causalFiniteExperiment π.1 Qs t) (causalPrefixMap t x.2) :=
  ae_finiteBayesObservation_mass_pos α _ _ (measurable_causalPrefixMap t) _
    hα.1 (fun θ w => (causalFiniteExperiment_valid π.1 π.2 Qs hQ t θ).1 w)
    (causalPathExperiment_prefix_mass Qs hQ π t)

theorem ae_causalPosterior_mem_simplex (α : Θ → ℝ) (hα : IsDist α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) (t : ℕ) :
    ∀ᵐ x ∂causalBayesJoint α Qs hQ π,
      causalPosterior α Qs π t (causalPrefixMap t x.2) ∈ stdSimplex ℝ Θ := by
  filter_upwards [ae_causalPrefix_mass_pos α hα Qs hQ π t] with x hx
  exact finiteBayesPosterior_mem_simplex α _ hα.1
    (fun θ w => (causalFiniteExperiment_valid π.1 π.2 Qs hQ t θ).1 w) _ hx.ne'

/-- The expected terminal potential is the actual limit of finite Bayesian
potentials. The convergence premise in the algebraic Bregman core is discharged. -/
theorem tendsto_causalBayesPotential (α : Θ → ℝ) (hα : IsDist α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) (F : (Θ → ℝ) → ℝ)
    (hF : ContinuousOn F (stdSimplex ℝ Θ)) :
    Tendsto (fun t => finiteBayesPotential F α (causalFiniteExperiment π.1 Qs t))
      atTop (𝓝 (∫ x, F (causalLimitPosterior α Qs hQ π x) ∂causalBayesJoint α Qs hQ π)) := by
  letI := isProbabilityMeasure_causalBayesJoint α hα Qs hQ π
  have h := tendsto_integral_simplex_potential (causalBayesJoint α Qs hQ π) F hF
    (fun t x => causalPosterior α Qs π t (causalPrefixMap t x.2))
    (causalLimitPosterior α Qs hQ π)
    (fun t => ((measurable_of_finite (causalPosterior α Qs π t)).comp
      ((measurable_causalPrefixMap t).comp measurable_snd)).aemeasurable)
    (ae_causalPosterior_mem_simplex α hα Qs hQ π)
    (ae_causalLimitPosterior_mem_simplex α hα Qs hQ π)
    (causalPosterior_tendsto_limit α hα Qs hQ π)
  convert h using 1
  funext t
  exact (integral_causalPrefix_eq_sum α hα Qs hQ π t
    (fun w => F (causalPosterior α Qs π t w))).symm

end IdExp
