import Formal.PosteriorIdentification
import Formal.CausalFiniteRecovery

/-!
# Posterior concentration on actual causal histories

The response kernels and policy are arbitrary history-dependent causal
kernels. The finite observation is the full recorded action-observation
prefix, not a world-dependent observation or a POMDP encoding. Bayes' rule,
the prefix-filtration martingale, and all one/every-prior quantifiers are
instantiated explicitly.
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

/-- Bayes' posterior for the acquired experiment, including recorded actions.
It is zero at histories having zero mixture probability. -/
noncomputable def causalPosterior (α : Θ → ℝ) (Qs : Θ → CausalResponse A O)
    (π : ValidCausalPolicy A O) (t : ℕ) (w : CausalFiniteTrace A O t) (θ : Θ) : ℝ :=
  finiteBayesPosterior α (causalFiniteExperiment π.1 Qs t) w θ

/-- Almost-sure concentration under every true world. For a full-support
prior this is equivalent to the usual assertion under the Bayesian joint law. -/
def CausalPosteriorConcentrates (α : Θ → ℝ) (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π : ValidCausalPolicy A O) : Prop :=
  ∀ θ, ∀ᵐ ω ∂(causalPathExperiment Qs hQ π θ : Measure (CausalTraj A O)),
    Tendsto (fun t => causalPosterior α Qs π t (causalPrefixMap t ω) θ) atTop (𝓝 1)

theorem causalPathExperiment_prefix_mass (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (π : ValidCausalPolicy A O)
    (t : ℕ) (θ : Θ) (w : CausalFiniteTrace A O t) :
    (causalPathExperiment Qs hQ π θ : Measure (CausalTraj A O))
      (causalPrefixMap t ⁻¹' {w}) =
        ENNReal.ofReal (causalFiniteExperiment π.1 Qs t θ w) := by
  rw [causalPathExperiment_coe, causalPrefixMap_preimage_singleton, causalPathMeasure_cyl]
  rfl

theorem causalPosterior_ae_eq_condExp (α : Θ → ℝ) (hα : IsDist α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) (t : ℕ) (θ : Θ) :
    (fun x : Θ × CausalTraj A O => causalPosterior α Qs π t (causalPrefixMap t x.2) θ)
      =ᵐ[finiteBayesJoint α (fun θ => (causalPathExperiment Qs hQ π θ : Measure _))]
      (finiteBayesJoint α (fun θ => (causalPathExperiment Qs hQ π θ : Measure _)))[
        finiteBayesClassInd θ | finiteBayesFiltration (causalPrefixFiltration A O) t] := by
  rw [finiteBayesFiltration_eq_observation (causalPrefixFiltration A O)
    (fun t => causalPrefixMap t) (fun _ => rfl)]
  exact finiteBayesPosterior_ae_eq_condExp α _ hα
    (isProbabilityMeasure_causalPathExperiment' Qs hQ π)
    (causalPrefixMap t) (measurable_causalPrefixMap t)
    (causalFiniteExperiment π.1 Qs t)
    (fun θ w => (causalFiniteExperiment_valid π.1 π.2 Qs hQ t θ).1 w)
    (causalPathExperiment_prefix_mass Qs hQ π t) θ

theorem causalPosteriorConcentrates_iff_joint (α : Θ → ℝ) (hfs : FullSupport α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) :
    CausalPosteriorConcentrates α Qs hQ π ↔
      ∀ᵐ x ∂finiteBayesJoint α (fun θ =>
        (causalPathExperiment Qs hQ π θ : Measure (CausalTraj A O))),
        Tendsto (fun t => causalPosterior α Qs π t (causalPrefixMap t x.2) x.1)
          atTop (𝓝 1) :=
  finiteBayesConcentrates_iff_joint α _ (fun t => causalPrefixMap t)
    (fun t => causalFiniteExperiment π.1 Qs t) hfs

/-- The posterior/identification equivalence does not require that a policy
with full revelation exists: it holds for each individual policy. -/
theorem causalPosteriorConcentrates_iff_exactlyIdentifies
    (α : Θ → ℝ) (hα : IsDist α) (hfs : FullSupport α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) :
    CausalPosteriorConcentrates α Qs hQ π ↔ CausalExactlyIdentifies Qs hQ π := by
  have hnonneg : ∀ t θ w, 0 ≤ causalFiniteExperiment π.1 Qs t θ w :=
    fun t θ w => (causalFiniteExperiment_valid π.1 π.2 Qs hQ t θ).1 w
  constructor
  · intro hconc
    apply (causalExactlyIdentifies_iff_pairwise_mutuallySingular Qs hQ π).2
    exact pairwise_mutuallySingular_of_finiteBayesConcentrates α _ hα.1
      (fun t => causalPrefixMap t) (fun t => measurable_causalPrefixMap t)
      (fun t => causalFiniteExperiment π.1 Qs t) hnonneg hconc
  · rintro ⟨D, hD, herr⟩
    apply finiteBayesConcentrates_of_exactDecoder α _ hα hfs
      (isProbabilityMeasure_causalPathExperiment' Qs hQ π)
      (fun t => causalPrefixMap t) (fun t => measurable_causalPrefixMap t)
      (fun t => causalFiniteExperiment π.1 Qs t) hnonneg
      (causalPathExperiment_prefix_mass Qs hQ π)
      (causalPrefixFiltration A O) (fun _ => rfl) iSup_causalPrefixFiltration D hD
    exact fun θ => ae_iff.2 (herr θ)

theorem causalNativelySufficient_iff_posteriorConcentrates_of_attainable
    (α : Θ → ℝ) (hα : IsDist α) (hfs : FullSupport α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hattain : CausalFullRevelationAttainable Qs hQ) (π : ValidCausalPolicy A O) :
    CausalNativelySufficient Qs π ↔ CausalPosteriorConcentrates α Qs hQ π :=
  (causalNativelySufficient_iff_exactlyIdentifies_of_attainable Qs hQ hattain π).trans
    (causalPosteriorConcentrates_iff_exactlyIdentifies α hα hfs Qs hQ π).symm

/-- One full-support prior suffices; its choice cannot change whether the
policy identifies the class. -/
theorem causalPosteriorConcentrates_one_iff_every
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) :
    (∃ α : Θ → ℝ, IsDist α ∧ FullSupport α ∧ CausalPosteriorConcentrates α Qs hQ π) ↔
      ∀ α : Θ → ℝ, IsDist α → FullSupport α → CausalPosteriorConcentrates α Qs hQ π := by
  constructor
  · rintro ⟨α, hα, hfs, hconc⟩ β hβ hβfs
    exact (causalPosteriorConcentrates_iff_exactlyIdentifies β hβ hβfs Qs hQ π).2
      ((causalPosteriorConcentrates_iff_exactlyIdentifies α hα hfs Qs hQ π).1 hconc)
  · intro h
    let α : Θ → ℝ := fun _ => 1 / Fintype.card Θ
    have hpos : (0 : ℝ) < Fintype.card Θ := by exact_mod_cast Fintype.card_pos
    have hα : IsDist α := by
      refine ⟨fun _ => by dsimp [α]; positivity, ?_⟩
      simp only [α, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
    have hfs : FullSupport α := fun _ => by dsimp [α]; positivity
    exact ⟨α, hα, hfs, h α hα hfs⟩

theorem causalNativelySufficient_iff_some_posteriorConcentrates_of_attainable
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hattain : CausalFullRevelationAttainable Qs hQ) (π : ValidCausalPolicy A O) :
    CausalNativelySufficient Qs π ↔
      ∃ α : Θ → ℝ, IsDist α ∧ FullSupport α ∧ CausalPosteriorConcentrates α Qs hQ π := by
  rw [causalPosteriorConcentrates_one_iff_every Qs hQ π]
  constructor
  · intro h α hα hfs
    exact (causalNativelySufficient_iff_posteriorConcentrates_of_attainable
      α hα hfs Qs hQ hattain π).1 h
  · intro h
    obtain ⟨α, hα, hfs, hconc⟩ :=
      (causalPosteriorConcentrates_one_iff_every Qs hQ π).2 h
    exact (causalNativelySufficient_iff_posteriorConcentrates_of_attainable
      α hα hfs Qs hQ hattain π).2 hconc

theorem causalNativelySufficient_iff_every_posteriorConcentrates_of_attainable
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hattain : CausalFullRevelationAttainable Qs hQ) (π : ValidCausalPolicy A O) :
    CausalNativelySufficient Qs π ↔
      ∀ α : Θ → ℝ, IsDist α → FullSupport α → CausalPosteriorConcentrates α Qs hQ π :=
  (causalNativelySufficient_iff_some_posteriorConcentrates_of_attainable
    Qs hQ hattain π).trans (causalPosteriorConcentrates_one_iff_every Qs hQ π)

/-- All six items of the paper's finite attained-full-revelation theorem,
on the literal causal experiments. The prior is arbitrary with full support;
`causalPosteriorConcentrates_one_iff_every` supplies the existential/universal
prior reformulation. Exact terminal greatestness without full revelation is
the separate general terminal-garbling theorem. -/
theorem causalFiniteRecovery
    (α : Θ → ℝ) (hα : IsDist α) (hfs : FullSupport α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hattain : CausalFullRevelationAttainable Qs hQ) (π : ValidCausalPolicy A O) :
    List.TFAE [
      CausalNativelySufficient Qs π,
      BlackwellLE (fun θ => (causalPathExperiment Qs hQ π θ : Measure (CausalTraj A O)))
          (fun θ => Measure.dirac θ) ∧
        BlackwellLE (fun θ => Measure.dirac θ)
          (fun θ => (causalPathExperiment Qs hQ π θ : Measure (CausalTraj A O))),
      Pairwise fun θ η =>
        (causalPathExperiment Qs hQ π θ : Measure (CausalTraj A O)) ⟂ₘ
          (causalPathExperiment Qs hQ π η : Measure (CausalTraj A O)),
      ∃ D : CausalTraj A O → Θ, Measurable D ∧
        ∀ θ, (causalPathExperiment Qs hQ π θ : Measure (CausalTraj A O))
          {ω | D ω = θ} = 1,
      CausalPosteriorConcentrates α Qs hQ π,
      Tendsto (fun t => deterministicLabelMinimaxError (causalFiniteExperiment π.1 Qs t))
        atTop (𝓝 0)] := by
  tfae_have 1 ↔ 2 :=
    causalNativelySufficient_iff_fullRevelationBlackwellEquiv_of_attainable Qs hQ hattain π
  tfae_have 1 ↔ 3 :=
    causalNativelySufficient_iff_pairwise_mutuallySingular_of_attainable Qs hQ hattain π
  tfae_have 1 ↔ 4 :=
    (causalNativelySufficient_iff_exactlyIdentifies_of_attainable Qs hQ hattain π).trans
      (causalExactlyIdentifies_iff_correct_probability_one Qs hQ π)
  tfae_have 1 ↔ 5 :=
    causalNativelySufficient_iff_posteriorConcentrates_of_attainable α hα hfs Qs hQ hattain π
  tfae_have 1 ↔ 6 :=
    causalNativelySufficient_iff_prefixDeterministicError_tendsto_zero_of_attainable Qs hQ hattain π
  tfae_finish

end IdExp
