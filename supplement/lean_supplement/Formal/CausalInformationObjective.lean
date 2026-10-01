import Formal.FiniteBayesInformation
import Formal.CausalBregman
import Formal.CausalPotentialObjective

/-!
# Complete mutual information on actual causal experiments

Terminal information is prior entropy minus the expected entropy of the
posterior given the full recorded path. The finite-prefix information curve
is monotone, converges to that terminal value, and has that value as its
supremum. Thus the complete undiscounted objective is not an assumed limit.

For every full-support probability prior its value equals the prior entropy
exactly at identifying policies. Attainable full revelation is needed only
to conclude that these are precisely the maximizing policies, equivalently
the natively sufficient policies. No finite-POMDP encoding is imported.
-/

namespace IdExp

open MeasureTheory ProbabilityTheory Filter Topology

variable {Θ A O : Type*} [Fintype Θ] [Nonempty Θ] [DecidableEq Θ]
  [MeasurableSpace Θ] [MeasurableSingletonClass Θ]
  [Fintype A] [Fintype O] [Nonempty A] [Nonempty O]
  [MeasurableSpace A] [MeasurableSpace O]
  [MeasurableSingletonClass A] [MeasurableSingletonClass O]

/-- Entropy-form information in the full recorded action--observation prefix. -/
noncomputable def causalPrefixInformation (α : Θ → ℝ)
    (Qs : Θ → CausalResponse A O) (π : ValidCausalPolicy A O) (t : ℕ) : ℝ :=
  finiteBayesInformation α (causalFiniteExperiment π.1 Qs t)

/-- Mutual information between the finite class and the complete causal path,
in the entropy form used by the paper. -/
noncomputable def causalInformationObjective (α : Θ → ℝ)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) : ℝ :=
  ent α - ∫ x, ent (causalLimitPosterior α Qs hQ π x) ∂causalBayesJoint α Qs hQ π

omit [Nonempty Θ] [DecidableEq Θ] [MeasurableSingletonClass Θ] in
/-- Information is the gain of the negative-entropy posterior potential. -/
theorem causalInformationObjective_eq_negEntropyPotential (α : Θ → ℝ)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) :
    causalInformationObjective α Qs hQ π =
      causalPotentialObjective (fun p => -ent p) α Qs hQ π := by
  simp only [causalInformationObjective, causalPotentialObjective,
    causalTerminalPotential, integral_neg]
  ring

theorem causalInformationObjective_le_priorEntropy (α : Θ → ℝ) (hα : IsDist α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) :
    causalInformationObjective α Qs hQ π ≤ ent α := by
  rw [causalInformationObjective_eq_negEntropyPotential]
  simpa using causalPotentialObjective_le_full (fun p => -ent p)
    continuous_ent.neg.continuousOn strictConvexOn_neg_ent_simplex.convexOn
    α hα Qs hQ π

/-- Prior entropy is reached exactly when the particular policy identifies;
existence of another identifying policy is not needed for this equivalence. -/
theorem causalInformationObjective_eq_priorEntropy_iff_exactlyIdentifies
    (α : Θ → ℝ) (hα : IsDist α) (hfs : FullSupport α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) :
    causalInformationObjective α Qs hQ π = ent α ↔ CausalExactlyIdentifies Qs hQ π := by
  rw [causalInformationObjective_eq_negEntropyPotential]
  simpa using causalPotentialObjective_eq_full_iff_exactlyIdentifies (fun p => -ent p)
    continuous_ent.neg.continuousOn strictConvexOn_neg_ent_simplex
    α hα hfs Qs hQ π

theorem causalInformationObjective_isGreatest_priorEntropy_iff_attainable
    (α : Θ → ℝ) (hα : IsDist α) (hfs : FullSupport α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ)) :
    IsGreatest (Set.range (causalInformationObjective α Qs hQ)) (ent α) ↔
      CausalFullRevelationAttainable Qs hQ := by
  have heq : causalInformationObjective α Qs hQ =
      causalPotentialObjective (fun p => -ent p) α Qs hQ :=
    funext (causalInformationObjective_eq_negEntropyPotential α Qs hQ)
  rw [heq]
  simpa using causalPotentialObjective_isGreatest_full_iff_attainable (fun p => -ent p)
    continuous_ent.neg.continuousOn strictConvexOn_neg_ent_simplex α hα hfs Qs hQ

/-- Item 1 of the finite attained-top objective theorem, on the actual causal
class: complete information maximizers are exactly identifying policies. -/
theorem causalInformationObjective_maximizer_iff_exactlyIdentifies
    (α : Θ → ℝ) (hα : IsDist α) (hfs : FullSupport α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hattain : CausalFullRevelationAttainable Qs hQ) (π : ValidCausalPolicy A O) :
    (∀ σ, causalInformationObjective α Qs hQ σ ≤ causalInformationObjective α Qs hQ π) ↔
      CausalExactlyIdentifies Qs hQ π := by
  simp_rw [causalInformationObjective_eq_negEntropyPotential]
  exact causalPotentialObjective_maximizer_iff_exactlyIdentifies (fun p => -ent p)
    continuous_ent.neg.continuousOn strictConvexOn_neg_ent_simplex α hα hfs Qs hQ hattain π

theorem causalInformationObjective_argmax_eq_nativelySufficient
    (α : Θ → ℝ) (hα : IsDist α) (hfs : FullSupport α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hattain : CausalFullRevelationAttainable Qs hQ) :
    {π | ∀ σ, causalInformationObjective α Qs hQ σ ≤ causalInformationObjective α Qs hQ π} =
      {π | CausalNativelySufficient Qs π} := by
  ext π
  exact (causalInformationObjective_maximizer_iff_exactlyIdentifies
    α hα hfs Qs hQ hattain π).trans
    (causalNativelySufficient_iff_exactlyIdentifies_of_attainable Qs hQ hattain π).symm

omit [Nonempty Θ] [DecidableEq Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ]
  [Nonempty A] [Nonempty O] [MeasurableSpace A] [MeasurableSpace O]
  [MeasurableSingletonClass A] [MeasurableSingletonClass O] in
/-- The empty prefix carries no information, including on singleton classes. -/
theorem causalPrefixInformation_zero (α : Θ → ℝ) (hα : IsDist α)
    (Qs : Θ → CausalResponse A O) (π : ValidCausalPolicy A O) :
    causalPrefixInformation α Qs π 0 = 0 := by
  change ent α - finiteBayesPotential ent α (causalFiniteExperiment π.1 Qs 0) = 0
  rw [causalFiniteBayesPotential_zero ent α hα π.1 Qs, sub_self]

omit [Nonempty Θ] [DecidableEq Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ]
  [Nonempty A] [Nonempty O] [MeasurableSpace A] [MeasurableSpace O]
  [MeasurableSingletonClass A] [MeasurableSingletonClass O] in
/-- Exact finite Bayesian refinement makes the information curve monotone.
No full support or full-revelation hypothesis is involved. -/
theorem monotone_causalPrefixInformation (α : Θ → ℝ) (hα : IsDist α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) : Monotone (causalPrefixInformation α Qs π) := by
  classical
  apply monotone_nat_of_le_succ
  intro t
  exact finiteBayesInformation_mono_refinement α
    (causalFiniteExperiment π.1 Qs (t + 1)) (causalFiniteExperiment π.1 Qs t) Fin.init hα.1
    (fun θ w => (causalFiniteExperiment_valid π.1 π.2 Qs hQ (t + 1) θ).1 w)
    (fun θ w => (causalFiniteExperiment_valid π.1 π.2 Qs hQ t θ).1 w)
    (causalFiniteExperiment_isFiniteRefinement π.1 π.2 Qs hQ t)

/-- The monotone prefix information converges to the entropy-form terminal
information for every policy, including nonidentifying policies. -/
theorem tendsto_causalPrefixInformation (α : Θ → ℝ) (hα : IsDist α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) :
    Tendsto (causalPrefixInformation α Qs π) atTop
      (𝓝 (causalInformationObjective α Qs hQ π)) := by
  exact (tendsto_causalBayesPotential α hα Qs hQ π ent continuous_ent.continuousOn).const_sub (ent α)

theorem causalPrefixInformation_le_terminal (α : Θ → ℝ) (hα : IsDist α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) (t : ℕ) :
    causalPrefixInformation α Qs π t ≤ causalInformationObjective α Qs hQ π :=
  (monotone_causalPrefixInformation α hα Qs hQ π).ge_of_tendsto
    (tendsto_causalPrefixInformation α hα Qs hQ π) t

/-- The complete undiscounted information objective is the actual supremum
of the finite-prefix information curve, not merely an upper bound. -/
theorem iSup_causalPrefixInformation_eq_terminal (α : Θ → ℝ) (hα : IsDist α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) :
    (⨆ t, causalPrefixInformation α Qs π t) = causalInformationObjective α Qs hQ π :=
  iSup_eq_of_forall_le_of_tendsto (causalPrefixInformation_le_terminal α hα Qs hQ π)
    (tendsto_causalPrefixInformation α hα Qs hQ π)

theorem causalInformationObjective_nonneg (α : Θ → ℝ) (hα : IsDist α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) : 0 ≤ causalInformationObjective α Qs hQ π := by
  simpa only [causalPrefixInformation_zero α hα Qs π] using
    causalPrefixInformation_le_terminal α hα Qs hQ π 0

omit [Nonempty Θ] [DecidableEq Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ]
  [Nonempty A] [Nonempty O] [MeasurableSpace A] [MeasurableSpace O]
  [MeasurableSingletonClass A] [MeasurableSingletonClass O] in
theorem causalPrefixInformation_nonneg (α : Θ → ℝ) (hα : IsDist α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) (t : ℕ) : 0 ≤ causalPrefixInformation α Qs π t := by
  simpa only [causalPrefixInformation_zero α hα Qs π] using
    (monotone_causalPrefixInformation α hα Qs hQ π) (Nat.zero_le t)

theorem causalPrefixInformation_le_priorEntropy (α : Θ → ℝ) (hα : IsDist α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) (t : ℕ) : causalPrefixInformation α Qs π t ≤ ent α :=
  (causalPrefixInformation_le_terminal α hα Qs hQ π t).trans
    (causalInformationObjective_le_priorEntropy α hα Qs hQ π)

end IdExp
