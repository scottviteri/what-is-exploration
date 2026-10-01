import Formal.CrossingDecisionWitnesses
import Formal.AbsorbingExperiment
import Formal.CausalBehaviorCapability

/-!
# Crossing partitions on actual policy records

The only informative observation is the root answer. Every valid policy,
including arbitrary randomized continuations, therefore has the statistical
content of the recorded mixture with weight `π [] 0`. Its literal native
audit at any positive collection and target horizons is `max r (1-r) / 2`.
The same two bounded decisions recover this audit. No relation between the
two horizons, positive mixture weights, or attainable revelation is needed.
-/

namespace IdExp

open Finset
noncomputable section

namespace Crossing

def rootTests (a : Fin 2) : FiniteExperiment (Fin 4) (Fin 2) :=
  if a = 0 then testA else testB

theorem rootTests_valid (a : Fin 2) : IsFiniteExperiment (rootTests a) := by
  unfold rootTests
  split_ifs <;> first | exact testA_valid | exact testB_valid

def response : Fin 4 → CausalResponse (Fin 2) (Fin 2) :=
  absorbingResponse 0 rootTests

theorem response_valid (θ : Fin 4) : IsCausalResponse (response θ) :=
  absorbingResponse_valid 0 rootTests rootTests_valid θ

def behavior (θ : Fin 4) : CausalBehavior (Fin 2) (Fin 2) :=
  CausalBehavior.ofResponse (response θ) (response_valid θ)

theorem behavior_prefix (π : CausalPolicy (Fin 2) (Fin 2)) (t : ℕ) :
    causalBehaviorFiniteExperiment π behavior t = causalFiniteExperiment π response t :=
  causalBehaviorFiniteExperiment_ofResponse π response response_valid t

theorem rootProbability_mem (π : ValidCausalPolicy (Fin 2) (Fin 2)) :
    π.val [] 0 ∈ Set.Icc (0 : ℝ) 1 := by
  have h := (π.property []).2
  rw [Fin.sum_univ_two] at h
  exact ⟨(π.property []).1 0, by linarith [(π.property []).1 1]⟩

theorem root_eq_recordedMixture (π : ValidCausalPolicy (Fin 2) (Fin 2)) :
    absorbingRootExperiment rootTests π.val = recordedMixture (π.val [] 0) := by
  have h := (π.property []).2
  rw [Fin.sum_univ_two] at h
  have h1 : π.val [] 1 = 1 - π.val [] 0 := by linarith
  funext θ z
  rcases z with ⟨a, o⟩
  fin_cases a <;> simp [absorbingRootExperiment, rootTests, recordedMixture, h1]

theorem prefix_equiv (π : ValidCausalPolicy (Fin 2) (Fin 2)) (t : ℕ) :
    FiniteBlackwellLE (causalFiniteExperiment π.val response (t + 1))
        (recordedMixture (π.val [] 0)) ∧
      FiniteBlackwellLE (recordedMixture (π.val [] 0))
        (causalFiniteExperiment π.val response (t + 1)) := by
  simpa only [root_eq_recordedMixture, response] using
    absorbingCausalExperiment_root_blackwell_equiv 0 rootTests rootTests_valid
      π.val π.property t

set_option maxHeartbeats 800000 in
theorem recorded_native_deficiency {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (n : ℕ) (τ : CausalPlan (Fin 2) (Fin 2) (n + 1)) :
    finiteDeficiency (recordedMixture r)
        (causalPlanObservationExperiment (n + 1) τ response) =
      if absorbingPlanRoot n τ = 0 then (1 - r) / 2 else r / 2 := by
  obtain ⟨hA, hB⟩ := absorbingNativeTest_all_depths_blackwell_equiv
    0 rootTests rootTests_valid n τ
  have he := finiteDeficiency_eq_of_target_blackwellEquiv (recordedMixture r)
    (causalPlanObservationExperiment (n + 1) τ response)
    (rootTests (absorbingPlanRoot n τ)) (recordedMixture_valid hr0 hr1)
    (causalPlanObservationExperiment_valid _ _ _ response_valid)
    (rootTests_valid _) hA hB
  apply he.trans
  by_cases h : absorbingPlanRoot n τ = 0
  · simpa only [rootTests, h, if_true] using recordedMixture_deficiency_A hr0 hr1
  · simpa only [rootTests, h, if_false] using recordedMixture_deficiency_B hr0 hr1

theorem recorded_native_audit {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (n : ℕ) :
    causalNativeDeficiency (recordedMixture r) response (n + 1) =
      recordedMixtureAudit r := by
  have hformula : recordedMixtureAudit r = max ((1 - r) / 2) (r / 2) := by
    unfold recordedMixtureAudit
    rw [recordedMixture_deficiency_A hr0 hr1, recordedMixture_deficiency_B hr0 hr1]
  rw [hformula]
  apply le_antisymm
  · apply Finset.sup'_le
    intro τ _
    rw [recorded_native_deficiency hr0 hr1]
    split_ifs <;> first | exact le_max_left _ _ | exact le_max_right _ _
  · apply max_le
    · have h := finiteDeficiency_causalPlan_le_native (recordedMixture r)
        response (n + 1) (fun _ => 0)
      simpa [recorded_native_deficiency hr0 hr1, absorbingPlanRoot] using h
    · have h := finiteDeficiency_causalPlan_le_native (recordedMixture r)
        response (n + 1) (fun _ => 1)
      simpa [recorded_native_deficiency hr0 hr1, absorbingPlanRoot] using h

theorem native_audit_upTo (π : ValidCausalPolicy (Fin 2) (Fin 2)) (t n : ℕ) :
    causalNativeDeficiencyUpTo (causalFiniteExperiment π.val response (t + 1))
      response (n + 1) = recordedMixtureAudit (π.val [] 0) := by
  rw [causalNativeDeficiencyUpTo_eq_terminal _
    (causalFiniteExperiment_valid _ π.property _ response_valid _) _ response_valid]
  have he : causalNativeDeficiency (causalFiniteExperiment π.val response (t + 1))
      response (n + 1) = causalNativeDeficiency (recordedMixture (π.val [] 0))
      response (n + 1) := by
    unfold causalNativeDeficiency
    congr 1
    funext τ
    exact finiteDeficiency_eq_of_source_blackwellEquiv _ _ _
      (prefix_equiv π t).1 (prefix_equiv π t).2
  rw [he, recorded_native_audit (rootProbability_mem π).1 (rootProbability_mem π).2]

theorem native_audit_eq (π : ValidCausalPolicy (Fin 2) (Fin 2)) (t n : ℕ) :
    causalNativeDeficiencyUpTo (causalFiniteExperiment π.val response (t + 1))
      response (n + 1) = (1 / 2) * max (π.val [] 0) (1 - π.val [] 0) := by
  rw [native_audit_upTo, recordedMixtureAudit_eq (rootProbability_mem π).1
    (rootProbability_mem π).2]

theorem native_audit_minimizers (π : ValidCausalPolicy (Fin 2) (Fin 2)) (t n : ℕ) :
    1 / 4 ≤ causalNativeDeficiencyUpTo (causalFiniteExperiment π.val response (t + 1))
      response (n + 1) ∧
    (causalNativeDeficiencyUpTo (causalFiniteExperiment π.val response (t + 1))
      response (n + 1) = 1 / 4 ↔ π.val [] 0 = 1 / 2) := by
  rw [native_audit_upTo]
  exact ⟨recordedMixtureAudit_ge_quarter (rootProbability_mem π).1 (rootProbability_mem π).2,
    recordedMixtureAudit_eq_quarter_iff (rootProbability_mem π).1 (rootProbability_mem π).2⟩

theorem prefix_value (π : ValidCausalPolicy (Fin 2) (Fin 2)) (t : ℕ)
    (α : Fin 4 → ℝ) (u : Fin 4 → Fin 2 → ℝ) :
    finiteBayesValue (causalFiniteExperiment π.val response (t + 1)) α u =
      finiteBayesValue (recordedMixture (π.val [] 0)) α u := by
  obtain ⟨h1, h2⟩ := prefix_equiv π t
  exact le_antisymm (finiteBayesValue_mono_of_finiteBlackwellLE _ _ h1 α u)
    (finiteBayesValue_mono_of_finiteBlackwellLE _ _ h2 α u)

/-- Both reference values are one, attained by the corresponding pure root
measurement. These two bounded tasks recover the full positive-depth audit. -/
theorem native_audit_eq_two_regrets (π : ValidCausalPolicy (Fin 2) (Fin 2)) (t n : ℕ) :
    causalNativeDeficiencyUpTo (causalFiniteExperiment π.val response (t + 1))
      response (n + 1) =
      max (1 - finiteBayesValue (causalFiniteExperiment π.val response (t + 1)) priorA askA)
        (1 - finiteBayesValue (causalFiniteExperiment π.val response (t + 1)) priorB askB) := by
  rw [native_audit_upTo, prefix_value, prefix_value,
    value_mixture_priorA (rootProbability_mem π).1 (rootProbability_mem π).2,
    value_mixture_priorB (rootProbability_mem π).1 (rootProbability_mem π).2]
  unfold recordedMixtureAudit
  rw [recordedMixture_deficiency_A (rootProbability_mem π).1 (rootProbability_mem π).2,
    recordedMixture_deficiency_B (rootProbability_mem π).1 (rootProbability_mem π).2]
  congr 1 <;> ring


/-- Every mixing weight is realized by a valid policy. Its later rows have
no effect on the statistical content, though they remain part of the record. -/
def policy {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : ValidCausalPolicy (Fin 2) (Fin 2) :=
  ⟨fun _ => ![r, 1 - r], fun _ => crossingWeights_isDist hr0 hr1⟩

theorem balanced_audit (t n : ℕ) :
    causalNativeDeficiencyUpTo
      (causalFiniteExperiment (policy (r := 1 / 2) (by norm_num) (by norm_num)).val
        response (t + 1)) response (n + 1) = 1 / 4 := by
  rw [native_audit_upTo]
  exact recordedMixtureAudit_half

theorem prefix_potential (π : ValidCausalPolicy (Fin 2) (Fin 2)) (t : ℕ)
    (α : Fin 4 → ℝ) (hα : IsDist α) (Φ : (Fin 4 → ℝ) → ℝ)
    (hΦ : ConvexOn ℝ (stdSimplex ℝ (Fin 4)) Φ) :
    finiteBayesPotential Φ α (causalFiniteExperiment π.val response (t + 1)) =
      finiteBayesPotential Φ α (recordedMixture (π.val [] 0)) := by
  obtain ⟨⟨G, hG, heG⟩, ⟨H, hH, heH⟩⟩ := prefix_equiv π t
  apply le_antisymm
  · have h := finiteBayesPotential_garble_le α hα _
      (recordedMixture_valid (rootProbability_mem π).1 (rootProbability_mem π).2) G hG Φ hΦ
    simpa only [heG] using h
  · have h := finiteBayesPotential_garble_le α hα _
      (causalFiniteExperiment_valid _ π.property _ response_valid _) H hH Φ hΦ
    simpa only [heH] using h

theorem prefix_information (π : ValidCausalPolicy (Fin 2) (Fin 2)) (t : ℕ)
    (α : Fin 4 → ℝ) (hα : IsDist α) :
    finiteBayesInformation α (causalFiniteExperiment π.val response (t + 1)) =
      finiteBayesInformation α (recordedMixture (π.val [] 0)) := by
  have h := prefix_potential π t α hα (fun p => -ent p)
    strictConvexOn_neg_ent_simplex.convexOn
  simp only [finiteBayesPotential, mul_neg, Finset.sum_neg_distrib] at h
  unfold finiteBayesInformation finiteBayesPotential
  linarith

theorem prefix_quadratic (π : ValidCausalPolicy (Fin 2) (Fin 2)) (t : ℕ)
    (α : Fin 4 → ℝ) (hα : IsDist α) :
    quadraticPosteriorScore α (causalFiniteExperiment π.val response (t + 1)) =
      quadraticPosteriorScore α (recordedMixture (π.val [] 0)) := by
  unfold quadraticPosteriorScore
  rw [prefix_potential π t α hα _ convexOn_posteriorQuadraticPotential]

theorem information_optimizers (π : ValidCausalPolicy (Fin 2) (Fin 2)) (t : ℕ) :
    finiteBayesInformation crossingPrior (causalFiniteExperiment π.val response (t + 1)) ≤
      finiteBayesInformation crossingPrior (recordedMixture 0) ∧
    (finiteBayesInformation crossingPrior (causalFiniteExperiment π.val response (t + 1)) =
      finiteBayesInformation crossingPrior (recordedMixture 0) ↔ π.val [] 0 = 0) := by
  rw [prefix_information π t crossingPrior crossingPrior_isDist]
  exact information_selects_B (rootProbability_mem π).1 (rootProbability_mem π).2

theorem quadratic_optimizers (π : ValidCausalPolicy (Fin 2) (Fin 2)) (t : ℕ) :
    quadraticPosteriorScore crossingPrior (causalFiniteExperiment π.val response (t + 1)) ≤
      quadraticPosteriorScore crossingPrior (recordedMixture 1) ∧
    (quadraticPosteriorScore crossingPrior (causalFiniteExperiment π.val response (t + 1)) =
      quadraticPosteriorScore crossingPrior (recordedMixture 1) ↔ π.val [] 0 = 1) := by
  rw [prefix_quadratic π t crossingPrior crossingPrior_isDist]
  exact quadratic_selects_A (rootProbability_mem π).1 (rootProbability_mem π).2

end Crossing

/-- Paper-facing name for the actual all-policy, all-positive-depth audit. -/
theorem crossingCausal_native_audit_eq (π : ValidCausalPolicy (Fin 2) (Fin 2)) (t n : ℕ) :
    causalNativeDeficiencyUpTo (causalFiniteExperiment π.val Crossing.response (t + 1))
      Crossing.response (n + 1) = (1 / 2) * max (π.val [] 0) (1 - π.val [] 0) :=
  Crossing.native_audit_eq π t n

/-- Two fixed bounded decision tasks recover that literal native audit. -/
theorem crossingCausal_native_audit_eq_two_regrets
    (π : ValidCausalPolicy (Fin 2) (Fin 2)) (t n : ℕ) :
    causalNativeDeficiencyUpTo (causalFiniteExperiment π.val Crossing.response (t + 1))
      Crossing.response (n + 1) =
      max (1 - finiteBayesValue (causalFiniteExperiment π.val Crossing.response (t + 1)) priorA askA)
        (1 - finiteBayesValue (causalFiniteExperiment π.val Crossing.response (t + 1)) priorB askB) :=
  Crossing.native_audit_eq_two_regrets π t n

end
end IdExp
