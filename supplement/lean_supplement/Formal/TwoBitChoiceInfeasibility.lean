import Formal.CrossingCausal

/-!
# Two irreversible bit reads with no natively sufficient policy

Four deterministic worlds carry two unrestricted bits. The first action returns
one selected bit; every later observation is zero. Full action-observation
records and arbitrary randomized history-dependent continuation policies are
included. A root probability s of reading the first bit leaves exact target
errors (1-s)/2 and s/2 at every positive collection time. No prior is used.
-/

namespace IdExp.TwoBitChoice
open Finset
noncomputable section

/-- Worlds 00, 01, 10, 11, in that order. -/
def firstBit : Fin 4 → Fin 2 := ![0, 0, 1, 1]
def secondBit : Fin 4 → Fin 2 := ![0, 1, 0, 1]

/-- The pure tests as experiments on the four worlds. -/
def testA : FiniteExperiment (Fin 4) (Fin 2) := deterministicExperiment firstBit
def testB : FiniteExperiment (Fin 4) (Fin 2) := deterministicExperiment secondBit

theorem testA_valid : IsFiniteExperiment testA := by
  intro θ
  refine ⟨fun s => by unfold testA deterministicExperiment; split_ifs <;> norm_num, ?_⟩
  fin_cases θ <;> simp [testA, deterministicExperiment, firstBit, Fin.sum_univ_two]

theorem testB_valid : IsFiniteExperiment testB := by
  intro θ
  refine ⟨fun s => by unfold testB deterministicExperiment; split_ifs <;> norm_num, ?_⟩
  fin_cases θ <;> simp [testB, deterministicExperiment, secondBit, Fin.sum_univ_two]

/-- Run `A` with probability `r` (label `0`), otherwise `B` (label `1`), and
record the label with the result. -/
def recordedMixture (r : ℝ) : FiniteExperiment (Fin 4) (Fin 2 × Fin 2) :=
  fun θ z => if z.1 = 0 then r * testA θ z.2 else (1 - r) * testB θ z.2

theorem recordedMixture_valid {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    IsFiniteExperiment (recordedMixture r) := by
  intro θ
  constructor
  · intro z
    unfold recordedMixture
    split_ifs
    · exact mul_nonneg hr0 ((testA_valid θ).1 _)
    · exact mul_nonneg (by linarith) ((testB_valid θ).1 _)
  · unfold recordedMixture
    rw [Fintype.sum_prod_type, Fin.sum_univ_two]
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    simp only [h10, ↓reduceIte, ← Finset.mul_sum, (testA_valid θ).2, (testB_valid θ).2]
    ring

/-! ## Mixtures with a recorded label: total variation and decoding are linear -/

/-- Recording the label makes total variation the weighted sum of the pure
tests' total variations. -/
theorem finiteTV_recordedMixture {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (θ θ' : Fin 4) :
    finiteTV (recordedMixture r θ) (recordedMixture r θ') =
      r * finiteTV (testA θ) (testA θ') + (1 - r) * finiteTV (testB θ) (testB θ') := by
  unfold finiteTV recordedMixture
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [h10, ↓reduceIte]
  have hA : ∀ s, |r * testA θ s - r * testA θ' s| = r * |testA θ s - testA θ' s| := fun s => by
    rw [← mul_sub, abs_mul, abs_of_nonneg hr0]
  have hB : ∀ s, |(1 - r) * testB θ s - (1 - r) * testB θ' s| =
      (1 - r) * |testB θ s - testB θ' s| := fun s => by
    rw [← mul_sub, abs_mul, abs_of_nonneg (by linarith)]
  simp only [hA, hB, ← Finset.mul_sum]
  ring

theorem decisionLaw_liftDecoderA (r : ℝ) (G : Fin 2 → Fin 2 → ℝ) (θ : Fin 4) :
    finiteDecisionLaw (recordedMixture r) (liftDecoderA G) θ =
      fun a => r * testA θ a + (1 - r) * finiteDecisionLaw testB G θ a := by
  funext a
  unfold finiteDecisionLaw recordedMixture liftDecoderA
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [h10, ↓reduceIte, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, Finset.mul_sum]
  ring_nf

theorem decisionLaw_liftDecoderB (r : ℝ) (G : Fin 2 → Fin 2 → ℝ) (θ : Fin 4) :
    finiteDecisionLaw (recordedMixture r) (liftDecoderB G) θ =
      fun b => (1 - r) * testB θ b + r * finiteDecisionLaw testA G θ b := by
  funext b
  unfold finiteDecisionLaw recordedMixture liftDecoderB
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  simp only [h10, h01, ↓reduceIte, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, Finset.mul_sum]
  ring_nf

/-! ## The pure decoders and their errors -/

/-- The missing first bit is guessed fairly. -/
def decodeBA : Fin 2 → Fin 2 → ℝ := fun _ _ => 1 / 2

/-- The missing second bit is guessed fairly. -/
def decodeAB : Fin 2 → Fin 2 → ℝ := fun _ _ => 1 / 2

theorem decodeBA_stochastic : decodeBA ∈ stochasticRules (Fin 2) (Fin 2) := by
  intro o _
  refine ⟨fun a => by norm_num [decodeBA], ?_⟩
  simp [decodeBA]

theorem decodeAB_stochastic : decodeAB ∈ stochasticRules (Fin 2) (Fin 2) := by
  intro o _
  refine ⟨fun b => by norm_num [decodeAB], ?_⟩
  simp [decodeAB]

theorem decodeBA_error (θ : Fin 4) : finiteTV (finiteDecisionLaw testB decodeBA θ) (testA θ) ≤ 1 / 2 := by
  fin_cases θ <;>
    simp [finiteTV, finiteDecisionLaw, testA, testB, deterministicExperiment, firstBit, secondBit,
      decodeBA, Fin.sum_univ_two] <;> norm_num

theorem decodeAB_error (θ : Fin 4) : finiteTV (finiteDecisionLaw testA decodeAB θ) (testB θ) ≤ 1 / 2 := by
  fin_cases θ <;>
    simp [finiteTV, finiteDecisionLaw, testA, testB, deterministicExperiment, firstBit, secondBit,
      decodeAB, Fin.sum_univ_two] <;> norm_num

/-! ## Pairwise separations -/

theorem testA_tv_00_10 : finiteTV (testA 0) (testA 2) = 1 := by
  simp [finiteTV, testA, deterministicExperiment, firstBit, Fin.sum_univ_two]; norm_num

theorem testB_tv_00_10 : finiteTV (testB 0) (testB 2) = 0 := by
  simp [finiteTV, testB, deterministicExperiment, secondBit, Fin.sum_univ_two]

theorem testA_tv_00_01 : finiteTV (testA 0) (testA 1) = 0 := by
  simp [finiteTV, testA, deterministicExperiment, firstBit, Fin.sum_univ_two]

theorem testB_tv_00_01 : finiteTV (testB 0) (testB 1) = 1 := by
  simp [finiteTV, testB, deterministicExperiment, secondBit, Fin.sum_univ_two]; norm_num

/-! ## Exact deficiencies -/

/-- `δ(M_r, A) = (1 − r)/2`. -/
theorem recordedMixture_deficiency_A {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    finiteDeficiency (recordedMixture r) testA = (1 - r) / 2 := by
  apply le_antisymm
  · apply finiteDeficiency_le_of_decoder _ _ (liftDecoderA decodeBA)
      (liftDecoderA_stochastic decodeBA decodeBA_stochastic)
    intro θ
    change finiteTV (finiteDecisionLaw (recordedMixture r) (liftDecoderA decodeBA) θ) (testA θ) ≤ _
    rw [decisionLaw_liftDecoderA, finiteTV_mix_left _ _ hr1]
    have := decodeBA_error θ
    nlinarith
  · have h := finiteDeficiency_pairwise_lower (recordedMixture r) testA
      (recordedMixture_valid hr0 hr1) testA_valid 0 2
    rw [testA_tv_00_10, finiteTV_recordedMixture hr0 hr1, testA_tv_00_10, testB_tv_00_10] at h
    linarith

/-- `δ(M_r, B) = r/2`. -/
theorem recordedMixture_deficiency_B {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    finiteDeficiency (recordedMixture r) testB = r / 2 := by
  apply le_antisymm
  · apply finiteDeficiency_le_of_decoder _ _ (liftDecoderB decodeAB)
      (liftDecoderB_stochastic decodeAB decodeAB_stochastic)
    intro θ
    change finiteTV (finiteDecisionLaw (recordedMixture r) (liftDecoderB decodeAB) θ) (testB θ) ≤ _
    rw [decisionLaw_liftDecoderB]
    have hmix := finiteTV_mix_left (testB θ) (finiteDecisionLaw testA decodeAB θ)
      (r := 1 - r) (by linarith)
    simp only [sub_sub_cancel] at hmix
    rw [hmix]
    have := decodeAB_error θ
    nlinarith
  · have h := finiteDeficiency_pairwise_lower (recordedMixture r) testB
      (recordedMixture_valid hr0 hr1) testB_valid 0 1
    rw [testB_tv_00_01, finiteTV_recordedMixture hr0 hr1, testA_tv_00_01, testB_tv_00_01] at h
    linarith


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
    π.val [] 0 ∈ Set.Icc (0 : ℝ) 1 := Crossing.rootProbability_mem π

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


/-- Every positive full record has the same target errors as its recorded root. -/
theorem prefix_target_errors (π : ValidCausalPolicy (Fin 2) (Fin 2)) (t : ℕ) :
    finiteDeficiency (causalFiniteExperiment π.val response (t + 1)) testA =
        (1 - π.val [] 0) / 2 ∧
    finiteDeficiency (causalFiniteExperiment π.val response (t + 1)) testB =
        π.val [] 0 / 2 := by
  constructor
  · rw [finiteDeficiency_eq_of_source_blackwellEquiv _
      (recordedMixture (π.val [] 0)) _ (prefix_equiv π t).1 (prefix_equiv π t).2]
    exact recordedMixture_deficiency_A (rootProbability_mem π).1 (rootProbability_mem π).2
  · rw [finiteDeficiency_eq_of_source_blackwellEquiv _
      (recordedMixture (π.val [] 0)) _ (prefix_equiv π t).1 (prefix_equiv π t).2]
    exact recordedMixture_deficiency_B (rootProbability_mem π).1 (rootProbability_mem π).2

/-- The native collector that selects one bit; later choices are immaterial. -/
def readPolicy (a : Fin 2) : ValidCausalPolicy (Fin 2) (Fin 2) :=
  ⟨causalPolicyOfPlan 1 (fun _ => a), isCausalPolicy_causalPolicyOfPlan 1 (fun _ => a)⟩

/-- The full action-observation target is equivalent to the selected bit. -/
theorem read_prefix_equiv (a : Fin 2) (n : ℕ) :
    FiniteBlackwellLE
      (causalFiniteExperiment (readPolicy a).val response (n + 1)) (rootTests a) ∧
    FiniteBlackwellLE (rootTests a)
      (causalFiniteExperiment (readPolicy a).val response (n + 1)) := by
  obtain ⟨hA, hB⟩ := absorbingCausalExperiment_root_blackwell_equiv 0 rootTests
    rootTests_valid (readPolicy a).val (readPolicy a).property n
  obtain ⟨hC, hD⟩ := absorbingPlanRoot_blackwell_equiv rootTests 0 (fun _ => a)
  exact ⟨finiteBlackwellLE_trans hA hC, finiteBlackwellLE_trans hD hB⟩

/-- Paper-facing equality against the one-step full recorded native targets. -/
theorem prefix_record_target_errors (π : ValidCausalPolicy (Fin 2) (Fin 2)) (t : ℕ) :
    finiteDeficiency (causalFiniteExperiment π.val response (t + 1))
        (causalFiniteExperiment (readPolicy 0).val response 1) = (1 - π.val [] 0) / 2 ∧
    finiteDeficiency (causalFiniteExperiment π.val response (t + 1))
        (causalFiniteExperiment (readPolicy 1).val response 1) = π.val [] 0 / 2 := by
  have htarget (a : Fin 2) := finiteDeficiency_eq_of_target_blackwellEquiv
    (causalFiniteExperiment π.val response (t + 1))
    (causalFiniteExperiment (readPolicy a).val response 1) (rootTests a)
    (causalFiniteExperiment_valid _ π.property _ response_valid (t + 1))
    (causalFiniteExperiment_valid _ (readPolicy a).property _ response_valid 1)
    (rootTests_valid a) (read_prefix_equiv a 0).1 (read_prefix_equiv a 0).2
  constructor
  · rw [htarget 0]
    simpa [rootTests] using (prefix_target_errors π t).1
  · rw [htarget 1]
    simpa [rootTests] using (prefix_target_errors π t).2

/-- The exact errors also hold against every positive-depth native intervention. -/
theorem prefix_native_deficiency (π : ValidCausalPolicy (Fin 2) (Fin 2)) (t n : ℕ)
    (τ : CausalPlan (Fin 2) (Fin 2) (n + 1)) :
    finiteDeficiency (causalFiniteExperiment π.val response (t + 1))
        (causalPlanObservationExperiment (n + 1) τ response) =
      if absorbingPlanRoot n τ = 0 then (1 - π.val [] 0) / 2 else π.val [] 0 / 2 := by
  rw [finiteDeficiency_eq_of_source_blackwellEquiv _
    (recordedMixture (π.val [] 0)) _ (prefix_equiv π t).1 (prefix_equiv π t).2]
  exact recorded_native_deficiency (rootProbability_mem π).1 (rootProbability_mem π).2 n τ

/-- Neither randomization nor later history-dependent actions make both bit targets
asymptotically simulable. -/
theorem no_natively_sufficient_policy (π : ValidCausalPolicy (Fin 2) (Fin 2)) :
    ¬ CausalNativelySufficient response π := by
  intro h
  obtain ⟨T, hT⟩ := h 1 (1 / 4) (by norm_num)
  have hfirst := hT (T + 1) (by omega) (fun _ => 0)
  have hsecond := hT (T + 1) (by omega) (fun _ => 1)
  rw [prefix_native_deficiency π T 0] at hfirst hsecond
  norm_num [absorbingPlanRoot] at hfirst hsecond
  linarith

/-- Therefore the finitary process preorder has no greatest policy. -/
theorem no_finitarily_greatest_policy (π : ValidCausalPolicy (Fin 2) (Fin 2)) :
    ¬ CausalFinitarilyGreatest response π := by
  rw [← causalNativelySufficient_iff_finitarilyGreatest response response_valid]
  exact no_natively_sufficient_policy π

#print axioms prefix_target_errors
#print axioms prefix_record_target_errors
#print axioms prefix_native_deficiency
#print axioms no_natively_sufficient_policy
#print axioms no_finitarily_greatest_policy

end
end IdExp.TwoBitChoice
