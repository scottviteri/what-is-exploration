import Formal.KnownNoiseMisranking

/-!
# First-visit counts strictly prefer an uninformative branch

The initial action irreversibly selects READ or NOISE. READ returns the fixed
unknown bit twice; NOISE returns two independent uniform four-symbol labels.
Later actions are unrestricted and retained in the record, but cannot change
branches. Total first-visit reward counts distinct observed labels. Its exact
expectation is `7/4 - 3/4 * P(READ)`, for every randomized causal policy.
Consequently every optimum is class-independent, and has deficiency `1/2`
against the available revealing record; the reverse deficiency is zero.
-/

namespace IdExp.FirstVisitCount

open Finset
noncomputable section

abbrev World := Fin 2
abbrev Action := Fin 2
abbrev Observation := Fin 4

/-- The initial action selects the branch permanently. Normalized responses
are specified even at histories that have zero probability in a world. -/
def response (θ : World) : CausalResponse Action Observation
  | [], a, o => KnownNoise.response θ [] a o
  | (a₀, _) :: _, _, o => KnownNoise.response θ [] a₀ o

theorem response_valid (θ : World) : IsCausalResponse (response θ) := by
  intro h a
  cases h with
  | nil => exact KnownNoise.response_valid θ [] a
  | cons ao h => exact KnownNoise.response_valid θ [] ao.1

abbrev prior := KnownNoise.prior
abbrev purePolicy := KnownNoise.purePolicy

/-- A first visit earns one; a repeat earns zero. At budget two this is exactly
the number of distinct observed labels, without counting chosen actions. -/
def countReward (w : CausalFiniteTrace Action Observation 2) : ℝ :=
  if (w 0).2 = (w 1).2 then 1 else 2

def expectedCount (π : ValidCausalPolicy Action Observation) : ℝ :=
  ∑ θ, prior θ * ∑ w, causalFiniteExperiment π.1 response 2 θ w * countReward w

/-- The actual two-step trace probability includes both policy action factors. -/
theorem record_two (π : ValidCausalPolicy Action Observation) (θ : World)
    (w : CausalFiniteTrace Action Observation 2) :
    causalFiniteExperiment π.1 response 2 θ w =
      π.1 [] (w 0).1 * KnownNoise.response θ [] (w 0).1 (w 0).2 *
        (π.1 [w 0] (w 1).1 * KnownNoise.response θ [] (w 0).1 (w 1).2) := by
  simp [causalFiniteExperiment, causalTraceProb, causalTraceProbFrom,
    List.ofFn_succ, response]

/-- Summing the retained second action removes its normalized policy row.
This permits any dependence of that action on the first observed label. -/
theorem expected_observation_payoff (π : ValidCausalPolicy Action Observation)
    (θ : World) (u : Observation → Observation → ℝ) :
    (∑ w, causalFiniteExperiment π.1 response 2 θ w * u (w 0).2 (w 1).2) =
      ∑ a, ∑ o, π.1 [] a * KnownNoise.response θ [] a o *
        ∑ o', KnownNoise.response θ [] a o' * u o o' := by
  rw [← (finTwoArrowEquiv (Action × Observation)).symm.sum_comp]
  simp only [Fintype.sum_prod_type, record_two, finTwoArrowEquiv_symm_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro o _
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, (π.2 [(a, o)]).2]
  simp only [one_mul]

/-- Exact score for all stochastic, history-dependent policies. -/
theorem expectedCount_eq (π : ValidCausalPolicy Action Observation) :
    expectedCount π = 7 / 4 - 3 / 4 * π.1 [] 0 := by
  change (∑ θ, prior θ * ∑ w, causalFiniteExperiment π.1 response 2 θ w *
    (fun o o' : Observation => if o = o' then (1 : ℝ) else 2) (w 0).2 (w 1).2) = _
  simp_rw [expected_observation_payoff π (u := fun o o' => if o = o' then 1 else 2)]
  have hr : π.1 [] 0 + π.1 [] 1 = 1 := by
    simpa [Fin.sum_univ_succ] using (π.2 []).2
  norm_num [prior, KnownNoise.prior, KnownNoise.response, Fin.sum_univ_succ]
  norm_num only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_succ, Fin.val_ofNat]
  norm_num [show (2 : Fin 4).val = 2 from rfl, show (2 : Fin 3).val = 2 from rfl]
  linear_combination 7 / 4 * hr

/-- READ scores one, whereas NOISE scores seven quarters. -/
theorem pure_scores : expectedCount (purePolicy 0) = 1 ∧
    expectedCount (purePolicy 1) = 7 / 4 := by
  norm_num [expectedCount_eq, purePolicy, KnownNoise.purePolicy, detPolicy]

/-- Every optimum commits to NOISE, even when arbitrary policy randomization
and observation-dependent later actions are permitted. -/
theorem count_maximizers (π : ValidCausalPolicy Action Observation) :
    (∀ ρ : ValidCausalPolicy Action Observation, expectedCount ρ ≤ expectedCount π) ↔
      π.1 [] 0 = 0 := by
  constructor
  · intro h
    have hh := h (purePolicy 1)
    rw [expectedCount_eq, expectedCount_eq] at hh
    norm_num [purePolicy, KnownNoise.purePolicy, detPolicy] at hh
    linarith [(π.2 []).1 0]
  · intro hπ ρ
    rw [expectedCount_eq, expectedCount_eq, hπ]
    linarith [(ρ.2 []).1 0]

/-- The available policy that reveals the bit twice, including its actions. -/
def readRecord : FiniteExperiment World (CausalFiniteTrace Action Observation 2) :=
  causalFiniteExperiment (purePolicy 0).1 response 2

theorem readRecord_valid : IsFiniteExperiment readRecord :=
  causalFiniteExperiment_valid _ (purePolicy 0).2 response response_valid 2

theorem readRecord_pairTV : finiteTV (readRecord 0) (readRecord 1) = 1 := by
  unfold finiteTV readRecord
  rw [← (finTwoArrowEquiv (Action × Observation)).symm.sum_comp]
  simp_rw [record_two (purePolicy 0)]
  norm_num [finTwoArrowEquiv_symm_apply, Fintype.sum_prod_type,
    purePolicy, KnownNoise.purePolicy, detPolicy, KnownNoise.response, Fin.sum_univ_succ]

/-- At an optimal root choice, the entire retained record is world-independent,
including all subsequent policy randomization. -/
theorem noise_root_record_classIndependent (π : ValidCausalPolicy Action Observation)
    (hπ : π.1 [] 0 = 0) :
    ClassIndependentFiniteExperiment (causalFiniteExperiment π.1 response 2) := by
  intro θ θ'
  funext w
  rw [record_two, record_two]
  by_cases ha : (w 0).1 = 0
  · simp [ha, hπ]
  · simp [KnownNoise.response, ha]

/-- A first-visit-count optimum is strictly worse as reusable evidence. Both
deficiencies refer to literal finite causal records, not only observations. -/
theorem every_count_optimum_strictly_misranks
    (π : ValidCausalPolicy Action Observation)
    (hopt : ∀ ρ : ValidCausalPolicy Action Observation, expectedCount ρ ≤ expectedCount π) :
    π.1 [] 0 = 0 ∧
    finiteDeficiency readRecord (causalFiniteExperiment π.1 response 2) = 0 ∧
    finiteDeficiency (causalFiniteExperiment π.1 response 2) readRecord = 1 / 2 := by
  have hroot := (count_maximizers π).mp hopt
  have hclass := noise_root_record_classIndependent π hroot
  have hvalid := causalFiniteExperiment_valid π.1 π.2 response response_valid 2
  refine ⟨hroot, ?_, ?_⟩
  · apply le_antisymm
    · apply finiteDeficiency_le_of_decoder readRecord (causalFiniteExperiment π.1 response 2)
        (fun _ => causalFiniteExperiment π.1 response 2 0)
      · intro x _; exact hvalid 0
      · intro θ
        have he : finiteDecisionLaw readRecord
            (fun _ => causalFiniteExperiment π.1 response 2 0) θ =
              causalFiniteExperiment π.1 response 2 θ := by
          funext y
          simp only [finiteDecisionLaw, ← Finset.sum_mul, (readRecord_valid θ).2, one_mul]
          exact congrFun (hclass 0 θ) y
        change finiteTV (finiteDecisionLaw readRecord
          (fun _ => causalFiniteExperiment π.1 response 2 0) θ)
            (causalFiniteExperiment π.1 response 2 θ) ≤ 0
        rw [he]
        simp [finiteTV]
    · exact finiteDeficiency_nonneg_of_valid _ _ readRecord_valid hvalid
  · rw [finiteDeficiency_classIndependent_binary_eq_half_pairTV _ _
      hvalid readRecord_valid hclass, readRecord_pairTV]

end
end IdExp.FirstVisitCount
