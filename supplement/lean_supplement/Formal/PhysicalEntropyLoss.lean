import Formal.PhysicalEntropyControl
import Formal.CausalPartialExecution

/-!
# Persistent capability loss of physical-entropy maximizers

All positive finite records and the full retained path have exactly the
root experiment's statistical content. The missing revelation deficiency
is therefore `(1-s)/2` for every stochastic policy with root reveal
probability `s`, and one third for every full MOP maximizer.
-/

namespace IdExp.PhysicalEntropyControl
open Finset MeasureTheory ProbabilityTheory
noncomputable section

/-- Recorded root action and resulting physical state. -/
def rootRecord (π : ValidCausalPolicy Action Observation) :
    FiniteExperiment World (Action × Observation) := absorbingRootExperiment root π.1

theorem rootRecord_valid (π : ValidCausalPolicy Action Observation) :
    IsFiniteExperiment (rootRecord π) :=
  absorbingRootExperiment_valid root root_valid π.1 π.2

theorem one_eq_absorbing (π : CausalPolicy Action Observation) :
    causalFiniteExperiment π response 1 =
      causalFiniteExperiment π (absorbingResponse 0 root) 1 := by
  funext θ w
  simp [causalFiniteExperiment, causalTraceProb, List.ofFn_succ, causalTraceProbFrom,
    response, absorbingResponse]

theorem one_rootRecord_equiv (π : ValidCausalPolicy Action Observation) :
    FiniteBlackwellLE (causalFiniteExperiment π.1 response 1) (rootRecord π) ∧
      FiniteBlackwellLE (rootRecord π) (causalFiniteExperiment π.1 response 1) := by
  rw [one_eq_absorbing]
  exact absorbingCausalExperiment_root_blackwell_equiv 0 root root_valid π.1 π.2 0

theorem rootRecord_pairTV (π : ValidCausalPolicy Action Observation) :
    finiteTV (rootRecord π 0) (rootRecord π 1) = π.1 [] 0 := by
  have hs := (policy_root_bounds π).1
  norm_num [rootRecord, absorbingRootExperiment, finiteTV, Fintype.sum_prod_type,
    Fin.sum_univ_succ, root, abs_of_nonneg hs, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, Fin.reduceFinMk]
  ring

theorem revelation_pairTV : finiteTV (root 0 0) (root 0 1) = 1 := by
  norm_num [root, finiteTV, Fin.sum_univ_succ]

/-- Preserve revealed labels; on either known-noise label guess the bit fairly. -/
def guess : (Action × Observation) → Observation → ℝ :=
  fun ao => if ao.2 = 0 then ![1,0,0,0]
    else if ao.2 = 1 then ![0,1,0,0] else ![1/2,1/2,0,0]

theorem guess_valid : guess ∈ stochasticRules (Action × Observation) Observation := by
  intro ao _
  constructor
  · intro o
    rcases ao with ⟨a, i⟩
    fin_cases i <;> fin_cases o <;> norm_num [guess]
  · rcases ao with ⟨a, i⟩
    fin_cases i <;> norm_num [guess, Fin.sum_univ_succ]

theorem guess_error (π : ValidCausalPolicy Action Observation) (θ : World) :
    decodeErr (rootRecord π) (root 0) guess θ = (1 - π.1 [] 0)/2 := by
  have hs0 := (policy_root_bounds π).1
  have hs1 := (policy_root_bounds π).2
  have hhalf : 0 ≤ (1 - π.1 [] 0)/2 := by linarith
  have hneg : π.1 [] 0 + (1 - π.1 [] 0)/2 - 1 ≤ 0 := by linarith
  unfold decodeErr
  norm_num [rootRecord, absorbingRootExperiment, root, guess, Fintype.sum_prod_type,
    Fin.sum_univ_succ, policy_root_other, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    Fin.reduceFinMk]
  fin_cases θ <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_succ, Fin.ext_iff] <;>
    (repeat first | rw [abs_of_nonpos (by linarith)] | rw [abs_of_nonneg (by linarith)]) <;> ring

/-- Exact minimax loss to the available root revelation, with randomized decoders. -/
theorem rootRecord_revelation_deficiency (π : ValidCausalPolicy Action Observation) :
    finiteDeficiency (rootRecord π) (root 0) = (1 - π.1 [] 0)/2 := by
  apply le_antisymm
  · exact finiteDeficiency_le_of_decoder _ _ guess guess_valid _ (fun θ => (guess_error π θ).le)
  · have h := finiteDeficiency_pairwise_lower (rootRecord π) (root 0)
      (rootRecord_valid π) (root_valid 0) 0 1
    rwa [revelation_pairTV, rootRecord_pairTV] at h

theorem prefix_revelation_deficiency (π : ValidCausalPolicy Action Observation) (t : ℕ) :
    finiteDeficiency (causalFiniteExperiment π.1 response (t+1)) (root 0) =
      (1 - π.1 [] 0)/2 := by
  obtain ⟨he1, h1e⟩ := causalFiniteExperiment_sharedTail_blackwell_equiv π.1 π.2
    response response_valid stay stay_valid 1 response_sharedTail
    (show 1 ≤ t+1 by omega)
  obtain ⟨h1r, hr1⟩ := one_rootRecord_equiv π
  rw [finiteDeficiency_eq_of_source_blackwellEquiv _ (rootRecord π) (root 0)
    (finiteBlackwellLE_trans he1 h1r) (finiteBlackwellLE_trans hr1 h1e)]
  exact rootRecord_revelation_deficiency π

theorem one_pairTV (π : ValidCausalPolicy Action Observation) :
    finiteTV (causalFiniteExperiment π.1 response 1 0)
      (causalFiniteExperiment π.1 response 1 1) = π.1 [] 0 := by
  rw [one_eq_absorbing]
  unfold finiteTV
  rw [← (Equiv.funUnique (Fin 1) (Action × Observation)).symm.sum_comp]
  simp only [absorbingCausalExperiment_one_root]
  exact rootRecord_pairTV π

/-- Full path TV is fixed at the initial reveal probability. Future action
randomness remains in the record and does not create extra world information. -/
theorem path_pairTV (π : ValidCausalPolicy Action Observation) :
    finiteMeasureTV
      (causalPathExperiment response response_valid π 0 : Measure (CausalTraj Action Observation))
      (causalPathExperiment response response_valid π 1 : Measure (CausalTraj Action Observation)) =
      π.1 [] 0 :=
  (causalPath_sharedTail_pairTV response response_valid π stay stay_valid 1
    response_sharedTail 0 1).trans (one_pairTV π)

/-- The arbitrary measurable full-record decoder has exactly the same
remaining deficiency as a finite recorded prefix. -/
theorem path_revelation_deficiency (π : ValidCausalPolicy Action Observation) :
    finiteMeasureDeficiency (causalPathExperiment response response_valid π)
      (rowExperiment (root 0)) = (1 - π.1 [] 0)/2 := by
  apply le_antisymm
  · have h := finiteMeasureDeficiency_le_of_source_garbling_of_prob
      (causalPathExperiment response response_valid π)
      (causalTraceMeasureExperiment response response_valid π 1)
      (causalPrefixKernel 1) (finiteMarkovDecode_causalPrefixKernel response response_valid π 1)
      (rowExperiment (root 0))
      (isProbabilityMeasure_causalTraceMeasureExperiment' response response_valid π 1)
      (fun θ => isProbabilityMeasure_finiteMeasureOfRow _ (root_valid 0 θ))
    rw [causalTraceMeasureExperiment_eq_rowExperiment,
      finiteMeasureDeficiency_eq_finiteDeficiency _ _
        (causalFiniteExperiment_valid π.1 π.2 response response_valid 1) (root_valid 0),
      prefix_revelation_deficiency π 0] at h
    exact h
  · have h := finiteMeasureDeficiency_pairwise_lower
      (causalPathExperiment response response_valid π) (rowExperiment (root 0))
      (isProbabilityMeasure_causalPathExperiment' response response_valid π)
      (fun θ => isProbabilityMeasure_finiteMeasureOfRow _ (root_valid 0 θ)) 0 1
    rw [path_pairTV] at h
    have ht : finiteMeasureTV (rowExperiment (root 0) 0 : Measure Observation)
        (rowExperiment (root 0) 1 : Measure Observation) = 1 := by
      rw [rowExperiment, rowExperiment, finiteMeasureTV_finiteMeasureOfRow _ _
        (root_valid 0 0).1 (root_valid 0 1).1, revelation_pairTV]
    rwa [ht] at h

/-- Every full discounted physical-MOP maximizer loses one third of the
available revelation capability, at every positive horizon and on the full path. -/
theorem maximizing_revelation_loss (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (π : ValidCausalPolicy Action Observation)
    (hmax : ∀ ρ : ValidCausalPolicy Action Observation, objective γ ρ ≤ objective γ π) :
    (∀ t, finiteDeficiency (causalFiniteExperiment π.1 response (t+1)) (root 0) = 1/3) ∧
      finiteMeasureDeficiency (causalPathExperiment response response_valid π)
        (rowExperiment (root 0)) = 1/3 := by
  have hroot := maximizing_root_eq_third γ hγ0.le hγ1 π hmax
  constructor
  · intro t; rw [prefix_revelation_deficiency, hroot]; norm_num
  · rw [path_revelation_deficiency, hroot]; norm_num

/-- The available deterministic one-step revelation intervention. -/
def readPlan : CausalPlan Action Observation 1 := fun _ => 0

theorem nativeRead_equiv_revelation :
    FiniteBlackwellLE (causalPlanObservationExperiment 1 readPlan response) (root 0) ∧
      FiniteBlackwellLE (root 0) (causalPlanObservationExperiment 1 readPlan response) := by
  have heq : causalPlanObservationExperiment 1 readPlan response =
      causalPlanObservationExperiment 1 readPlan (absorbingResponse 0 root) := by
    unfold causalPlanObservationExperiment
    rw [one_eq_absorbing]
  rw [heq]
  exact absorbingNativeTest_all_depths_blackwell_equiv 0 root root_valid 0 readPlan

theorem prefix_nativeRead_deficiency (π : ValidCausalPolicy Action Observation) (t : ℕ) :
    finiteDeficiency (causalFiniteExperiment π.1 response (t+1))
      (causalPlanObservationExperiment 1 readPlan response) = (1 - π.1 [] 0)/2 := by
  rw [finiteDeficiency_eq_of_target_blackwellEquiv _ _ (root 0)
    (causalFiniteExperiment_valid π.1 π.2 response response_valid (t+1))
    (causalPlanObservationExperiment_valid 1 readPlan response response_valid)
    (root_valid 0) nativeRead_equiv_revelation.1 nativeRead_equiv_revelation.2]
  exact prefix_revelation_deficiency π t

theorem path_nativeRead_deficiency (π : ValidCausalPolicy Action Observation) :
    finiteMeasureDeficiency (causalPathExperiment response response_valid π)
      (rowExperiment (causalPlanObservationExperiment 1 readPlan response)) =
      (1 - π.1 [] 0)/2 := by
  rw [finiteMeasureDeficiency_row_target_eq_of_blackwellEquiv _
    (isProbabilityMeasure_causalPathExperiment' response response_valid π) _ (root 0)
    (causalPlanObservationExperiment_valid 1 readPlan response response_valid)
    (root_valid 0) nativeRead_equiv_revelation.1 nativeRead_equiv_revelation.2]
  exact path_revelation_deficiency π

/-- The loss is a fixed available native intervention, including the entire
retained infinite record and arbitrary measurable randomized terminal decoders. -/
theorem maximizing_native_loss (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (π : ValidCausalPolicy Action Observation)
    (hmax : ∀ ρ : ValidCausalPolicy Action Observation, objective γ ρ ≤ objective γ π) :
    (∀ t, finiteDeficiency (causalFiniteExperiment π.1 response (t+1))
      (causalPlanObservationExperiment 1 readPlan response) = 1/3) ∧
      finiteMeasureDeficiency (causalPathExperiment response response_valid π)
        (rowExperiment (causalPlanObservationExperiment 1 readPlan response)) = 1/3 := by
  have hroot := maximizing_root_eq_third γ hγ0.le hγ1 π hmax
  constructor
  · intro t; rw [prefix_nativeRead_deficiency, hroot]; norm_num
  · rw [path_nativeRead_deficiency, hroot]; norm_num

/-- Every global MOP maximizer fails native sufficiency in this literal
physical-state control system. -/
theorem maximizing_not_nativelySufficient (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (π : ValidCausalPolicy Action Observation)
    (hmax : ∀ ρ : ValidCausalPolicy Action Observation, objective γ ρ ≤ objective γ π) :
    ¬ CausalNativelySufficient response π := by
  intro hsuff
  obtain ⟨T, hT⟩ := hsuff 1 (1/3) (by norm_num)
  have h := hT (T+1) (by omega) readPlan
  rw [(maximizing_native_loss γ hγ0 hγ1 π hmax).1 T] at h
  exact (lt_irrefl _ h)

/-- The pure revelation intervention can generate any finite experiment on
these two worlds, using the revealed bit as the decoder's input. -/
theorem revelation_dominates {Y : Type*} [Fintype Y]
    (E : FiniteExperiment World Y) (hE : IsFiniteExperiment E) :
    FiniteBlackwellLE E (root 0) := by
  let G : Observation → Y → ℝ := fun o => if o = 0 then E 0 else E 1
  refine ⟨G, ?_, ?_⟩
  · intro o _
    by_cases ho : o = 0
    · simpa [G, ho] using hE 0
    · simpa [G, ho] using hE 1
  · funext θ y
    fin_cases θ <;>
      norm_num [finiteDecisionLaw, root, G, Fin.sum_univ_succ,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_succ]

def readPolicy : ValidCausalPolicy Action Observation :=
  ⟨uniformTail 1, uniformTail_valid (by norm_num) (by norm_num)⟩

/-- Complete native capability is attainable in the same environment. -/
theorem readPolicy_nativelySufficient : CausalNativelySufficient response readPolicy := by
  intro n ε hε
  refine ⟨1, ?_⟩
  intro t ht τ
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show t ≠ 0 by omega)
  have h := finiteDeficiency_mono_target_of_finiteBlackwellLE
    (causalFiniteExperiment readPolicy.1 response (k+1))
    (causalPlanObservationExperiment n τ response) (root 0)
    (causalFiniteExperiment_valid readPolicy.1 readPolicy.2 response response_valid (k+1))
    (root_valid 0)
    (revelation_dominates _ (causalPlanObservationExperiment_valid n τ response response_valid))
  rw [prefix_revelation_deficiency] at h
  norm_num [readPolicy, uniformTail] at h
  exact h.trans_lt hε

/-- Every MOP optimum is strictly below an attainable greatest process, not
merely below an unavailable ideal revelation experiment. -/
theorem maximizing_strictly_dominated (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (π : ValidCausalPolicy Action Observation)
    (hmax : ∀ ρ : ValidCausalPolicy Action Observation, objective γ ρ ≤ objective γ π) :
    CausalFinitaryDominates response readPolicy π ∧
      ¬ CausalFinitaryDominates response π readPolicy := by
  have hgreat := (causalNativelySufficient_iff_finitarilyGreatest response response_valid
    readPolicy).1 readPolicy_nativelySufficient
  refine ⟨hgreat π, ?_⟩
  intro hback
  apply maximizing_not_nativelySufficient γ hγ0 hγ1 π hmax
  apply (causalNativelySufficient_iff_finitarilyGreatest response response_valid π).2
  intro ρ
  exact causalFinitaryDominates_trans response response_valid hback (hgreat ρ)

end
end IdExp.PhysicalEntropyControl
