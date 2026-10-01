import Formal.CausalUniversality

/-!
# Native finite-depth distances and their weighted pseudometric

The domain is the actual subtype of valid history-dependent response kernels.
The topology and the metric on its behavioral quotient are constructed in
`CausalGeometry.lean`. No topology is assumed in the algebraic arguments here.
-/

namespace IdExp

open Finset Set

set_option linter.unusedSectionVars false

variable {A O : Type*} [Fintype A] [Fintype O]
  [Nonempty A] [Nonempty O] [DecidableEq A] [DecidableEq O]

/-- Native observation law evaluated at a valid world. -/
noncomputable def nativeObservationLaw (n : ℕ) (τ : CausalPlan A O n)
    (Q : ValidCausalWorld A O) : CausalObservationTrace O n → ℝ :=
  causalPlanObservationExperiment n τ Subtype.val Q

theorem nativeObservationLaw_valid (n : ℕ) (τ : CausalPlan A O n)
    (Q : ValidCausalWorld A O) : IsDist (nativeObservationLaw n τ Q) :=
  causalPlanObservationExperiment_valid n τ Subtype.val (fun Q => Q.property) Q

/-- The finite maximum in the paper's d_n, with observation-only signals. -/
noncomputable def nativeDepthDist (n : ℕ) (Q Q' : ValidCausalWorld A O) : ℝ :=
  (univ : Finset (CausalPlan A O n)).sup' univ_nonempty
    (fun τ => finiteTV (nativeObservationLaw n τ Q) (nativeObservationLaw n τ Q'))

theorem nativeTestDist_le_depth (n : ℕ) (τ : CausalPlan A O n)
    (Q Q' : ValidCausalWorld A O) :
    finiteTV (nativeObservationLaw n τ Q) (nativeObservationLaw n τ Q') ≤
      nativeDepthDist n Q Q' := by
  unfold nativeDepthDist
  exact Finset.le_sup'
    (fun σ : CausalPlan A O n =>
      finiteTV (nativeObservationLaw n σ Q) (nativeObservationLaw n σ Q'))
    (mem_univ τ)

theorem nativeDepthDist_nonneg (n : ℕ) (Q Q' : ValidCausalWorld A O) :
    0 ≤ nativeDepthDist n Q Q' :=
  (finiteTV_nonneg _ _).trans
    (nativeTestDist_le_depth n (fun _ => Classical.choice inferInstance) Q Q')

theorem nativeDepthDist_le_one (n : ℕ) (Q Q' : ValidCausalWorld A O) :
    nativeDepthDist n Q Q' ≤ 1 := by
  apply Finset.sup'_le
  intro τ _
  exact finiteTV_le_one_of_isDist _ _
    (nativeObservationLaw_valid n τ Q) (nativeObservationLaw_valid n τ Q')

@[simp] theorem nativeDepthDist_self (n : ℕ) (Q : ValidCausalWorld A O) :
    nativeDepthDist n Q Q = 0 := by
  simp [nativeDepthDist, finiteTV]

theorem nativeDepthDist_comm (n : ℕ) (Q Q' : ValidCausalWorld A O) :
    nativeDepthDist n Q Q' = nativeDepthDist n Q' Q := by
  simp only [nativeDepthDist, finiteTV_symm]

theorem nativeDepthDist_triangle (n : ℕ) (Q R Q' : ValidCausalWorld A O) :
    nativeDepthDist n Q Q' ≤ nativeDepthDist n Q R + nativeDepthDist n R Q' := by
  apply Finset.sup'_le
  intro τ _
  exact (finiteTV_triangle _ _ _).trans (add_le_add
    (nativeTestDist_le_depth n τ Q R) (nativeTestDist_le_depth n τ R Q'))

@[simp] theorem nativeDepthDist_zero (Q Q' : ValidCausalWorld A O) :
    nativeDepthDist 0 Q Q' = 0 := by
  have hrow (τ : CausalPlan A O 0) (Q : ValidCausalWorld A O) :
      nativeObservationLaw 0 τ Q = fun _ => 1 := by
    funext w
    have h := (nativeObservationLaw_valid 0 τ Q).2
    simpa only [Fintype.sum_unique,
      show (default : CausalObservationTrace O 0) = w from Subsingleton.elim _ _] using h
  simp [nativeDepthDist, hrow, finiteTV]

theorem nativeObservationLaw_eq_of_behEq
    {Q Q' : ValidCausalWorld A O} (h : CausalBehEq Q.val Q'.val)
    (n : ℕ) (τ : CausalPlan A O n) :
    nativeObservationLaw n τ Q = nativeObservationLaw n τ Q' := by
  funext o
  unfold nativeObservationLaw
  rw [causalPlanObservationExperiment_eq_reconstruction,
    causalPlanObservationExperiment_eq_reconstruction]
  exact causalTraceProb_eq_of_causalBehEq (causalPolicyOfPlan n τ) h _

/-- Zero in every depth coordinate is exactly controlled-trace equivalence;
the converse constructs the open-loop plan for each given trace. -/
theorem nativeDepthDist_all_zero_iff (Q Q' : ValidCausalWorld A O) :
    (∀ n, nativeDepthDist n Q Q' = 0) ↔ CausalBehEq Q.val Q'.val := by
  constructor
  · intro h htr
    let n := htr.length
    let w : CausalFiniteTrace A O n := htr.get
    let τ : CausalPlan A O n := fun d => (w d.1).1
    have hw : List.ofFn w = htr := List.ofFn_get _
    have hagree : CausalPlanAgreesTrace τ w := by
      intro k
      simp [τ, causalTraceDecisionPoint, causalDecisionPointOfHistory, causalTracePrefix]
    have hobs : nativeObservationLaw n τ Q = nativeObservationLaw n τ Q' := by
      apply (finiteTV_eq_zero_iff _ _).1
      exact le_antisymm ((nativeTestDist_le_depth n τ Q Q').trans_eq (h n))
        (finiteTV_nonneg _ _)
    have hfull :
        causalFiniteExperiment (causalPolicyOfPlan n τ) Subtype.val n Q =
        causalFiniteExperiment (causalPolicyOfPlan n τ) Subtype.val n Q' := by
      rw [← causalPlanObservationExperiment_attach n τ Subtype.val]
      funext x
      change (∑ o, nativeObservationLaw n τ Q o * causalAttachPlanActionsRule τ o x) =
        ∑ o, nativeObservationLaw n τ Q' o * causalAttachPlanActionsRule τ o x
      rw [hobs]
    have hc := congrFun hfull w
    change causalTraceProb (causalPolicyOfPlan n τ) Q.val (List.ofFn w) =
      causalTraceProb (causalPolicyOfPlan n τ) Q'.val (List.ofFn w) at hc
    rw [causalTraceProb_factor, causalTraceProb_factor,
      causalPolicyProb_plan_eq_indicator] at hc
    simpa only [causalPlanTraceIndicator, if_pos hagree, one_mul, hw] using hc
  · intro h n
    unfold nativeDepthDist
    simp [nativeObservationLaw_eq_of_behEq h, finiteTV]

/-- Forgetting and reattaching deterministic actions preserves rowwise TV. -/
theorem nativePlan_full_tv_eq (n : ℕ) (τ : CausalPlan A O n)
    (Q Q' : ValidCausalWorld A O) :
    finiteTV (causalFiniteExperiment (causalPolicyOfPlan n τ) Subtype.val n Q)
      (causalFiniteExperiment (causalPolicyOfPlan n τ) Subtype.val n Q') =
    finiteTV (nativeObservationLaw n τ Q) (nativeObservationLaw n τ Q') := by
  apply le_antisymm
  · have h := finiteTV_decisionLaw_le
      (causalPlanObservationExperiment n τ (Subtype.val : ValidCausalWorld A O → _))
      (causalAttachPlanActionsRule τ)
      (causalAttachPlanActionsRule_mem_stochasticRules τ) Q Q'
    rw [causalPlanObservationExperiment_attach] at h
    exact h
  · exact finiteTV_decisionLaw_le
      (causalFiniteExperiment (causalPolicyOfPlan n τ) Subtype.val n)
      causalForgetActionsRule causalForgetActionsRule_mem_stochasticRules Q Q'

/-- The literal randomized-policy inequality in the native geometry
proposition, including the recorded actions in the acquired signal. -/
theorem causalPolicy_tv_le_nativeDepthDist
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (n : ℕ) (Q Q' : ValidCausalWorld A O) :
    finiteTV (causalFiniteExperiment π Subtype.val n Q)
      (causalFiniteExperiment π Subtype.val n Q') ≤ nativeDepthDist n Q Q' := by
  rw [causalFiniteExperiment_kuhn_decomposition π hπ]
  apply finiteTV_mixture_le _ _ _ (kuhnWeight_isDist π hπ n)
  intro τ
  rw [nativePlan_full_tv_eq]
  exact nativeTestDist_le_depth n τ Q Q'

/-- Positive summable weights, indexed so the sum starts at depth one. -/
noncomputable def nativeWeight (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 1)

theorem nativeWeight_pos (n : ℕ) : 0 < nativeWeight n := by
  unfold nativeWeight
  positivity

theorem nativeWeight_summable : Summable nativeWeight := by
  exact summable_geometric_two.comp_injective Nat.succ_injective

/-- The paper's weighted native pseudometric. -/
noncomputable def nativeDist (Q Q' : ValidCausalWorld A O) : ℝ :=
  ∑' n, nativeWeight n * nativeDepthDist (n + 1) Q Q'

theorem nativeDist_summable (Q Q' : ValidCausalWorld A O) :
    Summable (fun n => nativeWeight n * nativeDepthDist (n + 1) Q Q') := by
  apply Summable.of_norm_bounded nativeWeight_summable
  intro n
  rw [Real.norm_of_nonneg (mul_nonneg (nativeWeight_pos n).le
    (nativeDepthDist_nonneg (n + 1) Q Q'))]
  exact mul_le_of_le_one_right (nativeWeight_pos n).le (nativeDepthDist_le_one _ _ _)

theorem nativeDist_nonneg (Q Q' : ValidCausalWorld A O) : 0 ≤ nativeDist Q Q' :=
  tsum_nonneg (fun n => mul_nonneg (nativeWeight_pos n).le (nativeDepthDist_nonneg _ _ _))

@[simp] theorem nativeDist_self (Q : ValidCausalWorld A O) : nativeDist Q Q = 0 := by
  simp [nativeDist]

theorem nativeDist_comm (Q Q' : ValidCausalWorld A O) :
    nativeDist Q Q' = nativeDist Q' Q := by
  simp only [nativeDist, nativeDepthDist_comm]

theorem nativeDist_triangle (Q R Q' : ValidCausalWorld A O) :
    nativeDist Q Q' ≤ nativeDist Q R + nativeDist R Q' := by
  rw [nativeDist, nativeDist, nativeDist,
    ← (nativeDist_summable Q R).tsum_add (nativeDist_summable R Q')]
  exact (nativeDist_summable Q Q').tsum_le_tsum
    (fun n => by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (nativeDepthDist_triangle _ _ _ _) (nativeWeight_pos n).le)
    ((nativeDist_summable Q R).add (nativeDist_summable R Q'))

theorem nativeDist_eq_zero_iff (Q Q' : ValidCausalWorld A O) :
    nativeDist Q Q' = 0 ↔ CausalBehEq Q.val Q'.val := by
  rw [← nativeDepthDist_all_zero_iff]
  constructor
  · intro hz n
    cases n with
    | zero => exact nativeDepthDist_zero Q Q'
    | succ n =>
      have hle := (nativeDist_summable Q Q').le_tsum n
        (fun i _ => mul_nonneg (nativeWeight_pos i).le (nativeDepthDist_nonneg _ _ _))
      change nativeWeight n * nativeDepthDist (n + 1) Q Q' ≤ nativeDist Q Q' at hle
      rw [hz] at hle
      have hd := nativeDepthDist_nonneg (n + 1) Q Q'
      have hw := nativeWeight_pos n
      nlinarith
  · intro h
    simp [nativeDist, h]

end IdExp
