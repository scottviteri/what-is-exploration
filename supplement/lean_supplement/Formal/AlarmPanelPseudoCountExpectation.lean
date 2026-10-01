import Formal.StartupPolicyReferences
import Formal.CausalUniversality

/-!
# Actual-prior expectations of finite alarm/panel record rewards

These helpers apply to any fixed real score on a finite collected record. They
transfer bounds on supported records to the actual prior expectation, retain the
literal startup branch decomposition, and obtain a deterministic global optimizer
from the finite causal Kuhn decomposition. There is no assumed optimizer or
supplied abstract objective realization.
-/

noncomputable section
namespace IdExp.AlarmPanel.PseudoCount
open Finset MeasureTheory

/-- Expected finite-record score under the fixed geometric alarm prior. -/
def recordObjective (π : CausalPolicy Action Observation) (t : ℕ)
    (F : CausalFiniteTrace Action Observation t → ℝ) : ℝ :=
  ∫ θ, ∑ w, experiment π t θ w * F w ∂AlarmPanelPrior.prior

/-- Every real score on the finite record alphabet has an integrable expectation. -/
theorem recordObjective_integrable (π : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (t : ℕ)
    (F : CausalFiniteTrace Action Observation t → ℝ) :
    Integrable (fun θ => ∑ w, experiment π t θ w * F w) AlarmPanelPrior.prior := by
  exact integrable_finsetSum _ fun w _ =>
    (PulseBrierScore.likelihood_integrable _ (experiment_valid π hπ t) w).mul_const (F w)

/-- Literal startup mixture, valid for any fixed finite-record score and any
adaptive continuation of a valid collector. -/
theorem recordObjective_branch_mixture (π : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (n : ℕ)
    (F : CausalFiniteTrace Action Observation (n+1) → ℝ) :
    recordObjective π (n+1) F =
      inspectionProbability π * recordObjective (inspectBranch π) (n+1) F +
      (1-inspectionProbability π) * recordObjective (playBranch π) (n+1) F := by
  simpa only [priorRecordReward, finiteRecordReward, experimentV_original, recordObjective]
    using priorRecordReward_branch_mixture Variant.original Variant.original_valid π hπ n F

/-- A bound only on positive-mass records bounds the worldwise expectation. -/
theorem recordExpectation_le_of_support (π : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (t : ℕ)
    (F : CausalFiniteTrace Action Observation t → ℝ) (C : ℝ) (θ : World)
    (hF : ∀ w, experiment π t θ w ≠ 0 → F w ≤ C) :
    (∑ w, experiment π t θ w * F w) ≤ C := by
  calc
    (∑ w, experiment π t θ w * F w) ≤ ∑ w, experiment π t θ w * C := by
      apply Finset.sum_le_sum
      intro w _
      by_cases hw : experiment π t θ w = 0
      · simp [hw]
      · exact mul_le_mul_of_nonneg_left (hF w hw) ((experiment_valid π hπ t θ).1 w)
    _ = C := by rw [← Finset.sum_mul, (experiment_valid π hπ t θ).2, one_mul]

/-- The corresponding supported lower bound for the worldwise expectation. -/
theorem le_recordExpectation_of_support (π : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (t : ℕ)
    (F : CausalFiniteTrace Action Observation t → ℝ) (C : ℝ) (θ : World)
    (hF : ∀ w, experiment π t θ w ≠ 0 → C ≤ F w) :
    C ≤ ∑ w, experiment π t θ w * F w := by
  calc
    C = ∑ w, experiment π t θ w * C := by
      rw [← Finset.sum_mul, (experiment_valid π hπ t θ).2, one_mul]
    _ ≤ ∑ w, experiment π t θ w * F w := by
      apply Finset.sum_le_sum
      intro w _
      by_cases hw : experiment π t θ w = 0
      · simp [hw]
      · exact mul_le_mul_of_nonneg_left (hF w hw) ((experiment_valid π hπ t θ).1 w)

/-- Uniform supported-record upper bounds transfer to the actual-prior objective. -/
theorem recordObjective_le_of_support (π : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (t : ℕ)
    (F : CausalFiniteTrace Action Observation t → ℝ) (C : ℝ)
    (hF : ∀ θ w, experiment π t θ w ≠ 0 → F w ≤ C) :
    recordObjective π t F ≤ C := by
  have h := integral_mono (recordObjective_integrable π hπ t F) (integrable_const C)
    (fun θ => recordExpectation_le_of_support π hπ t F C θ (hF θ))
  simpa [recordObjective] using h

/-- Uniform supported-record lower bounds transfer to the actual-prior objective. -/
theorem le_recordObjective_of_support (π : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (t : ℕ)
    (F : CausalFiniteTrace Action Observation t → ℝ) (C : ℝ)
    (hF : ∀ θ w, experiment π t θ w ≠ 0 → C ≤ F w) :
    C ≤ recordObjective π t F := by
  have h := integral_mono (integrable_const C) (recordObjective_integrable π hπ t F)
    (fun θ => le_recordExpectation_of_support π hπ t F C θ (hF θ))
  simpa [recordObjective] using h

/-- The actual finite experiment is a world-independent mixture of deterministic
causal plans. -/
theorem experiment_kuhn (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (t : ℕ) (θ : World) (w : CausalFiniteTrace Action Observation t) :
    experiment π t θ w = ∑ τ : CausalPlan Action Observation t,
      kuhnWeight π t τ * experiment (causalPolicyOfPlan t τ) t θ w :=
  congrFun (congrFun (causalFiniteExperiment_kuhn_decomposition π hπ response t) θ) w

/-- Prior expectation preserves the causal Kuhn decomposition of the record score. -/
theorem recordObjective_kuhn (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (t : ℕ) (F : CausalFiniteTrace Action Observation t → ℝ) :
    recordObjective π t F = ∑ τ : CausalPlan Action Observation t,
      kuhnWeight π t τ * recordObjective (causalPolicyOfPlan t τ) t F := by
  have hpoint (θ : World) : (∑ w, experiment π t θ w * F w) =
      ∑ τ : CausalPlan Action Observation t,
        kuhnWeight π t τ * (∑ w, experiment (causalPolicyOfPlan t τ) t θ w * F w) := by
    simp_rw [experiment_kuhn π hπ t θ, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro τ _
    simp only [Finset.mul_sum, mul_assoc]
  unfold recordObjective
  simp_rw [hpoint]
  rw [integral_finsetSum _ (fun τ _ =>
    (recordObjective_integrable _ (isCausalPolicy_causalPolicyOfPlan t τ) t F).const_mul _)]
  simp only [integral_const_mul]

/-- A deterministic causal plan actually attains the maximum over all valid
adaptive policies for every fixed finite-record score. -/
theorem exists_maximizing_plan (t : ℕ) (F : CausalFiniteTrace Action Observation t → ℝ) :
    ∃ τ : CausalPlan Action Observation t, ∀ ρ : CausalPolicy Action Observation,
      IsCausalPolicy ρ → recordObjective ρ t F ≤ recordObjective (causalPolicyOfPlan t τ) t F := by
  obtain ⟨τ, _, hτ⟩ := Finset.exists_max_image
    (Finset.univ : Finset (CausalPlan Action Observation t))
    (fun τ => recordObjective (causalPolicyOfPlan t τ) t F) Finset.univ_nonempty
  refine ⟨τ, fun ρ hρ => ?_⟩
  rw [recordObjective_kuhn ρ hρ t F]
  calc
    (∑ σ : CausalPlan Action Observation t,
        kuhnWeight ρ t σ * recordObjective (causalPolicyOfPlan t σ) t F) ≤
      ∑ σ : CausalPlan Action Observation t,
        kuhnWeight ρ t σ * recordObjective (causalPolicyOfPlan t τ) t F := by
      apply Finset.sum_le_sum
      intro σ _
      exact mul_le_mul_of_nonneg_left (hτ σ (Finset.mem_univ σ)) (kuhnWeight_nonneg ρ hρ t σ)
    _ = _ := by rw [← Finset.sum_mul, (kuhnWeight_isDist ρ hρ t).2, one_mul]

end IdExp.AlarmPanel.PseudoCount
