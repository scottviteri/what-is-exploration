import Formal.CompressionProgressSwap
import Formal.CausalUniversality

/-!
# Attained dominated maxima for every finite full-history score

The finite Kuhn decomposition proves actual all-policy global optimality.
The counterexample class is chosen after the fixed scorer and horizon, not
changed while comparing policies. No existence-of-an-optimum premise remains.
-/
namespace IdExp.CompressionProgressSwap
open Finset
noncomputable section

def planPolicy (n : ℕ) (τ : CausalPlan Bool World n) : Policy :=
  ⟨causalPolicyOfPlan n τ, isCausalPolicy_causalPolicyOfPlan n τ⟩

theorem averageExperiment_kuhn (e : Bool) (π : Policy) (n : ℕ)
    (w : CausalFiniteTrace Bool World n) :
    averageExperiment e π n w = ∑ τ : CausalPlan Bool World n,
      kuhnWeight π.1 n τ * averageExperiment e (planPolicy n τ) n w := by
  unfold averageExperiment
  rw [causalFiniteExperiment_kuhn_decomposition π.1 π.2 (response e) n]
  simp only [planPolicy]
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro τ _
  ring

theorem objective_kuhn (e : Bool) (π : Policy) (n : ℕ)
    (F : CausalFiniteTrace Bool World n → ℝ) :
    objective e π n F = ∑ τ : CausalPlan Bool World n,
      kuhnWeight π.1 n τ * objective e (planPolicy n τ) n F := by
  unfold objective
  simp_rw [averageExperiment_kuhn e π n, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro τ _
  simp only [Finset.mul_sum, mul_assoc]

/-- An actual deterministic plan maximizes the score over all valid policies. -/
theorem exists_maximizing_plan (n : ℕ) (F : CausalFiniteTrace Bool World n → ℝ) :
    ∃ τ : CausalPlan Bool World n, ∀ π : Policy,
      objective false π n F ≤ objective false (planPolicy n τ) n F := by
  classical
  obtain ⟨τ,_,hτ⟩ := Finset.exists_max_image (Finset.univ : Finset (CausalPlan Bool World n))
    (fun τ => objective false (planPolicy n τ) n F) Finset.univ_nonempty
  refine ⟨τ, ?_⟩
  intro π
  rw [objective_kuhn]
  calc
    (∑ σ : CausalPlan Bool World n, kuhnWeight π.1 n σ * objective false (planPolicy n σ) n F) ≤
        ∑ σ : CausalPlan Bool World n, kuhnWeight π.1 n σ * objective false (planPolicy n τ) n F := by
      apply Finset.sum_le_sum
      intro σ _
      exact mul_le_mul_of_nonneg_left (hτ σ (Finset.mem_univ σ))
        (kuhnWeight_nonneg π.1 π.2 n σ)
    _ = objective false (planPolicy n τ) n F := by
      rw [← Finset.sum_mul, (kuhnWeight_isDist π.1 π.2 n).2, one_mul]

/-- Every fixed finite full-history score admits a dominated global maximizer
in one of the two classes. The revealing policy is greatest in that same class. -/
theorem exists_dominated_global_maximizer (n : ℕ)
    (F : CausalFiniteTrace Bool World (n+1) → ℝ) :
    ∃ (e : Bool) (π : Policy),
      (∀ ρ : Policy, objective e ρ (n+1) F ≤ objective e π (n+1) F) ∧
      CausalFinitarilyGreatest (response e) (policy e) ∧
      CausalFinitaryDominates (response e) (policy e) π ∧
      ¬ CausalFinitaryDominates (response e) π (policy e) := by
  obtain ⟨τ,hτ⟩ := exists_maximizing_plan (n+1) F
  let a : Bool := τ (causalDecisionPointOfHistory (n+1) [] (by simp))
  have hroot : (planPolicy (n+1) τ).1 [] (!a) = 0 := by
    simp only [planPolicy, causalPolicyOfPlan, List.length_nil, Nat.zero_lt_succ, ↓reduceDIte]
    apply if_neg
    change (!a) ≠ a
    cases a <;> decide
  refine ⟨!a,planPolicy (n+1) τ, ?_, revealing_greatest (!a),
    coin_strictly_dominated (!a) (planPolicy (n+1) τ) hroot⟩
  intro ρ
  simpa only [objective_eq (!a) false] using hτ ρ

end
end IdExp.CompressionProgressSwap
