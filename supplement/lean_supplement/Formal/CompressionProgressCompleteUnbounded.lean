import Formal.CompressionProgressIdeal
import Formal.CausalPolicyCountableMixture

/-!
# Attainment of unbounded complete compression progress

If finite-prefix expected scores have no common finite bound, a countable
mixture of deterministic-root policies attains infinite expected complete
return. It is still an ordinary valid history policy, with a deterministic
first action. Choosing the opposite revealing-button wiring gives permanent
one-half deficiency and an attained extended-valued global maximum.

The proof uses only componentwise lower bounds on finite-prefix expectations;
it does not assume that exchanging two infinite limits preserves an optimum.
-/
namespace IdExp.CompressionProgressIdeal
open CompressionProgressSwap
open scoped ENNReal
noncomputable section

/-- Every deterministic finite plan, including a zero-step plan completed by
its fixed fallback action, assigns zero probability to one Boolean root action. -/
theorem planPolicy_exists_root_zero (n : ℕ) (τ : CausalPlan Bool World n) :
    ∃ e : Bool, (planPolicy n τ).1 [] e = 0 := by
  classical
  by_cases hn : 0 < n
  · let a : Bool := τ (causalDecisionPointOfHistory n [] (by simpa using hn))
    refine ⟨!a, ?_⟩
    simp only [planPolicy, causalPolicyOfPlan, List.length_nil, hn, ↓reduceDIte]
    apply if_neg
    change (!a) ≠ a
    cases a <;> decide
  · let a : Bool := Classical.choice (inferInstance : Nonempty Bool)
    refine ⟨!a, ?_⟩
    simp only [planPolicy, causalPolicyOfPlan, List.length_nil, hn, ↓reduceDIte]
    apply if_neg
    change (!a) ≠ a
    cases a <;> decide

/-- At least one deterministic-root family has unbounded finite-prefix scores.
Finite-plan attainment supplies the reduction from arbitrary randomized policies. -/
theorem exists_unbounded_root (S : HistoryCompressor)
    (hu : ∀ B : ℝ, ∃ (π : Policy) (n : ℕ), B < prefixObjective S false π n) :
    ∃ e : Bool, ∀ B : ℝ, ∃ (π : Policy) (n : ℕ),
      π.1 [] e = 0 ∧ B < prefixObjective S false π n := by
  classical
  by_cases hf : ∀ B : ℝ, ∃ (π : Policy) (n : ℕ),
      π.1 [] false = 0 ∧ B < prefixObjective S false π n
  · exact ⟨false, hf⟩
  · push Not at hf
    obtain ⟨B, hB⟩ := hf
    refine ⟨true, ?_⟩
    intro C
    obtain ⟨π, n, hn⟩ := hu (max B C)
    obtain ⟨τ, hτ⟩ := exists_maximizing_plan n (fun w => S.score (List.ofFn w))
    have hmax : max B C < prefixObjective S false (planPolicy n τ) n :=
      hn.trans_le (hτ π)
    obtain ⟨e, he⟩ := planPolicy_exists_root_zero n τ
    cases e with
    | false =>
      have hb := hB (planPolicy n τ) n he
      exact (not_lt_of_ge hb ((le_max_left B C).trans_lt hmax)).elim
    | true =>
      exact ⟨planPolicy n τ, n, he, (le_max_right B C).trans_lt hmax⟩

/-- A nonnegative full-history score inherits every weighted component's
finite-prefix expectation as a lower bound under the actual mixed policy. -/
theorem weighted_prefix_le_countable_mixture (S : HistoryCompressor) (e : Bool)
    {I : Type*} (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : Summable w) (ht : ∑' i, w i = 1) (π : I → Policy) (i : I) (n : ℕ) :
    w i * prefixObjective S e (π i) n ≤
      prefixObjective S e (countablePolicyMixture w hw hs ht π) n := by
  unfold prefixObjective objective
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  have h0 := weighted_trace_le_countablePolicyMixture w hw hs ht π i
    (response e 0) (response_valid e 0) (List.ofFn x)
  have h1 := weighted_trace_le_countablePolicyMixture w hw hs ht π i
    (response e 1) (response_valid e 1) (List.ofFn x)
  have ha : w i * averageExperiment e (π i) n x ≤
      averageExperiment e (countablePolicyMixture w hw hs ht π) n x := by
    unfold averageExperiment causalFiniteExperiment
    linarith
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_right ha (S.score_nonneg (List.ofFn x))

/-- A fixed positive normalized weighting of the countable selected policies. -/
def geometricPolicyWeight (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n * (1 / 2)

theorem geometricPolicyWeight_pos (n : ℕ) : 0 < geometricPolicyWeight n := by
  unfold geometricPolicyWeight
  positivity

theorem geometricPolicyWeight_summable : Summable geometricPolicyWeight := by
  exact (summable_geometric_of_norm_lt_one (show ‖(1 / 2 : ℝ)‖ < 1 by norm_num)).mul_right _

theorem geometricPolicyWeight_tsum : ∑' n, geometricPolicyWeight n = 1 := by
  unfold geometricPolicyWeight
  rw [tsum_mul_right, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
  norm_num

/-- A single deterministic-root policy attains infinite complete return when
that root family has unbounded finite-prefix expectations. -/
theorem exists_root_zero_complete_top (S : HistoryCompressor) (e : Bool)
    (hu : ∀ B : ℝ, ∃ (π : Policy) (n : ℕ),
      π.1 [] e = 0 ∧ B < prefixObjective S false π n) :
    ∃ π : Policy, π.1 [] e = 0 ∧ completeObjective S false π = ⊤ := by
  classical
  have hsel (k : ℕ) : ∃ (π : Policy) (n : ℕ),
      π.1 [] e = 0 ∧ (k : ℝ) / geometricPolicyWeight k < prefixObjective S false π n :=
    hu _
  choose π n hroot hscore using hsel
  let mix := countablePolicyMixture geometricPolicyWeight
    (fun k => (geometricPolicyWeight_pos k).le)
    geometricPolicyWeight_summable geometricPolicyWeight_tsum π
  refine ⟨mix, countablePolicyMixture_root_zero _ _ _ _ π e hroot, ?_⟩
  apply top_unique
  rw [← ENNReal.iSup_natCast]
  apply iSup_le
  intro k
  have hk : (k : ℝ) ≤ prefixObjective S false mix (n k) := by
    have hscaled : (k : ℝ) < geometricPolicyWeight k *
        prefixObjective S false (π k) (n k) := by
      exact (div_lt_iff₀ (geometricPolicyWeight_pos k)).mp (hscore k) |>.trans_eq (mul_comm _ _)
    exact hscaled.le.trans (weighted_prefix_le_countable_mixture S false _ _ _ _ π k (n k))
  apply le_iSup_of_le (n k)
  simpa only [ENNReal.ofReal_natCast] using (ENNReal.ofReal_le_ofReal hk)

/-- Unbounded finite returns give an attained complete global maximum with
infinite expected value, and a fixed missed target with deficit one half. -/
theorem exists_complete_dominated_maximizer_of_unbounded (S : HistoryCompressor)
    (hu : ∀ B : ℝ, ∃ (π : Policy) (n : ℕ), B < prefixObjective S false π n) :
    ∃ (e : Bool) (π : Policy),
      π.1 [] e = 0 ∧
      completeObjective S e π = ⊤ ∧
      (∀ ρ : Policy, completeObjective S e ρ ≤ completeObjective S e π) ∧
      CausalFinitarilyGreatest (response e) (policy e) ∧
      CausalFinitaryDominates (response e) (policy e) π ∧
      ¬ CausalFinitaryDominates (response e) π (policy e) ∧
      (∀ t : ℕ, finiteDeficiency (causalFiniteExperiment π.1 (response e) t)
        (causalFiniteExperiment (policy e).1 (response e) 1) = 1 / 2) := by
  obtain ⟨e, he⟩ := exists_unbounded_root S hu
  obtain ⟨π, hroot, htop⟩ := exists_root_zero_complete_top S e he
  have htop' : completeObjective S e π = ⊤ := by
    rwa [completeObjective_eq S e false]
  refine ⟨e, π, hroot, htop', ?_, revealing_greatest e,
    (coin_strictly_dominated e π hroot).1, (coin_strictly_dominated e π hroot).2,
    fun t => coin_deficiency e π hroot t⟩
  intro ρ
  rw [htop']
  exact le_top

end
end IdExp.CompressionProgressIdeal
