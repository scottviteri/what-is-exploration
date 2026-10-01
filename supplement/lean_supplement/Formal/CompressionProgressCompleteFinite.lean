import Formal.CompressionProgressIdeal

/-!
# Finite complete-return attainment for exact integer-cost compression progress

The fixed learner is scored on every action-observation pair. In the two
repeated-bit classes, deterministic finite-plan values are half-integers.
A uniform finite upper bound therefore implies attained complete-return
optimality. Choosing the revealing button opposite the optimizer's root
makes the attained optimum permanently deficient by one half.
-/
namespace IdExp.CompressionProgressCompleteFinite
open CompressionProgressSwap CompressionProgressIdeal
open scoped ENNReal
noncomputable section

lemma runFrom_score_nat (S : HistoryCompressor) (old : S.Model)
    (archive D : History) : ∃ k : ℕ, (S.runFrom old archive D).2 = (k : ℝ) := by
  induction D generalizing old archive with
  | nil => exact ⟨0, by simp [IdealHistoryCompressor.Specification.runFrom]⟩
  | cons x D ih =>
    obtain ⟨k, hk⟩ := ih (S.update old (archive ++ [x])) (archive ++ [x])
    refine ⟨S.cost old (archive ++ [x]) -
      S.cost (S.update old (archive ++ [x])) (archive ++ [x]) + k, ?_⟩
    simp only [IdealHistoryCompressor.Specification.runFrom,
      IdealHistoryCompressor.Specification.gain, hk, Nat.cast_add]
    rw [Nat.cast_sub (S.update_minimizes old old (archive ++ [x]))]

lemma score_nat (S : HistoryCompressor) (D : History) :
    ∃ k : ℕ, S.score D = (k : ℝ) :=
  runFrom_score_nat S S.initial [] D

lemma planPolicy_nat (n : ℕ) (τ : CausalPlan Bool World n) (h : History) (a : Bool) :
    ∃ k : ℕ, (planPolicy n τ).1 h a = (k : ℝ) := by
  change ∃ k : ℕ, causalPolicyOfPlan n τ h a = (k : ℝ)
  unfold causalPolicyOfPlan
  split_ifs
  · exact ⟨1, by norm_num⟩
  · exact ⟨0, by norm_num⟩
  · exact ⟨1, by norm_num⟩
  · exact ⟨0, by norm_num⟩

lemma plan_tail_nat (n : ℕ) (τ : CausalPlan Bool World n) (e : Bool) (world : World)
    (pre rest : History) (hne : pre ≠ []) :
    ∃ k : ℕ, causalTraceProbFrom (planPolicy n τ).1 (response e world) pre rest =
      (k : ℝ) := by
  induction rest generalizing pre with
  | nil => exact ⟨1, by norm_num [causalTraceProbFrom]⟩
  | cons ao rest ih =>
    obtain ⟨i, hi⟩ := planPolicy_nat n τ pre ao.1
    obtain ⟨j, hj⟩ := ih (pre ++ [ao]) (by simp)
    simp only [causalTraceProbFrom, response, hne, ↓reduceIte, hi, hj]
    split_ifs
    · exact ⟨i * j, by push_cast; ring⟩
    · exact ⟨0, by simp⟩

lemma plan_average_twice_nat (m : ℕ) (τ : CausalPlan Bool World m)
    (e : Bool) (n : ℕ) (w : CausalFiniteTrace Bool World n) :
    ∃ k : ℕ, 2 * averageExperiment e (planPolicy m τ) n w = (k : ℝ) := by
  unfold averageExperiment causalFiniteExperiment
  cases hh : List.ofFn w with
  | nil => exact ⟨2, by norm_num [causalTraceProb, causalTraceProbFrom]⟩
  | cons ao rest =>
    simp only [causalTraceProb, causalTraceProbFrom, response, ↓reduceIte,
      List.nil_append]
    rw [tail_eq (planPolicy m τ).1 e e 1 0 [ao] rest (by simp)]
    obtain ⟨i, hi⟩ := planPolicy_nat m τ [] ao.1
    obtain ⟨j, hj⟩ := plan_tail_nat m τ e 0 [ao] rest (by simp)
    refine ⟨i * j, ?_⟩
    calc
      _ = (planPolicy m τ).1 [] ao.1 * (root e ao.1 0 ao.2 + root e ao.1 1 ao.2) *
          causalTraceProbFrom (planPolicy m τ).1 (response e 0) [ao] rest := by ring
      _ = (i * j : ℕ) := by rw [root_sum, mul_one, hi, hj]; norm_cast

/-- The finite deterministic-plan score is exactly a nonnegative half-integer. -/
theorem plan_prefix_twice_nat (S : HistoryCompressor) (n : ℕ)
    (τ : CausalPlan Bool World n) :
    ∃ k : ℕ, 2 * prefixObjective S false (planPolicy n τ) n = (k : ℝ) := by
  classical
  choose c hc using plan_average_twice_nat n τ false n
  choose s hs using fun w : CausalFiniteTrace Bool World n => score_nat S (List.ofFn w)
  refine ⟨∑ w, c w * s w, ?_⟩
  simp only [prefixObjective, objective, Finset.mul_sum, ← mul_assoc, hc, hs,
    Nat.cast_sum, Nat.cast_mul]

lemma prefixObjective_zero (S : HistoryCompressor) (e : Bool) (π : Policy) :
    prefixObjective S e π 0 = 0 := by
  simp [prefixObjective, objective, IdealHistoryCompressor.Specification.score,
    IdealHistoryCompressor.Specification.runFrom]

/-- A uniform bound on finite returns yields one finite deterministic plan
whose attained prefix value bounds every policy at every horizon. -/
theorem exists_uniformly_maximizing_plan (S : HistoryCompressor) (B : ℝ)
    (hbound : ∀ (π : Policy) (n : ℕ), prefixObjective S false π n ≤ B) :
    ∃ (n : ℕ) (τ : CausalPlan Bool World (n+1)), ∀ (π : Policy) (m : ℕ),
      prefixObjective S false π m ≤
        prefixObjective S false (planPolicy (n+1) τ) (n+1) := by
  classical
  let V : Set ℕ := {k | ∃ (n : ℕ) (τ : CausalPlan Bool World (n+1)),
    2 * prefixObjective S false (planPolicy (n+1) τ) (n+1) = (k : ℝ)}
  have hne : V.Nonempty := by
    let τ : CausalPlan Bool World 1 := fun _ => false
    obtain ⟨k, hk⟩ := plan_prefix_twice_nat S 1 τ
    exact ⟨k, 0, τ, hk⟩
  have hbounded : BddAbove V := by
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * B)
    refine ⟨N, ?_⟩
    rintro k ⟨n, τ, hk⟩
    have h : (k : ℝ) ≤ (N : ℝ) := by
      have := hbound (planPolicy (n+1) τ) (n+1)
      nlinarith
    exact_mod_cast h
  have hfinite : V.Finite := hbounded.finite
  obtain ⟨n, τ, hk⟩ := hne.csSup_mem hfinite
  refine ⟨n, τ, ?_⟩
  intro π m
  cases m with
  | zero =>
    rw [prefixObjective_zero]
    have h : (0 : ℝ) ≤ (sSup V : ℕ) := Nat.cast_nonneg _
    linarith
  | succ m =>
    obtain ⟨σ, hσ⟩ := exists_maximizing_plan (m+1)
      (fun w => S.score (List.ofFn w))
    obtain ⟨j, hj⟩ := plan_prefix_twice_nat S (m+1) σ
    have hjV : j ∈ V := ⟨m, σ, hj⟩
    have hjle : j ≤ sSup V := le_csSup hbounded hjV
    have hjle' : (j : ℝ) ≤ (sSup V : ℕ) := by exact_mod_cast hjle
    have hπ : prefixObjective S false π (m+1) ≤
        prefixObjective S false (planPolicy (m+1) σ) (m+1) := hσ π
    linarith

/-- Complete-return attainment from a finite bound, with an explicit root-zero
witness and the permanent native deficit. No complete maximizer is assumed. -/
theorem exists_complete_dominated_maximizer_of_prefix_bound
    (S : HistoryCompressor) (B : ℝ)
    (hbound : ∀ (π : Policy) (n : ℕ), prefixObjective S false π n ≤ B) :
    ∃ (e : Bool) (π : Policy),
      π.1 [] e = 0 ∧
      completeObjective S e π < ⊤ ∧
      (∀ ρ : Policy, completeObjective S e ρ ≤ completeObjective S e π) ∧
      CausalFinitarilyGreatest (response e) (policy e) ∧
      CausalFinitaryDominates (response e) (policy e) π ∧
      ¬ CausalFinitaryDominates (response e) π (policy e) ∧
      (∀ t : ℕ, finiteDeficiency (causalFiniteExperiment π.1 (response e) t)
        (causalFiniteExperiment (policy e).1 (response e) 1) = 1/2) := by
  obtain ⟨n, τ, hτ⟩ := exists_uniformly_maximizing_plan S B hbound
  let π := planPolicy (n+1) τ
  let a : Bool := τ (causalDecisionPointOfHistory (n+1) [] (by simp))
  have hroot : π.1 [] (!a) = 0 := by
    simp only [π, planPolicy, causalPolicyOfPlan, List.length_nil, Nat.zero_lt_succ,
      ↓reduceDIte]
    apply if_neg
    change (!a) ≠ a
    cases a <;> decide
  have hfinite : completeObjective S (!a) π < ⊤ := by
    apply lt_of_le_of_lt (b := ENNReal.ofReal B)
    · apply iSup_le
      intro m
      exact ENNReal.ofReal_le_ofReal (by
        simpa only [prefixObjective_eq S (!a) false] using hbound π m)
    · exact ENNReal.ofReal_lt_top
  have hmax (ρ : Policy) : completeObjective S (!a) ρ ≤ completeObjective S (!a) π := by
    apply iSup_le
    intro m
    apply le_iSup_of_le (n+1)
    exact ENNReal.ofReal_le_ofReal (by
      simpa only [prefixObjective_eq S (!a) false] using hτ ρ m)
  exact ⟨!a, π, hroot, hfinite, hmax, revealing_greatest (!a),
    (coin_strictly_dominated (!a) π hroot).1,
    (coin_strictly_dominated (!a) π hroot).2, coin_deficiency (!a) π hroot⟩

/-- The finite-supremum formulation: finiteness is a bound, not an assumed
attainment property. The resulting complete optimum is finite and deficient. -/
theorem exists_complete_dominated_maximizer_of_finite_supremum
    (S : HistoryCompressor)
    (hfinite : (⨆ π : Policy, completeObjective S false π) < ⊤) :
    ∃ (e : Bool) (π : Policy),
      π.1 [] e = 0 ∧
      completeObjective S e π < ⊤ ∧
      (∀ ρ : Policy, completeObjective S e ρ ≤ completeObjective S e π) ∧
      CausalFinitarilyGreatest (response e) (policy e) ∧
      CausalFinitaryDominates (response e) (policy e) π ∧
      ¬ CausalFinitaryDominates (response e) π (policy e) ∧
      (∀ t : ℕ, finiteDeficiency (causalFiniteExperiment π.1 (response e) t)
        (causalFiniteExperiment (policy e).1 (response e) 1) = 1/2) := by
  apply exists_complete_dominated_maximizer_of_prefix_bound S
    (⨆ π : Policy, completeObjective S false π).toReal
  intro π n
  apply (ENNReal.ofReal_le_iff_le_toReal hfinite.ne).mp
  calc
    ENNReal.ofReal (prefixObjective S false π n) ≤ completeObjective S false π :=
      le_iSup (fun n => ENNReal.ofReal (prefixObjective S false π n)) n
    _ ≤ ⨆ ρ : Policy, completeObjective S false ρ :=
      le_iSup (completeObjective S false) π

end
end IdExp.CompressionProgressCompleteFinite
