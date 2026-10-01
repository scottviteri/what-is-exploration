import Formal.CausalSilentTail
import Formal.CausalUniversality
import Formal.CausalSharedTail

/-!
# Root experiments followed by a silent causal tail

An arbitrary finite family of root experiments becomes a valid causal class
by emitting one root signal and then a fixed observation forever. Every
positive prefix of every policy is exactly Blackwell-equivalent to its
recorded root action and observation. Every positive-depth deterministic
native test is equivalent to the root experiment selected by its first action.
These statements permit stochastic root rows and arbitrary world classes.
-/

namespace IdExp

open Finset Set

noncomputable section

set_option linter.unusedSectionVars false

variable {A O Θ : Type*} [Fintype A] [Fintype O]
  [DecidableEq A] [DecidableEq O] [Nonempty A] [Nonempty O]

/-- Deterministic signal processing for the finite encodings in this file. -/
def absorbingSignalRule {X Y : Type*} [Fintype Y] (f : X → Y) : X → Y → ℝ := by
  classical
  exact fun x y => if y = f x then 1 else 0

theorem absorbingSignalRule_valid {X Y : Type*} [Fintype Y] (f : X → Y) :
    absorbingSignalRule f ∈ stochasticRules X Y := by
  classical
  intro x _
  constructor
  · intro y
    by_cases h : y = f x <;> simp [absorbingSignalRule, h]
  · simp [absorbingSignalRule]

/-- Run the selected root experiment once, then emit a fixed silent symbol. -/
def absorbingResponse (o0 : O) (R : A → FiniteExperiment Θ O) (θ : Θ) : CausalResponse A O :=
  fun h a o => if h = [] then R a θ o else if o = o0 then 1 else 0

theorem absorbingResponse_valid (o0 : O) (R : A → FiniteExperiment Θ O)
    (hR : ∀ a, IsFiniteExperiment (R a)) (θ : Θ) :
    IsCausalResponse (absorbingResponse o0 R θ) := by
  intro h a
  by_cases hh : h = []
  · subst h
    change IsDist (R a θ)
    exact hR a θ
  · constructor
    · intro o
      by_cases ho : o = o0 <;> simp [absorbingResponse, hh, ho]
    · simp [absorbingResponse, hh]

/-- The absorbing model is the horizon-one case of a shared continuation. -/
theorem absorbingResponse_hasSharedTail (o0 : O) (R : A → FiniteExperiment Θ O) :
    HasSharedCausalTail (absorbingResponse o0 R) 1 (silentSymbolResponse o0) := by
  intro θ h a o hh
  have hne : h ≠ [] := by
    intro heq
    simp [heq] at hh
  simp [absorbingResponse, silentSymbolResponse, hne]

/-- The acquired root signal includes the randomized action label. -/
def absorbingRootExperiment (R : A → FiniteExperiment Θ O) (π : CausalPolicy A O) :
    FiniteExperiment Θ (A × O) :=
  fun θ ao => π [] ao.1 * R ao.1 θ ao.2

theorem absorbingRootExperiment_valid (R : A → FiniteExperiment Θ O)
    (hR : ∀ a, IsFiniteExperiment (R a)) (π : CausalPolicy A O)
    (hπ : IsCausalPolicy π) : IsFiniteExperiment (absorbingRootExperiment R π) := by
  intro θ
  constructor
  · intro ao
    exact mul_nonneg ((hπ []).1 ao.1) ((hR ao.1 θ).1 ao.2)
  · simp only [absorbingRootExperiment, Fintype.sum_prod_type, ← Finset.mul_sum,
      (hR _ _).2, mul_one]
    exact (hπ []).2

theorem causalTraceProbFrom_absorbing_eq_silent
    (o0 : O) (R : A → FiniteExperiment Θ O)
    (π : CausalPolicy A O) (θ : Θ)
    (pre rest : CausalHistory A O) (hpre : pre ≠ []) :
    causalTraceProbFrom π (absorbingResponse o0 R θ) pre rest =
      causalTraceProbFrom π (silentSymbolResponse o0) pre rest := by
  induction rest generalizing pre with
  | nil => rfl
  | cons ao rest ih =>
      simp only [causalTraceProbFrom]
      have hrow : absorbingResponse o0 R θ pre ao.1 ao.2 =
          silentSymbolResponse o0 pre ao.1 ao.2 := by
        simp [absorbingResponse, silentSymbolResponse, hpre]
      rw [hrow, ih (pre ++ [ao]) (by simp)]

/-- The continuation channel is independent of the world, even when later
policy actions adapt to and encode the observed root signal. -/
theorem absorbingCausalExperiment_eq_root_tail
    (o0 : O) (R : A → FiniteExperiment Θ O) (π : CausalPolicy A O) (n : ℕ) :
    causalFiniteExperiment π (absorbingResponse o0 R) (n + 1) =
      finiteDecisionLaw (absorbingRootExperiment R π) (unrestrictedSymbolTailRule o0 π n) := by
  classical
  funext θ w
  have hwlist : List.ofFn w = w 0 :: List.ofFn (Fin.tail w) := by
    simpa only [List.ofFn_cons] using congrArg List.ofFn (Fin.cons_self_tail w).symm
  change causalTraceProb π (absorbingResponse o0 R θ) (List.ofFn w) = _
  rw [hwlist]
  change π [] (w 0).1 * absorbingResponse o0 R θ [] (w 0).1 (w 0).2 *
      causalTraceProbFrom π (absorbingResponse o0 R θ) [w 0]
        (List.ofFn (Fin.tail w)) = _
  rw [causalTraceProbFrom_absorbing_eq_silent o0 R π θ [w 0]
    (List.ofFn (Fin.tail w)) (by simp)]
  unfold finiteDecisionLaw
  rw [Finset.sum_eq_single (w 0)]
  · simp [absorbingRootExperiment, unrestrictedSymbolTailRule, absorbingResponse]
  · intro ao _ hao
    simp [unrestrictedSymbolTailRule, Ne.symm hao]
  · simp

theorem absorbingCausalExperiment_one_root
    (o0 : O) (R : A → FiniteExperiment Θ O)
    (π : CausalPolicy A O) (θ : Θ) (w : CausalFiniteTrace A O 1) :
    causalFiniteExperiment π (absorbingResponse o0 R) 1 θ w =
      absorbingRootExperiment R π θ (w 0) := by
  simp [causalFiniteExperiment, causalTraceProb, List.ofFn_succ, causalTraceProbFrom,
    absorbingResponse, absorbingRootExperiment]

/-- The complete statistical content of every positive prefix is its root
action-observation pair. -/
theorem absorbingCausalExperiment_root_blackwell_equiv
    (o0 : O) (R : A → FiniteExperiment Θ O) (hR : ∀ a, IsFiniteExperiment (R a))
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π) (n : ℕ) :
    FiniteBlackwellLE (causalFiniteExperiment π (absorbingResponse o0 R) (n + 1))
        (absorbingRootExperiment R π) ∧
      FiniteBlackwellLE (absorbingRootExperiment R π)
        (causalFiniteExperiment π (absorbingResponse o0 R) (n + 1)) := by
  constructor
  · exact ⟨unrestrictedSymbolTailRule o0 π n,
      unrestrictedSymbolTailRule_mem_stochasticRules o0 π hπ n,
      (absorbingCausalExperiment_eq_root_tail o0 R π n).symm⟩
  · have hone : FiniteBlackwellLE (absorbingRootExperiment R π)
        (causalFiniteExperiment π (absorbingResponse o0 R) 1) := by
      refine ⟨absorbingSignalRule (fun w => w 0), absorbingSignalRule_valid _, ?_⟩
      funext θ ao
      unfold finiteDecisionLaw
      simp_rw [absorbingCausalExperiment_one_root]
      rw [← (Equiv.funUnique (Fin 1) (A × O)).symm.sum_comp]
      simp [absorbingSignalRule]
    exact finiteBlackwellLE_trans hone
      (causalFiniteExperiment_prefix_blackwell_of_le π hπ (absorbingResponse o0 R)
        (absorbingResponse_valid o0 R hR) (Nat.succ_le_succ (Nat.zero_le n)))

/-- The fixed first action selected by a positive-depth deterministic plan. -/
def absorbingPlanRoot (n : ℕ) (τ : CausalPlan A O (n + 1)) : A :=
  τ (causalDecisionPointOfHistory (n + 1) [] (by simp))

theorem absorbingPlan_rootPolicy (n : ℕ) (τ : CausalPlan A O (n + 1)) (a : A) :
    causalPolicyOfPlan (n + 1) τ [] a = if a = absorbingPlanRoot n τ then 1 else 0 := by
  simp [causalPolicyOfPlan, absorbingPlanRoot]
  congr 1

theorem absorbingPlanRoot_blackwell_equiv
    (R : A → FiniteExperiment Θ O) (n : ℕ) (τ : CausalPlan A O (n + 1)) :
    FiniteBlackwellLE (absorbingRootExperiment R (causalPolicyOfPlan (n + 1) τ))
        (R (absorbingPlanRoot n τ)) ∧
      FiniteBlackwellLE (R (absorbingPlanRoot n τ))
        (absorbingRootExperiment R (causalPolicyOfPlan (n + 1) τ)) := by
  classical
  constructor
  · refine ⟨absorbingSignalRule (fun o => (absorbingPlanRoot n τ, o)),
      absorbingSignalRule_valid _, ?_⟩
    funext θ ao
    unfold finiteDecisionLaw absorbingRootExperiment
    rw [absorbingPlan_rootPolicy]
    by_cases ha : ao.1 = absorbingPlanRoot n τ
    · simp [absorbingSignalRule, ha, Prod.ext_iff]
    · simp [absorbingSignalRule, Prod.ext_iff, ha]
  · refine ⟨absorbingSignalRule Prod.snd, absorbingSignalRule_valid _, ?_⟩
    funext θ o
    unfold finiteDecisionLaw absorbingRootExperiment
    simp_rw [absorbingPlan_rootPolicy]
    simp [absorbingSignalRule, Fintype.sum_prod_type]

/-- All adaptive deterministic interventions collapse to their chosen root
experiment; silent padding never creates additional native coordinates. -/
theorem absorbingNativeTest_all_depths_blackwell_equiv
    (o0 : O) (R : A → FiniteExperiment Θ O) (hR : ∀ a, IsFiniteExperiment (R a))
    (n : ℕ) (τ : CausalPlan A O (n + 1)) :
    FiniteBlackwellLE (causalPlanObservationExperiment (n + 1) τ (absorbingResponse o0 R))
        (R (absorbingPlanRoot n τ)) ∧
      FiniteBlackwellLE (R (absorbingPlanRoot n τ))
        (causalPlanObservationExperiment (n + 1) τ (absorbingResponse o0 R)) := by
  obtain ⟨hobs, hfull⟩ :=
    causalPlan_full_observation_blackwell_equiv (n + 1) τ (absorbingResponse o0 R)
  obtain ⟨htail, hroot⟩ := absorbingCausalExperiment_root_blackwell_equiv o0 R hR
    (causalPolicyOfPlan (n + 1) τ) (isCausalPolicy_causalPolicyOfPlan (n + 1) τ) n
  obtain ⟨hattach, hforget⟩ := absorbingPlanRoot_blackwell_equiv R n τ
  exact ⟨finiteBlackwellLE_trans hobs (finiteBlackwellLE_trans htail hattach),
    finiteBlackwellLE_trans hforget (finiteBlackwellLE_trans hroot hfull)⟩

end
end IdExp
