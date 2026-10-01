import Formal.CausalExperiment
import Formal.FiniteTV

/-!
# Causal experiments with a world-independent continuation

Once all candidate worlds use the same response law after depth k, a
world-independent decoder can continue any recorded k-prefix under the
policy. Every later finite experiment is exactly Blackwell-equivalent to
that prefix. The shared law may depend on the entire history: it need not
be constant, deterministic, or a reset.
-/

namespace IdExp

open Finset Set

variable {A O Θ : Type*} [Fintype A] [Fintype O]

/-- Every candidate world has the same continuation kernel after depth k. -/
def HasSharedCausalTail (Qs : Θ → CausalResponse A O) (k : ℕ)
    (R : CausalResponse A O) : Prop :=
  ∀ θ h a o, k ≤ h.length → Qs θ h a o = R h a o

/-- Append one action-observation pair using the policy and the shared
response law, retaining the entire input prefix. -/
noncomputable def causalSharedTailRule (π : CausalPolicy A O)
    (R : CausalResponse A O) (n : ℕ) :
    CausalFiniteTrace A O n → CausalFiniteTrace A O (n + 1) → ℝ := by
  classical
  exact fun u v => if u = Fin.init v then
    π (List.ofFn u) (v (Fin.last n)).1 *
      R (List.ofFn u) (v (Fin.last n)).1 (v (Fin.last n)).2 else 0

omit [Fintype A] [Fintype O] in
theorem causalSharedTailRule_snoc [DecidableEq A] [DecidableEq O] (π : CausalPolicy A O)
    (R : CausalResponse A O) (n : ℕ) (u v : CausalFiniteTrace A O n)
    (ao : A × O) :
    causalSharedTailRule π R n u (Fin.snoc v ao) =
      if u = v then π (List.ofFn u) ao.1 * R (List.ofFn u) ao.1 ao.2 else 0 := by
  classical
  simp [causalSharedTailRule]

theorem causalSharedTailRule_valid (π : CausalPolicy A O)
    (hπ : IsCausalPolicy π) (R : CausalResponse A O)
    (hR : IsCausalResponse R) (n : ℕ) :
    causalSharedTailRule π R n ∈
      stochasticRules (CausalFiniteTrace A O n) (CausalFiniteTrace A O (n + 1)) := by
  classical
  intro u _
  constructor
  · intro v
    unfold causalSharedTailRule
    split_ifs
    · exact mul_nonneg ((hπ _).1 _) ((hR _ _).1 _)
    · exact le_rfl
  · rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => A × O)).sum_comp]
    rw [Fintype.sum_prod_type]
    have hsnoc (ao : A × O) (v : CausalFiniteTrace A O n) :
        (Fin.snocEquiv (fun _ : Fin (n + 1) => A × O)) (ao, v) =
          Fin.snoc v ao := by
      funext i
      exact Fin.snocEquiv_apply _ _ i
    simp_rw [hsnoc, causalSharedTailRule_snoc]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, (hR _ _).2, mul_one]
    exact (hπ _).2

/-- Exact one-step extension, with no posterior or positive-prefix assumption. -/
theorem causalFiniteExperiment_sharedTail_step
    (π : CausalPolicy A O) (Qs : Θ → CausalResponse A O)
    (R : CausalResponse A O) (k n : ℕ) (htail : HasSharedCausalTail Qs k R)
    (hn : k ≤ n) :
    finiteDecisionLaw (causalFiniteExperiment π Qs n) (causalSharedTailRule π R n) =
      causalFiniteExperiment π Qs (n + 1) := by
  classical
  funext θ v
  unfold finiteDecisionLaw
  simp only [causalSharedTailRule, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  unfold causalFiniteExperiment
  rw [List.ofFn_succ_last, causalTraceProb_append_singleton]
  simp only [Fin.init_def]
  rw [htail θ (List.ofFn (fun i : Fin n => v i.castSucc)) _ _ (by simpa using hn)]
  ring

theorem causalFiniteExperiment_sharedTail_step_blackwell
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (R : CausalResponse A O)
    (hR : IsCausalResponse R) (k n : ℕ) (htail : HasSharedCausalTail Qs k R)
    (hn : k ≤ n) :
    FiniteBlackwellLE (causalFiniteExperiment π Qs (n + 1))
      (causalFiniteExperiment π Qs n) :=
  ⟨causalSharedTailRule π R n, causalSharedTailRule_valid π hπ R hR n,
    causalFiniteExperiment_sharedTail_step π Qs R k n htail hn⟩

/-- A recorded k-prefix simulates every later finite history exactly. -/
theorem causalFiniteExperiment_of_sharedTail_blackwell
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (R : CausalResponse A O)
    (hR : IsCausalResponse R) (k : ℕ) (htail : HasSharedCausalTail Qs k R)
    {n : ℕ} (hn : k ≤ n) :
    FiniteBlackwellLE (causalFiniteExperiment π Qs n)
      (causalFiniteExperiment π Qs k) := by
  exact Nat.le_induction (finiteBlackwellLE_refl _)
    (fun m hm ih => finiteBlackwellLE_trans
      (causalFiniteExperiment_sharedTail_step_blackwell π hπ Qs R hR k m htail hm) ih)
    n hn

/-- The entire finite experiment process stops gaining information at k. -/
theorem causalFiniteExperiment_sharedTail_blackwell_equiv
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (R : CausalResponse A O) (hR : IsCausalResponse R)
    (k : ℕ) (htail : HasSharedCausalTail Qs k R) {n : ℕ} (hn : k ≤ n) :
    FiniteBlackwellLE (causalFiniteExperiment π Qs n)
      (causalFiniteExperiment π Qs k) ∧
    FiniteBlackwellLE (causalFiniteExperiment π Qs k)
      (causalFiniteExperiment π Qs n) :=
  ⟨causalFiniteExperiment_of_sharedTail_blackwell π hπ Qs R hR k htail hn,
    causalFiniteExperiment_prefix_blackwell_of_le π hπ Qs hQ hn⟩

theorem causalFiniteExperiment_sharedTail_pairTV
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (R : CausalResponse A O) (hR : IsCausalResponse R)
    (k : ℕ) (htail : HasSharedCausalTail Qs k R) {n : ℕ} (hn : k ≤ n)
    (θ η : Θ) :
    finiteTV (causalFiniteExperiment π Qs n θ) (causalFiniteExperiment π Qs n η) =
      finiteTV (causalFiniteExperiment π Qs k θ) (causalFiniteExperiment π Qs k η) := by
  obtain ⟨⟨G, hG, hGE⟩, ⟨H, hH, hHE⟩⟩ :=
    causalFiniteExperiment_sharedTail_blackwell_equiv π hπ Qs hQ R hR k htail hn
  apply le_antisymm
  · have h := finiteTV_decisionLaw_le (causalFiniteExperiment π Qs k) G hG θ η
    rwa [hGE] at h
  · have h := finiteTV_decisionLaw_le (causalFiniteExperiment π Qs n) H hH θ η
    rwa [hHE] at h

end IdExp
