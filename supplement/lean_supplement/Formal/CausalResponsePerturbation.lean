import Formal.CausalSharedTail
import Formal.ApproximateResetSchedule

/-!
# One-step response perturbations on actual causal histories

The same randomized, history-dependent policy is run in two response worlds.
At each step, TV between the two trace-extension kernels is the policy-weighted
average of the observation-row TV errors. A uniform row error `δ` therefore
gives full recorded-history error at most `n * δ`, not just a bound for an
abstract finite-state rollout. Native-depth distance inherits the same bound.

The reset corollaries use this calculation at supported reset endpoints and
instantiate the actual varying-word infinite scheduler. In particular the
limit assumption is `t k * δ k → 0`, not merely `δ k → 0`.
-/

namespace IdExp

open Finset Set Filter Topology
open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

variable {A O Θ : Type*} [Fintype A] [Fintype O]

/-- The row TV of the actual one-step extension is precisely the policy
average of the response-row TVs. The appended actions stay in the signal. -/
theorem causalSharedTailRule_tv_eq (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Q R : CausalResponse A O) (n : ℕ) (u : CausalFiniteTrace A O n) :
    finiteTV (causalSharedTailRule π Q n u) (causalSharedTailRule π R n u) =
      ∑ a, π (List.ofFn u) a * finiteTV (Q (List.ofFn u) a) (R (List.ofFn u) a) := by
  classical
  unfold finiteTV
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => A × O)).sum_comp,
    Fintype.sum_prod_type]
  have hsnoc (ao : A × O) (v : CausalFiniteTrace A O n) :
      (Fin.snocEquiv (fun _ : Fin (n + 1) => A × O)) (ao, v) = Fin.snoc v ao := by
    funext i
    exact Fin.snocEquiv_apply _ _ i
  simp_rw [hsnoc, causalSharedTailRule_snoc]
  have hd (ao : A × O) (v : CausalFiniteTrace A O n) :
      |(if u = v then π (List.ofFn u) ao.1 * Q (List.ofFn u) ao.1 ao.2 else 0) -
        (if u = v then π (List.ofFn u) ao.1 * R (List.ofFn u) ao.1 ao.2 else 0)| =
      if u = v then |π (List.ofFn u) ao.1 *
        (Q (List.ofFn u) ao.1 ao.2 - R (List.ofFn u) ao.1 ao.2)| else 0 := by
    split_ifs <;> simp [mul_sub]
  simp_rw [hd]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Fintype.sum_prod_type]
  simp_rw [abs_mul, abs_of_nonneg ((hπ _).1 _)]
  simp_rw [← Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Uniform observation-row error controls each full trace-extension row. -/
theorem causalSharedTailRule_tv_le (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Q R : CausalResponse A O) (n : ℕ) (δ : ℝ)
    (hlocal : ∀ h a, finiteTV (Q h a) (R h a) ≤ δ)
    (u : CausalFiniteTrace A O n) :
    finiteTV (causalSharedTailRule π Q n u) (causalSharedTailRule π R n u) ≤ δ := by
  rw [causalSharedTailRule_tv_eq π hπ]
  calc
    ∑ a, π (List.ofFn u) a * finiteTV (Q (List.ofFn u) a) (R (List.ofFn u) a) ≤
        ∑ a, π (List.ofFn u) a * δ :=
      Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hlocal _ a) ((hπ _).1 a)
    _ = δ := by rw [← Finset.sum_mul, (hπ _).2, one_mul]

/-- The actual history-dependent causal telescope, for every randomized
policy and every finite horizon, including zero. -/
theorem causalFiniteExperiment_tv_le_mul (π : CausalPolicy A O)
    (hπ : IsCausalPolicy π) (Q R : CausalResponse A O)
    (hQ : IsCausalResponse Q) (hR : IsCausalResponse R) (δ : ℝ)
    (hlocal : ∀ h a, finiteTV (Q h a) (R h a) ≤ δ) (n : ℕ) :
    finiteTV (causalFiniteExperiment π (fun _ : Unit => Q) n ())
      (causalFiniteExperiment π (fun _ : Unit => R) n ()) ≤ (n : ℝ) * δ := by
  induction n with
  | zero => simp [finiteTV, causalFiniteExperiment, causalTraceProb, causalTraceProbFrom]
  | succ n ih =>
      have hstep (S : CausalResponse A O) :
          causalFiniteExperiment π (fun _ : Unit => S) (n + 1) () =
          PredictiveTransport.finiteBind
            (causalFiniteExperiment π (fun _ : Unit => S) n ())
            (causalSharedTailRule π S n) := by
        exact (congrFun (causalFiniteExperiment_sharedTail_step π (fun _ : Unit => S)
          S 0 n (fun _ _ _ _ _ => rfl) (Nat.zero_le n)) ()).symm
      rw [hstep Q, hstep R]
      have hb := PredictiveTransport.finiteTV_finiteBind_le
        (causalFiniteExperiment π (fun _ : Unit => Q) n ())
        (causalFiniteExperiment π (fun _ : Unit => R) n ())
        (causalFiniteExperiment_valid π hπ _ (fun _ => hQ) n ())
        (causalSharedTailRule π Q n) (causalSharedTailRule π R n)
        (causalSharedTailRule_valid π hπ R hR n)
        (causalSharedTailRule_tv_le π hπ Q R n δ hlocal)
      push_cast
      linarith

variable [Nonempty A] [Nonempty O]

/-- The native maximum is bounded by horizon times the uniform one-step
response error. No finite-state or Markov assumption is required. -/
theorem nativeDepthDist_le_mul_of_responseTV (Q R : ValidCausalWorld A O)
    (δ : ℝ) (hlocal : ∀ h a, finiteTV (Q.val h a) (R.val h a) ≤ δ) (n : ℕ) :
    nativeDepthDist n Q R ≤ (n : ℝ) * δ := by
  classical
  apply Finset.sup'_le
  intro τ _
  rw [← nativePlan_full_tv_eq]
  exact causalFiniteExperiment_tv_le_mul (causalPolicyOfPlan n τ)
    (isCausalPolicy_causalPolicyOfPlan n τ) Q.val R.val Q.property R.property δ hlocal n

/-- One-step reset error, imposed only at reachable reset endpoints.
Unlike native reset distance, the subsequent row condition is a stronger
raw-kernel condition at every within-block history. -/
def IsCausalOneStepResetWord {ℓ : ℕ} (Q : CausalResponse A O)
    (r : Fin ℓ → A) (δ : ℝ) : Prop :=
  ∀ (pre : CausalHistory A O) (ys : Fin ℓ → O),
    causalResponseProb Q (pre ++ List.ofFn (fun i => (r i, ys i))) ≠ 0 →
      ∀ h a, finiteTV
        (causalResponseAfter Q (pre ++ List.ofFn (fun i => (r i, ys i))) h a)
        (Q h a) ≤ δ

/-- The one-step reset premise discharges the native-depth reset premise
with exactly the stated horizon factor. -/
theorem IsCausalOneStepResetWord.atDepth {ℓ : ℕ} (Q : CausalResponse A O)
    (hQ : IsCausalResponse Q) (r : Fin ℓ → A) (δ : ℝ)
    (hr : IsCausalOneStepResetWord Q r δ) (n : ℕ) :
    IsCausalResetWordAtDepth Q hQ r n ((n : ℝ) * δ) := by
  intro pre ys hp
  exact nativeDepthDist_le_mul_of_responseTV _ _ δ (hr pre ys hp) n

variable [Nonempty Θ]

/-- Deterministic extraction after a one-step approximate reset has
full-history error at most the target horizon times the response-row error. -/
theorem oneStepResetWord_block_projection_tv_le {ℓ : ℕ} (m n : ℕ)
    (ρ : CausalPolicy A O) (hρ : IsCausalPolicy ρ) (r : Fin ℓ → A)
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ)) (δ : ℝ)
    (hr : ∀ θ, IsCausalOneStepResetWord (Qs θ) r δ) (θ : Θ) :
    finiteTV
      (finiteDecisionLaw
        (causalFiniteExperiment (causalResetSplicePolicy m ρ r π) Qs ((m + ℓ) + n))
        (finiteMapRule (causalBlockProjection (m + ℓ) n)) θ)
      (causalFiniteExperiment π Qs n θ) ≤ (n : ℝ) * δ :=
  approximateResetWord_block_projection_tv_le m n ρ hρ r π hπ Qs hQ _
    (fun θ => (hr θ).atDepth _ (hQ θ) r δ n) θ

/-- The one-step corollary at the actual variable schedule's cumulative
time, with no conditional-law or independence hypothesis. -/
theorem varyingOneStepResetSchedule_block_deficiency_le (ℓ : ℕ → ℕ)
    (r : (k : ℕ) → Fin (ℓ k) → A) (π : ℕ → ValidCausalPolicy A O) (t : ℕ → ℕ)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (δ : ℕ → ℝ) (hr : ∀ k θ, IsCausalOneStepResetWord (Qs θ) (r k) (δ k)) (k : ℕ) :
    finiteDeficiency
      (causalFiniteExperiment (varyingResetSchedulePolicy ℓ r π t) Qs
        (varyingResetClock ℓ t (k + 1)))
      (causalFiniteExperiment (π k).1 Qs (t k)) ≤ (t k : ℝ) * δ k :=
  varyingResetSchedule_block_deficiency_le ℓ r π t Qs hQ _
    (fun k θ => (hr k θ).atDepth _ (hQ θ) (r k) (δ k) (t k)) k

/-- **One-step approximate-reset Pareto collapse.** The actual infinite
spliced policy attains the scheme's Pareto limit when `t k * δ k → 0`. -/
theorem varyingOneStepResetSchedule_profile_eq_of_pareto (ℓ : ℕ → ℕ)
    (r : (k : ℕ) → Fin (ℓ k) → A) (π : ℕ → ValidCausalPolicy A O) (t : ℕ → ℕ)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (δ : ℕ → ℝ) (hδ : Tendsto (fun k => (t k : ℝ) * δ k) atTop (𝓝 0))
    (hr : ∀ k θ, IsCausalOneStepResetWord (Qs θ) (r k) (δ k))
    (e : ℕ ≃ CausalNativeTest A O) (p : ProfileCube)
    (hp : p ∈ causalParetoFrontier Qs hQ e)
    (hlim : ∀ j, Tendsto
      (fun k => causalPolicyTestDeficiency (π k) Qs (e j) (t k)) atTop (𝓝 (p j : ℝ))) :
    causalPolicyProfile Qs hQ e
      ⟨varyingResetSchedulePolicy ℓ r π t, varyingResetSchedulePolicy_valid ℓ r π t⟩ = p :=
  varyingResetSchedule_profile_eq_of_pareto ℓ r π t Qs hQ _ hδ
    (fun k θ => (hr k θ).atDepth _ (hQ θ) (r k) (δ k) (t k)) e p hp hlim

end
end IdExp
