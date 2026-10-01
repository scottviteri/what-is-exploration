import Formal.InformationDeficiencyContinuity
import Formal.CausalExperiment

/-!
# Expected observation surprisal is information plus world-conditional entropy

The primary paper's display (10): under the exact prior-predictive model on a
finite world class with a world-independent policy, the expected surprisal of
the newest observation equals the information gained by the newest step plus
the world-conditional entropy of that observation given the history and the
action.  Summing over steps gives

`E_α Σ_{t<H} −log P_α(O_{t+1} | H_t, A_{t+1}) = I_α(Q; H_H) + Σ_{t<H} H_α(O_{t+1} | Q, H_t, A_{t+1})`.

Everything is a finite identity on the actual causal prefix experiments
`causalFiniteExperiment`.  The prior-predictive conditional probability of the
newest observation is the ratio of the predictive masses of the two prefixes,
divided by the policy's action probability; terms with zero predictive mass
contribute zero.  The policy's own randomization cancels because it is the
same in every world.  No positivity of the prior is required.
-/

namespace IdExp

open Finset

variable {A O Θ : Type*} [Fintype A] [Fintype O] [Fintype Θ]

/-! ## Traces of length `n + 1` as a prefix and a last step -/

/-- Appending one action--observation pair to a finite trace. -/
theorem causalTraceProb_ofFn_snoc (π : CausalPolicy A O) (Q : CausalResponse A O)
    {n : ℕ} (u : CausalFiniteTrace A O n) (ao : A × O) :
    causalTraceProb π Q (List.ofFn (Fin.snoc u ao : Fin (n + 1) → A × O)) =
      causalTraceProb π Q (List.ofFn u) * π (List.ofFn u) ao.1 * Q (List.ofFn u) ao.1 ao.2 := by
  rw [List.ofFn_succ_last]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  exact causalTraceProb_append_singleton π Q (List.ofFn u) ao

/-- Summation over traces of length `n + 1` as a double sum over the prefix and
the newest pair. -/
theorem sum_trace_succ {n : ℕ} (f : CausalFiniteTrace A O (n + 1) → ℝ) :
    ∑ w, f w = ∑ u : CausalFiniteTrace A O n, ∑ ao : A × O, f (Fin.snoc u ao) := by
  have hsnoc : ∀ (ao : A × O) (u : CausalFiniteTrace A O n),
      (Fin.snocEquiv (fun _ : Fin (n + 1) => A × O)) (ao, u) = Fin.snoc u ao := by
    intro ao u
    funext i
    exact Fin.snocEquiv_apply _ _ i
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => A × O)).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun ao _ => ?_
  rw [hsnoc]

omit [Fintype Θ] in
theorem causalFiniteExperiment_snoc (π : CausalPolicy A O) (Qs : Θ → CausalResponse A O)
    {n : ℕ} (θ : Θ) (u : CausalFiniteTrace A O n) (ao : A × O) :
    causalFiniteExperiment π Qs (n + 1) θ (Fin.snoc u ao) =
      causalFiniteExperiment π Qs n θ u * π (List.ofFn u) ao.1 * Qs θ (List.ofFn u) ao.1 ao.2 := by
  unfold causalFiniteExperiment
  exact causalTraceProb_ofFn_snoc π (Qs θ) u ao

/-- Swapping an outer sum with two inner sums. -/
theorem sum_comm3 {U V : Type*} [Fintype U] [Fintype V] (f : Θ → U → V → ℝ) :
    ∑ θ, ∑ u, ∑ v, f θ u v = ∑ u, ∑ v, ∑ θ, f θ u v := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun u _ => Finset.sum_comm

/-! ## The quantities in the identity -/

variable (π : CausalPolicy A O) (Qs : Θ → CausalResponse A O) (α : Θ → ℝ)

/-- Joint prior mass of a prefix and a next observation under an action, with
the policy factor removed: `Σ_θ α_θ K_θ(u) Q_θ(u, a, o)`. -/
noncomputable def stepJointMass (n : ℕ) (u : CausalFiniteTrace A O n) (a : A) (o : O) : ℝ :=
  ∑ θ, α θ * (causalFiniteExperiment π Qs n θ u * Qs θ (List.ofFn u) a o)

/-- The prior-predictive conditional probability of the newest observation given
the history and the action: the ratio of predictive prefix masses divided by
the policy's action probability. -/
noncomputable def lastStepPredictive (n : ℕ) (w : CausalFiniteTrace A O (n + 1)) : ℝ :=
  finiteBayesMass α (causalFiniteExperiment π Qs (n + 1)) w /
    (finiteBayesMass α (causalFiniteExperiment π Qs n) (Fin.init w) *
      π (List.ofFn (Fin.init w)) (w (Fin.last n)).1)

/-- Expected surprisal of the newest observation, under the prior-predictive
law of length-`n+1` records. -/
noncomputable def expectedLastSurprisal (n : ℕ) : ℝ :=
  ∑ w, finiteBayesMass α (causalFiniteExperiment π Qs (n + 1)) w *
    (-Real.log (lastStepPredictive π Qs α n w))

/-- World-conditional entropy of the newest observation given the history and
the action, averaged under the joint law of world, history, and action. -/
noncomputable def stepConditionalEntropy (n : ℕ) : ℝ :=
  ∑ θ, α θ * ∑ u : CausalFiniteTrace A O n, causalFiniteExperiment π Qs n θ u *
    ∑ a, π (List.ofFn u) a * ent (Qs θ (List.ofFn u) a)

/-! ## Marginalization and mass identities -/

theorem finiteBayesMass_snoc {n : ℕ} (u : CausalFiniteTrace A O n) (ao : A × O) :
    finiteBayesMass α (causalFiniteExperiment π Qs (n + 1)) (Fin.snoc u ao) =
      π (List.ofFn u) ao.1 * stepJointMass π Qs α n u ao.1 ao.2 := by
  unfold finiteBayesMass stepJointMass
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun θ _ => ?_
  rw [causalFiniteExperiment_snoc]
  ring

omit [Fintype A] in
theorem sum_stepJointMass (hQ : ∀ θ, IsCausalResponse (Qs θ)) {n : ℕ}
    (u : CausalFiniteTrace A O n) (a : A) :
    ∑ o, stepJointMass π Qs α n u a o = finiteBayesMass α (causalFiniteExperiment π Qs n) u := by
  unfold stepJointMass finiteBayesMass
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun θ _ => ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum, (hQ θ _ a).2, mul_one]

theorem stepJointMass_nonneg (hα : ∀ θ, 0 ≤ α θ) (hπ : IsCausalPolicy π)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) {n : ℕ} (u : CausalFiniteTrace A O n) (a : A) (o : O) :
    0 ≤ stepJointMass π Qs α n u a o :=
  Finset.sum_nonneg fun θ _ => mul_nonneg (hα θ)
    (mul_nonneg (causalTraceProb_nonneg π hπ (Qs θ) (hQ θ) _) ((hQ θ _ a).1 o))

theorem stepJointMass_le_mass (hα : ∀ θ, 0 ≤ α θ) (hπ : IsCausalPolicy π)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) {n : ℕ} (u : CausalFiniteTrace A O n) (a : A) (o : O) :
    stepJointMass π Qs α n u a o ≤ finiteBayesMass α (causalFiniteExperiment π Qs n) u := by
  unfold stepJointMass finiteBayesMass
  refine Finset.sum_le_sum fun θ _ => ?_
  have hq1 : Qs θ (List.ofFn u) a o ≤ 1 := by
    have := Finset.single_le_sum (f := fun o' => Qs θ (List.ofFn u) a o')
      (fun o' _ => (hQ θ _ a).1 o') (Finset.mem_univ o)
    rw [(hQ θ _ a).2] at this
    exact this
  have hk := causalTraceProb_nonneg π hπ (Qs θ) (hQ θ) (List.ofFn u)
  calc α θ * (causalFiniteExperiment π Qs n θ u * Qs θ (List.ofFn u) a o)
      ≤ α θ * (causalFiniteExperiment π Qs n θ u * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq1 hk) (hα θ)
    _ = α θ * causalFiniteExperiment π Qs n θ u := by ring

/-- The newest-pair masses marginalize to the prefix mass. -/
theorem sum_finiteBayesMass_snoc (hπ : IsCausalPolicy π) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {n : ℕ} (u : CausalFiniteTrace A O n) :
    ∑ ao : A × O, finiteBayesMass α (causalFiniteExperiment π Qs (n + 1)) (Fin.snoc u ao) =
      finiteBayesMass α (causalFiniteExperiment π Qs n) u := by
  simp_rw [finiteBayesMass_snoc]
  rw [Fintype.sum_prod_type]
  show ∑ a, ∑ o, π (List.ofFn u) a * stepJointMass π Qs α n u a o = _
  calc ∑ a, ∑ o, π (List.ofFn u) a * stepJointMass π Qs α n u a o
      = ∑ a, π (List.ofFn u) a * finiteBayesMass α (causalFiniteExperiment π Qs n) u := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.mul_sum, sum_stepJointMass π Qs α hQ u a]
    _ = finiteBayesMass α (causalFiniteExperiment π Qs n) u := by
        rw [← Finset.sum_mul, (hπ _).2, one_mul]

/-! ## The per-term surprisal identity -/

/-- For a positive term, the surprisal of the newest observation is
`log M − log S` where `M` is the prefix mass and `S` the joint mass; zero
terms contribute zero on both sides. -/
theorem surprisal_term (P S M : ℝ) (hS : 0 ≤ S) (hSM : S ≤ M) :
    P * S * (-Real.log (P * S / (M * P))) = P * S * (Real.log M - Real.log S) := by
  by_cases hPS : P * S = 0
  · rw [hPS]; ring
  · have hP0 : P ≠ 0 := fun h => hPS (by rw [h, zero_mul])
    have hS0 : S ≠ 0 := fun h => hPS (by rw [h, mul_zero])
    have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hS0)
    have hM0 : M ≠ 0 := ne_of_gt (lt_of_lt_of_le hSpos hSM)
    rw [Real.log_div (mul_ne_zero hP0 hS0) (mul_ne_zero hM0 hP0), Real.log_mul hP0 hS0,
      Real.log_mul hM0 hP0]
    ring

/-! ## The one-step identity -/

theorem expectedLastSurprisal_eq (hα : IsDist α) (hπ : IsCausalPolicy π)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (n : ℕ) :
    expectedLastSurprisal π Qs α n =
      ∑ u : CausalFiniteTrace A O n, ∑ ao : A × O,
        π (List.ofFn u) ao.1 * stepJointMass π Qs α n u ao.1 ao.2 *
          (Real.log (finiteBayesMass α (causalFiniteExperiment π Qs n) u) -
            Real.log (stepJointMass π Qs α n u ao.1 ao.2)) := by
  unfold expectedLastSurprisal
  rw [sum_trace_succ]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun ao _ => ?_
  unfold lastStepPredictive
  rw [Fin.init_snoc, Fin.snoc_last, finiteBayesMass_snoc]
  exact surprisal_term _ _ _ (stepJointMass_nonneg π Qs α hα.1 hπ hQ u _ _)
    (stepJointMass_le_mass π Qs α hα.1 hπ hQ u _ _)

/-- Entropy increment of the predictive record law. -/
theorem ent_mass_succ_sub (hπ : IsCausalPolicy π) (hQ : ∀ θ, IsCausalResponse (Qs θ)) (n : ℕ) :
    ent (finiteBayesMass α (causalFiniteExperiment π Qs (n + 1))) -
        ent (finiteBayesMass α (causalFiniteExperiment π Qs n)) =
      ∑ u : CausalFiniteTrace A O n, ∑ ao : A × O,
        π (List.ofFn u) ao.1 * stepJointMass π Qs α n u ao.1 ao.2 *
          (Real.log (finiteBayesMass α (causalFiniteExperiment π Qs n) u) -
            Real.log (π (List.ofFn u) ao.1) - Real.log (stepJointMass π Qs α n u ao.1 ao.2)) := by
  unfold ent
  rw [sum_trace_succ, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hM := sum_finiteBayesMass_snoc π Qs α hπ hQ u
  have hpref : Real.negMulLog (finiteBayesMass α (causalFiniteExperiment π Qs n) u) =
      ∑ ao : A × O, finiteBayesMass α (causalFiniteExperiment π Qs (n + 1)) (Fin.snoc u ao) *
        (-Real.log (finiteBayesMass α (causalFiniteExperiment π Qs n) u)) := by
    rw [← Finset.sum_mul, hM]
    simp only [Real.negMulLog]
    ring
  rw [hpref, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ao _ => ?_
  rw [finiteBayesMass_snoc, Real.negMulLog_mul]
  simp only [Real.negMulLog]
  ring

/-- Entropy increment of one world's record law. -/
theorem ent_world_succ_sub (hπ : IsCausalPolicy π) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (n : ℕ) (θ : Θ) :
    ent (causalFiniteExperiment π Qs (n + 1) θ) - ent (causalFiniteExperiment π Qs n θ) =
      ∑ u : CausalFiniteTrace A O n, ∑ ao : A × O,
        causalFiniteExperiment π Qs n θ u * π (List.ofFn u) ao.1 * Qs θ (List.ofFn u) ao.1 ao.2 *
          (-Real.log (π (List.ofFn u) ao.1) - Real.log (Qs θ (List.ofFn u) ao.1 ao.2)) := by
  unfold ent
  rw [sum_trace_succ, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hone : ∑ ao : A × O, π (List.ofFn u) ao.1 * Qs θ (List.ofFn u) ao.1 ao.2 = 1 := by
    rw [Fintype.sum_prod_type]
    show ∑ a, ∑ o, π (List.ofFn u) a * Qs θ (List.ofFn u) a o = 1
    simp_rw [← Finset.mul_sum, (hQ θ _ _).2, mul_one]
    exact (hπ _).2
  have hpref : Real.negMulLog (causalFiniteExperiment π Qs n θ u) =
      ∑ ao : A × O, π (List.ofFn u) ao.1 * Qs θ (List.ofFn u) ao.1 ao.2 *
        Real.negMulLog (causalFiniteExperiment π Qs n θ u) := by
    rw [← Finset.sum_mul, hone, one_mul]
  rw [hpref, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ao _ => ?_
  rw [causalFiniteExperiment_snoc, mul_assoc, Real.negMulLog_mul, Real.negMulLog_mul]
  simp only [Real.negMulLog]
  ring

/-- The world-conditional step entropy as a sum over the newest pair. -/
theorem stepConditionalEntropy_eq (n : ℕ) :
    stepConditionalEntropy π Qs α n =
      ∑ u : CausalFiniteTrace A O n, ∑ ao : A × O, ∑ θ,
        α θ * (causalFiniteExperiment π Qs n θ u * (π (List.ofFn u) ao.1 *
          Real.negMulLog (Qs θ (List.ofFn u) ao.1 ao.2))) := by
  unfold stepConditionalEntropy ent
  rw [← sum_comm3]
  refine Finset.sum_congr rfl fun θ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Fintype.sum_prod_type]
  show α θ * (causalFiniteExperiment π Qs n θ u *
      ∑ a, π (List.ofFn u) a * ∑ o, Real.negMulLog (Qs θ (List.ofFn u) a o)) =
    ∑ a, ∑ o, α θ * (causalFiniteExperiment π Qs n θ u * (π (List.ofFn u) a *
      Real.negMulLog (Qs θ (List.ofFn u) a o)))
  simp_rw [Finset.mul_sum]

/-- The prior average of the world entropy increments splits into the policy's
own surprisal and the world-conditional step entropy. -/
theorem prior_avg_world_ent_succ_sub (hπ : IsCausalPolicy π)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (n : ℕ) :
    ∑ θ, α θ * (ent (causalFiniteExperiment π Qs (n + 1) θ) -
        ent (causalFiniteExperiment π Qs n θ)) =
      (∑ u : CausalFiniteTrace A O n, ∑ ao : A × O,
        π (List.ofFn u) ao.1 * stepJointMass π Qs α n u ao.1 ao.2 *
          (-Real.log (π (List.ofFn u) ao.1))) + stepConditionalEntropy π Qs α n := by
  simp_rw [ent_world_succ_sub π Qs hπ hQ n]
  rw [stepConditionalEntropy_eq]
  simp_rw [Finset.mul_sum]
  rw [sum_comm3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ao _ => ?_
  unfold stepJointMass
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun θ _ => ?_
  simp only [Real.negMulLog]
  ring

/-- **One-step surprisal identity.**  The expected surprisal of the newest
observation is the information gained by the newest step plus the
world-conditional entropy of that observation given history and action. -/
theorem expectedLastSurprisal_eq_information_add (hα : IsDist α) (hπ : IsCausalPolicy π)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (n : ℕ) :
    expectedLastSurprisal π Qs α n =
      (finiteBayesInformation α (causalFiniteExperiment π Qs (n + 1)) -
        finiteBayesInformation α (causalFiniteExperiment π Qs n)) +
      stepConditionalEntropy π Qs α n := by
  have hv : ∀ m, IsFiniteExperiment (causalFiniteExperiment π Qs m) :=
    fun m => causalFiniteExperiment_valid π hπ Qs hQ m
  rw [finiteBayesInformation_eq_ent_mass_sub α hα _ (hv (n + 1)),
    finiteBayesInformation_eq_ent_mass_sub α hα _ (hv n)]
  have h1 := ent_mass_succ_sub π Qs α hπ hQ n
  have h2 := prior_avg_world_ent_succ_sub π Qs α hπ hQ n
  have h3 := expectedLastSurprisal_eq π Qs α hα hπ hQ n
  have hsplit : ∑ θ, α θ * (ent (causalFiniteExperiment π Qs (n + 1) θ) -
      ent (causalFiniteExperiment π Qs n θ)) =
      ∑ θ, α θ * ent (causalFiniteExperiment π Qs (n + 1) θ) -
        ∑ θ, α θ * ent (causalFiniteExperiment π Qs n θ) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun θ _ => ?_
    ring
  have hgoal : (∑ u : CausalFiniteTrace A O n, ∑ ao : A × O,
        π (List.ofFn u) ao.1 * stepJointMass π Qs α n u ao.1 ao.2 *
          (Real.log (finiteBayesMass α (causalFiniteExperiment π Qs n) u) -
            Real.log (stepJointMass π Qs α n u ao.1 ao.2))) =
      (∑ u : CausalFiniteTrace A O n, ∑ ao : A × O,
        π (List.ofFn u) ao.1 * stepJointMass π Qs α n u ao.1 ao.2 *
          (Real.log (finiteBayesMass α (causalFiniteExperiment π Qs n) u) -
            Real.log (π (List.ofFn u) ao.1) - Real.log (stepJointMass π Qs α n u ao.1 ao.2))) -
      (∑ u : CausalFiniteTrace A O n, ∑ ao : A × O,
        π (List.ofFn u) ao.1 * stepJointMass π Qs α n u ao.1 ao.2 *
          (-Real.log (π (List.ofFn u) ao.1))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ao _ => ?_
    ring
  rw [h3, hgoal, ← h1]
  linarith [h2, hsplit]

/-! ## Summing over the horizon: the paper's display (10) -/

/-- The empty record carries no information. -/
theorem finiteBayesInformation_zero (hα : IsDist α) :
    finiteBayesInformation α (causalFiniteExperiment π Qs 0) = 0 := by
  have hK : ∀ θ (w : CausalFiniteTrace A O 0), causalFiniteExperiment π Qs 0 θ w = 1 := by
    intro θ w
    unfold causalFiniteExperiment
    rw [List.ofFn_zero]
    rfl
  have hv : IsFiniteExperiment (causalFiniteExperiment π Qs 0) := by
    intro θ
    refine ⟨fun w => by rw [hK]; norm_num, ?_⟩
    simp [hK]
  rw [finiteBayesInformation_eq_ent_mass_sub α hα _ hv]
  have hmass : ∀ w : CausalFiniteTrace A O 0,
      finiteBayesMass α (causalFiniteExperiment π Qs 0) w = 1 := by
    intro w
    unfold finiteBayesMass
    simp [hK, hα.2]
  unfold ent
  simp [hmass, hK]

/-- **The paper's display (10).**  Summed over a horizon `H`, the expected
observation surprisals equal the information carried by the length-`H` record
plus the sum of the world-conditional step entropies. -/
theorem sum_expectedLastSurprisal_eq (hα : IsDist α) (hπ : IsCausalPolicy π)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (H : ℕ) :
    ∑ s ∈ Finset.range H, expectedLastSurprisal π Qs α s =
      finiteBayesInformation α (causalFiniteExperiment π Qs H) +
        ∑ s ∈ Finset.range H, stepConditionalEntropy π Qs α s := by
  induction H with
  | zero => simp [finiteBayesInformation_zero π Qs α hα]
  | succ H ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih,
      expectedLastSurprisal_eq_information_add π Qs α hα hπ hQ H]
    ring

end IdExp
