import Formal.ControlEntropy
import Formal.PriorFreeScores
import Formal.DeterministicDeficiency

/-!
# Capacity of finite deterministic control channels

The input index of `capacity` is an action here. Its supremum ranges over
hypothetical action distributions, independently of the policy whose state
visits are being evaluated. Injective deterministic channels have capacity
log(card actions); constant channels have capacity zero.
-/

namespace IdExp

open Finset Set

noncomputable section

variable {A O : Type*} [Fintype A] [Nonempty A] [Fintype O]

omit [Nonempty A] in
/-- Complete observation of the channel input retains all its entropy. -/
theorem finiteBayesInformation_dirac_id (ν : A → ℝ) (hν : IsDist ν) :
    finiteBayesInformation ν (diracExp (id : A → A)) = ent ν := by
  classical
  rw [finiteBayesInformation_eq_ent_mass_sub ν hν _ (diracExp_valid _)]
  have hm : finiteBayesMass ν (diracExp (id : A → A)) = ν := by
    funext a
    simp [finiteBayesMass, diracExp]
  rw [hm]
  simp only [diracExp_eq_pi_single, ent_simplex_vertex, mul_zero, sum_const_zero, sub_zero]

omit [Nonempty A] in
/-- A constant action-to-observation channel carries no input information. -/
theorem finiteBayesInformation_dirac_const (ν : A → ℝ) (hν : IsDist ν) (o : O) :
    finiteBayesInformation ν (diracExp (fun _ : A => o)) = 0 := by
  classical
  rw [finiteBayesInformation_eq_ent_mass_sub ν hν _ (diracExp_valid _)]
  have hm : finiteBayesMass ν (diracExp (fun _ : A => o)) = Pi.single o 1 := by
    funext x
    simp [finiteBayesMass, diracExp, hν.2, Pi.single_apply]
  rw [hm]
  simp only [diracExp_eq_pi_single, ent_simplex_vertex, mul_zero, sum_const_zero, sub_zero]

/-- The uniform hypothetical input realizes the identity channel capacity. -/
theorem capacity_dirac_id : capacity (diracExp (id : A → A)) = Real.log (Fintype.card A) := by
  classical
  have hmax : IsMaxOn (fun ν => finiteBayesInformation ν (diracExp (id : A → A)))
      (stdSimplex ℝ A) (uniformPrior A) := by
    apply isMaxOn_iff.2
    intro ν hν
    rw [finiteBayesInformation_dirac_id ν hν,
      finiteBayesInformation_dirac_id _ isDist_uniformPrior, ent_uniformPrior]
    exact ent_le_log_card ν hν
  rw [capacity_eq_of_isMaxOn _ isDist_uniformPrior hmax,
    finiteBayesInformation_dirac_id _ isDist_uniformPrior, ent_uniformPrior]

/-- Exact action encodings retain the identity channel's capacity. -/
theorem capacity_dirac_injective [Nonempty O] (f : A → O) (hf : Function.Injective f) :
    capacity (diracExp f) = Real.log (Fintype.card A) := by
  have hto : finiteDeficiency (diracExp (id : A → A)) (diracExp f) = 0 :=
    finiteDeficiency_diracExp_eq_zero_of_separates (fun a b h => congrArg f h)
  have hfrom : finiteDeficiency (diracExp f) (diracExp (id : A → A)) = 0 :=
    finiteDeficiency_diracExp_eq_zero_of_separates (fun a b h => hf h)
  rw [← capacity_dirac_id (A := A)]
  exact le_antisymm (capacity_mono _ (diracExp_valid _) _ hto)
    (capacity_mono _ (diracExp_valid _) _ hfrom)

theorem capacity_dirac_const (o : O) : capacity (diracExp (fun _ : A => o)) = 0 := by
  classical
  have hmax : IsMaxOn (fun ν => finiteBayesInformation ν (diracExp (fun _ : A => o)))
      (stdSimplex ℝ A) (uniformPrior A) := by
    apply isMaxOn_iff.2
    intro ν hν
    rw [finiteBayesInformation_dirac_const ν hν,
      finiteBayesInformation_dirac_const _ isDist_uniformPrior]
  rw [capacity_eq_of_isMaxOn _ isDist_uniformPrior hmax,
    finiteBayesInformation_dirac_const _ isDist_uniformPrior]

omit [Nonempty A] in
/-- Marginalizing a full retained record recovers the original root-action
probability, for every valid controlled response and arbitrary later policy. -/
theorem causalFiniteExperiment_root_action_mass [DecidableEq A]
    {Θ : Type*} (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) (n : ℕ) (θ : Θ) (a : A) :
    (∑ w : CausalFiniteTrace A O (n+1),
      if (w 0).1 = a then causalFiniteExperiment π.1 Qs (n+1) θ w else 0) =
      π.1 [] a := by
  classical
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => A × O)).sum_comp]
  rw [Fintype.sum_prod_type]
  have hcons (ao : A × O) (r : CausalFiniteTrace A O n) :
      (Fin.consEquiv (fun _ : Fin (n+1) => A × O)) (ao,r) = Fin.cons ao r := rfl
  simp_rw [hcons]
  simp only [Fin.cons_zero, causalFiniteExperiment, List.ofFn_cons,
    causalTraceProb, causalTraceProbFrom, List.nil_append]
  have hsum (ao : A × O) :
      (∑ r : CausalFiniteTrace A O n,
        if ao.1 = a then π.1 [] ao.1 * Qs θ [] ao.1 ao.2 *
          causalTraceProbFrom π.1 (Qs θ) [ao] (List.ofFn r) else 0) =
      if ao.1 = a then π.1 [] ao.1 * Qs θ [] ao.1 ao.2 else 0 := by
    by_cases h : ao.1 = a
    · simp only [if_pos h, ← Finset.mul_sum, sum_causalTraceProbFrom π.1 π.2 _ (hQ θ), mul_one]
    · simp [h]
  simp_rw [hsum]
  rw [Fintype.sum_prod_type]
  simp [← Finset.mul_sum, (hQ θ [] a).2]

end

end IdExp
