import Formal.TwoBitChoiceInfeasibility
import Formal.StrictFinitaryObjective

/-!
# Undominated but incomplete policies in the irreversible two-bit interface

The exact target errors and root-record equivalence imply that finitary
comparison identifies precisely equal initial action probabilities. Thus every
policy is undominated, although no policy is natively sufficient.
-/

namespace IdExp.TwoBitChoice

/-- Finitary simulation cannot increase either fixed, time-constant target error. -/
theorem fixed_target_loss_le_of_dominates
    (π ρ : ValidCausalPolicy (Fin 2) (Fin 2))
    (hdom : CausalFinitaryDominates response π ρ)
    {Y : Type*} [Fintype Y] [Nonempty Y] (target : FiniteExperiment (Fin 4) Y)
    (a b : ℝ)
    (ha : ∀ t, finiteDeficiency (causalFiniteExperiment π.val response (t+1)) target = a)
    (hb : finiteDeficiency (causalFiniteExperiment ρ.val response 1) target = b) : a ≤ b := by
  by_contra h
  have hab : 0 < a - b := sub_pos.mpr (lt_of_not_ge h)
  obtain ⟨T, hT⟩ := hdom 1 (a-b) hab
  have hsmall := hT (T+1) (by omega)
  have htri := finiteDeficiency_triangle_of_fintype
    (causalFiniteExperiment π.val response (T+1))
    (causalFiniteExperiment ρ.val response 1) target
  rw [ha T, hb] at htri
  linarith

/-- The pair of native bit targets forces equal root mixing under any comparison. -/
theorem root_eq_of_finitaryDominates (π ρ : ValidCausalPolicy (Fin 2) (Fin 2))
    (hdom : CausalFinitaryDominates response π ρ) : π.val [] 0 = ρ.val [] 0 := by
  have hA := fixed_target_loss_le_of_dominates π ρ hdom testA
    ((1 - π.val [] 0) / 2) ((1 - ρ.val [] 0) / 2)
    (fun t => (prefix_target_errors π t).1) (prefix_target_errors ρ 0).1
  have hB := fixed_target_loss_le_of_dominates π ρ hdom testB
    (π.val [] 0 / 2) (ρ.val [] 0 / 2)
    (fun t => (prefix_target_errors π t).2) (prefix_target_errors ρ 0).2
  linarith

/-- Equal initial action probabilities give exact simulation of every target prefix. -/
theorem finitaryDominates_of_root_eq (π ρ : ValidCausalPolicy (Fin 2) (Fin 2))
    (heq : π.val [] 0 = ρ.val [] 0) : CausalFinitaryDominates response π ρ := by
  intro n ε hε
  refine ⟨1, fun t ht => ?_⟩
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  have hprefix : FiniteBlackwellLE (causalFiniteExperiment ρ.val response n)
      (causalFiniteExperiment ρ.val response (n+1)) :=
    causalFiniteExperiment_prefix_blackwell_of_le ρ.val ρ.property response response_valid
      (by omega)
  have hsource := (prefix_equiv π s).2
  rw [heq] at hsource
  have hbw := finiteBlackwellLE_trans hprefix
    (finiteBlackwellLE_trans (prefix_equiv ρ n).1 hsource)
  rw [finiteDeficiency_eq_zero_of_blackwellLE'
    (causalFiniteExperiment π.val response (s+1))
    (causalFiniteExperiment ρ.val response n)
    (causalFiniteExperiment_valid _ π.property _ response_valid _)
    (causalFiniteExperiment_valid _ ρ.property _ response_valid _) hbw]
  exact hε

/-- Complete characterization of the finitary preorder in this interface. -/
theorem finitaryDominates_iff_root_eq (π ρ : ValidCausalPolicy (Fin 2) (Fin 2)) :
    CausalFinitaryDominates response π ρ ↔ π.val [] 0 = ρ.val [] 0 :=
  ⟨root_eq_of_finitaryDominates π ρ, finitaryDominates_of_root_eq π ρ⟩

/-- Every policy is undominated, even though all policies are incomplete. -/
theorem every_policy_undominated_incomplete (π : ValidCausalPolicy (Fin 2) (Fin 2)) :
    (∀ ρ, CausalFinitaryDominates response ρ π → CausalFinitaryDominates response π ρ) ∧
    ¬ CausalNativelySufficient response π := by
  refine ⟨fun ρ hρ => ?_, no_natively_sufficient_policy π⟩
  exact finitaryDominates_of_root_eq π ρ (root_eq_of_finitaryDominates ρ π hρ).symm

#print axioms finitaryDominates_iff_root_eq
#print axioms every_policy_undominated_incomplete

end IdExp.TwoBitChoice
