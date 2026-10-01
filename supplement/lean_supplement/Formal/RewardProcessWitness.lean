import Formal.SurrogateBlindness
import Formal.FiniteDecoderAttainment

/-!
# From literal revealing records to strict process witnesses

These helpers retain arbitrary randomized, history-dependent policies. A
finite record that decodes the world exactly simulates every finite record;
a policy whose every prefix is world-independent cannot recover a separated
record, however long it is allowed to collect.
-/

namespace IdExp

open Finset Set
noncomputable section

variable {Θ X Y : Type*} [Fintype X] [Fintype Y]

theorem revealingFiniteExperiment_dominates
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (decode : X → Θ) (hdecode : ∀ θ x, E θ x ≠ 0 → decode x = θ)
    (F : FiniteExperiment Θ Y) (hF : IsFiniteExperiment F) :
    FiniteBlackwellLE F E := by
  refine ⟨fun x => F (decode x), fun x _ => hF (decode x), ?_⟩
  funext θ y
  change (∑ x, E θ x * F (decode x) y) = F θ y
  calc
    (∑ x, E θ x * F (decode x) y) = ∑ x, E θ x * F θ y := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : E θ x = 0
      · simp [hx]
      · rw [hdecode θ x hx]
    _ = F θ y := by rw [← Finset.sum_mul, (hE θ).2, one_mul]

section Causal

variable {A O : Type*} [Fintype A] [Fintype O]
  [Nonempty A] [Nonempty O] [Fintype Θ] [Nonempty Θ]

theorem causalFinitarilyGreatest_of_revealing_prefix
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) (m : ℕ)
    (decode : CausalFiniteTrace A O m → Θ)
    (hdecode : ∀ θ w, causalFiniteExperiment π.1 Qs m θ w ≠ 0 → decode w = θ) :
    CausalFinitarilyGreatest Qs π := by
  intro ρ n ε hε
  refine ⟨m, ?_⟩
  intro t ht
  have hroot := revealingFiniteExperiment_dominates
    (causalFiniteExperiment π.1 Qs m)
    (causalFiniteExperiment_valid _ π.2 Qs hQ m) decode hdecode
    (causalFiniteExperiment ρ.1 Qs n)
    (causalFiniteExperiment_valid _ ρ.2 Qs hQ n)
  have h := finiteBlackwellLE_trans hroot
    (causalFiniteExperiment_prefix_blackwell_of_le π.1 π.2 Qs hQ ht)
  rw [finiteDeficiency_eq_zero_of_finiteBlackwellLE _ _ h]
  exact hε

end Causal

section Binary

variable {A O : Type*} [Fintype A] [Fintype O] [Nonempty A] [Nonempty O]

theorem classIndependent_prefixes_not_finitarily_dominate
    (Qs : Fin 2 → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π ρ : ValidCausalPolicy A O) (m : ℕ)
    (hclass : ∀ t, ClassIndependentFiniteExperiment (causalFiniteExperiment π.1 Qs t))
    (hsep : 0 < finiteTV (causalFiniteExperiment ρ.1 Qs m 0)
      (causalFiniteExperiment ρ.1 Qs m 1)) :
    ¬ CausalFinitaryDominates Qs π ρ := by
  intro hdom
  obtain ⟨T, hT⟩ := hdom m _ (half_pos hsep)
  have h := hT T le_rfl
  rw [finiteDeficiency_classIndependent_binary_eq_half_pairTV _ _
    (causalFiniteExperiment_valid _ π.2 Qs hQ T)
    (causalFiniteExperiment_valid _ ρ.2 Qs hQ m) (hclass T)] at h
  exact (lt_irrefl _ h)

end Binary
end
end IdExp
