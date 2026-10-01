import Formal.CausalProcess
import Formal.FinitaryObjectiveCore

/-!
# Objective order and native sufficiency

Shared qualitative completion arguments. Concrete objective families supply
their monotonicity and strictness hypotheses, retaining their separate analytic
or quantitative proofs. Existence of a sufficient policy stays explicit.
-/

namespace IdExp

variable {A O Θ : Type*} [Fintype A] [Fintype O]
  [Nonempty A] [Nonempty O] [Nonempty Θ]

theorem causalNativelySufficient_of_strict_objective_eq
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (J : ValidCausalPolicy A O → ℝ)
    (hstrict : ∀ π σ, CausalFinitaryDominates Qs π σ →
      ¬ CausalFinitaryDominates Qs σ π → J σ < J π)
    {π σ : ValidCausalPolicy A O} (hπns : CausalNativelySufficient Qs π)
    (heq : J σ = J π) : CausalNativelySufficient Qs σ := by
  have hπg := (causalNativelySufficient_iff_finitarilyGreatest Qs hQ π).1 hπns
  have hσπ : CausalFinitaryDominates Qs σ π := by
    by_contra hnot
    exact (ne_of_lt (hstrict π σ (hπg σ) hnot)) heq
  rw [causalNativelySufficient_iff_finitarilyGreatest Qs hQ]
  exact fun ρ => causalFinitaryDominates_trans Qs hQ hσπ (hπg ρ)

theorem causalObjective_maximizer_iff_nativelySufficient
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (J : ValidCausalPolicy A O → ℝ)
    (hmono : ∀ π σ, CausalFinitaryDominates Qs π σ → J σ ≤ J π)
    (hstrict : ∀ π σ, CausalFinitaryDominates Qs π σ →
      ¬ CausalFinitaryDominates Qs σ π → J σ < J π)
    {π : ValidCausalPolicy A O} (hπns : CausalNativelySufficient Qs π)
    (σ : ValidCausalPolicy A O) :
    (∀ ρ, J ρ ≤ J σ) ↔ CausalNativelySufficient Qs σ := by
  rw [causalNativelySufficient_iff_finitarilyGreatest Qs hQ]
  exact strictlyFinitary_maximizer_iff_greatest
    (K := causalExperimentProcess Qs hQ) indexedFiniteDeficiency_triangle
    ⟨hmono, hstrict⟩
    ((causalNativelySufficient_iff_finitarilyGreatest Qs hQ π).1 hπns) σ

end IdExp
