import Formal.DecisionFiniteWitness

/-!
# Transferring every finite decision procedure through collected evidence

A stochastic decoder from acquired signals to alternative signals can be followed
by any randomized decision rule. The composed rule is valid, and its expected
unit-range payoff differs from the original rule's payoff by at most the decoder
error in every world. This is a rule-level statement before choosing a prior or
optimizing a decision rule. The world class is arbitrary.

Finite source and target alphabets also give attainment of the uniform matrix
deficiency on an arbitrary nonempty world class. One attaining decoder therefore
transfers every rule and every bounded payoff at the exact deficiency, with the
decoder chosen before the decision rule and payoff.
-/

namespace IdExp

open Finset Set

universe u

variable {Θ X Y D : Type*} [Fintype X] [Fintype Y] [Fintype D]

/-- A fixed decision procedure can be transferred through a supplied decoder.
The error bound holds separately in every world and simultaneously for every
unit-range payoff on the same finite decision set. No prior is required. -/
theorem finiteDecisionRule_payoff_abs_sub_le_decodeErr
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (G : X → Y → ℝ) (hG : G ∈ stochasticRules X Y)
    (r : Y → D → ℝ) (hr : r ∈ stochasticRules Y D)
    (θ : Θ) (u : D → ℝ) (hu : ∀ d, u d ∈ Set.Icc (0 : ℝ) 1) :
    |(∑ d, finiteDecisionLaw E (stochasticRuleComp G r) θ d * u d) -
      ∑ d, finiteDecisionLaw F r θ d * u d| ≤ decodeErr E F G θ := by
  have hcomp := stochasticRuleComp_mem_stochasticRules hG hr
  have hsource := finiteDecisionLaw_valid E hE _ hcomp θ
  have htarget := finiteDecisionLaw_valid F hF r hr θ
  have htv := decodeErr_stochasticRuleComp_le E F G r hr θ
  apply abs_sub_le_iff.2
  constructor
  · exact (expectation_sub_le_finiteTV _ _ u
      (hsource.2.trans htarget.2.symm) (fun d => (hu d).1)
      (fun d => (hu d).2)).trans htv
  · have hreverse := expectation_sub_le_finiteTV _ _ u
      (htarget.2.trans hsource.2.symm) (fun d => (hu d).1)
      (fun d => (hu d).2)
    rw [finiteTV_symm] at hreverse
    exact hreverse.trans htv

/-- Compactness of the finite decoder simplex removes the finite-world
assumption from matrix-deficiency attainment. Validity supplies uniformly
bounded errors; no topology or measurable structure on worlds is used. -/
theorem exists_decoder_eq_finiteDeficiency_arbitraryWorld
    [Nonempty Θ] [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F) :
    ∃ G ∈ stochasticRules X Y, ∀ θ, decodeErr E F G θ ≤ finiteDeficiency E F := by
  let C : Θ → Set (X → Y → ℝ) :=
    fun θ => {G | decodeErr E F G θ ≤ finiteDeficiency E F}
  have hclosed (θ : Θ) : IsClosed (C θ) :=
    isClosed_le (continuous_decodeErr E F θ) continuous_const
  have hfinite : ∀ S : Finset Θ,
      (stochasticRules X Y ∩ ⋂ θ ∈ S, C θ).Nonempty := by
    intro S
    by_cases hS : S.Nonempty
    · let _ : Nonempty {θ // θ ∈ S} := by
        obtain ⟨θ, hθ⟩ := hS
        exact ⟨⟨θ, hθ⟩⟩
      obtain ⟨G, hG, herr⟩ := exists_decoder_eq_finiteDeficiency
        (restrictFiniteExperiment S E) (restrictFiniteExperiment S F)
      refine ⟨G, hG, ?_⟩
      simp only [Set.mem_iInter]
      intro θ hθ
      exact (herr ⟨θ, hθ⟩).trans (finiteDeficiency_restrict_le E F hE hF S hS)
    · obtain ⟨G, hG⟩ := stochasticRules_nonempty_of_nonempty (X := X) (Y := Y)
      refine ⟨G, hG, ?_⟩
      rw [Finset.not_nonempty_iff_eq_empty.mp hS]
      simp
  obtain ⟨G, hG, hall⟩ := (isCompact_stochasticRules X Y).inter_iInter_nonempty
    C hclosed hfinite
  exact ⟨G, hG, fun θ => Set.mem_iInter.mp hall θ⟩

/-- One decoder, chosen without any decision problem, transfers every finite
randomized decision procedure at the exact uniform deficiency. The composed
procedure is valid; the absolute payoff bound is worldwise and covers all
unit-range payoffs. The decision alphabet, rule and payoff follow the decoder
in the quantifier order. -/
theorem exists_decoder_transferring_all_finiteDecisionRules
    [Nonempty Θ] [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F) :
    ∃ G ∈ stochasticRules X Y,
      (∀ θ, decodeErr E F G θ ≤ finiteDeficiency E F) ∧
      ∀ (D : Type u) [Fintype D] (r : Y → D → ℝ),
        r ∈ stochasticRules Y D →
        stochasticRuleComp G r ∈ stochasticRules X D ∧
        ∀ (θ : Θ) (u : D → ℝ), (∀ d, u d ∈ Set.Icc (0 : ℝ) 1) →
          |(∑ d, finiteDecisionLaw E (stochasticRuleComp G r) θ d * u d) -
            ∑ d, finiteDecisionLaw F r θ d * u d| ≤ finiteDeficiency E F := by
  obtain ⟨G, hG, herr⟩ := exists_decoder_eq_finiteDeficiency_arbitraryWorld E F hE hF
  refine ⟨G, hG, herr, ?_⟩
  intro D _ r hr
  refine ⟨stochasticRuleComp_mem_stochasticRules hG hr, ?_⟩
  intro θ u hu
  exact (finiteDecisionRule_payoff_abs_sub_le_decodeErr E F hE hF G hG r hr θ u hu).trans
    (herr θ)

end IdExp
