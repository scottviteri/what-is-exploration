import Formal.CausalObjectiveOrder
import Formal.StrictConvexSpreadModulus

/-!
# Strictness of complete potential objectives for every continuous strictly convex potential

The strict half of `prop:finite-world-strict-finitary` as stated: on a finite
world class with finite nonempty alphabets and a prior positive on every
world, for every potential continuous and strictly convex on the simplex, the
complete objective `J^Φ_α` is strictly finitarily monotone, and its maximizers
are exactly the natively sufficient policies once one exists.

The input is a *vanishing reverse modulus*: for every `γ > 0` there is
`η > 0` such that any exact garbling on any finite alphabets that loses less
than `η` of the potential can be reversed with prior-weighted squared row-TV
error below `γ`.  A linear reverse bound gives one; so does every continuous
strictly convex potential at a full-support prior, through the quadratic-gap
modulus of `StrictConvexSpreadModulus` and the quadratic reverse bound.  The
causal assembly is the one of `QuantitativeStrictness` with the modulus in
place of the constant: a margin `ε` at a missed horizon, a long prefix of the
dominating policy simulating a fixed prefix of the dominated one within
`min(ε/2, r)`, and a contradiction unless the potential gap at that prefix is
at least `η/2`, uniformly in the prefix.
-/

namespace IdExp

open Finset Set

universe u v

/-! ## Vanishing reverse moduli -/

section Finite

variable {Θ : Type v} [Fintype Θ] [Nonempty Θ]

/-- A potential has a vanishing reverse modulus at `α` when a small potential
loss under any exact garbling, on any finite alphabets, allows a reversal with
small prior-weighted squared row-TV error. -/
def HasVanishingReverseModulus (Φ : (Θ → ℝ) → ℝ) (α : Θ → ℝ) : Prop :=
  ∀ γ : ℝ, 0 < γ → ∃ η : ℝ, 0 < η ∧
    ∀ {S T : Type u} [Fintype S] [Fintype T] [Nonempty S] (F : FiniteExperiment Θ S),
      IsFiniteExperiment F → ∀ (G : S → T → ℝ), G ∈ stochasticRules S T →
        finiteBayesPotential Φ α F - finiteBayesPotential Φ α (finiteDecisionLaw F G) < η →
          ∃ R ∈ stochasticRules T S,
            ∑ θ, α θ * (finiteTV (F θ) (finiteDecisionLaw (finiteDecisionLaw F G) R θ)) ^ 2 < γ

omit [Nonempty Θ] in
/-- A linear reverse bound is a vanishing reverse modulus. -/
theorem hasVanishingReverseModulus_of_reverseBound (Φ : (Θ → ℝ) → ℝ) (α : Θ → ℝ) (c : ℝ)
    (hc : 0 < c) (hrev : HasReverseBound.{u, v} Φ α c) :
    HasVanishingReverseModulus.{u, v} Φ α := by
  intro γ hγ
  refine ⟨γ / c, by positivity, ?_⟩
  intro S T _ _ _ F hF G hG hgap
  obtain ⟨R, hR, hb⟩ := hrev F hF G hG
  refine ⟨R, hR, ?_⟩
  calc ∑ θ, α θ * (finiteTV (F θ) (finiteDecisionLaw (finiteDecisionLaw F G) R θ)) ^ 2
      ≤ c * (finiteBayesPotential Φ α F - finiteBayesPotential Φ α (finiteDecisionLaw F G)) := hb
    _ < c * (γ / c) := mul_lt_mul_of_pos_left hgap hc
    _ = γ := by field_simp

omit [Nonempty Θ] in
/-- **Every continuous strictly convex potential has a vanishing reverse
modulus at a prior with a positive floor.** -/
theorem strictConvexOn_hasVanishingReverseModulus (Φ : (Θ → ℝ) → ℝ)
    (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ)) (hΦ : StrictConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (a : ℝ) (ha : 0 < a) (hlow : ∀ θ, a ≤ α θ) :
    HasVanishingReverseModulus.{u, v} Φ α := by
  intro γ hγ
  obtain ⟨η, hη, hmod⟩ := exists_quadGap_modulus.{u, v} Φ hΦc hΦ α hα (4 * a * γ) (by positivity)
  refine ⟨η, hη, ?_⟩
  intro S T _ _ _ F hF G hG hgap
  obtain ⟨R, hR, hb⟩ := quadratic_hasReverseBound.{u, v} α hα a ha hlow F hF G hG
  refine ⟨R, hR, ?_⟩
  have hq := hmod F hF G hG hgap
  calc ∑ θ, α θ * (finiteTV (F θ) (finiteDecisionLaw (finiteDecisionLaw F G) R θ)) ^ 2
      ≤ (1 / (4 * a)) * (finiteBayesPotential posteriorQuadraticPotential α F -
          finiteBayesPotential posteriorQuadraticPotential α (finiteDecisionLaw F G)) := hb
    _ < (1 / (4 * a)) * (4 * a * γ) := mul_lt_mul_of_pos_left hq (by positivity)
    _ = γ := by field_simp

end Finite

/-! ## The causal assembly with a modulus -/

section Causal

set_option linter.unusedSectionVars false

variable {A O Θ : Type u} [Fintype A] [Fintype O]
  [MeasurableSpace A] [MeasurableSpace O]
  [MeasurableSingletonClass A] [MeasurableSingletonClass O]
  [Nonempty A] [Nonempty O] [Fintype Θ] [Nonempty Θ]
  [DecidableEq Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ]

variable (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))

/-- **Uniform gap from a vanishing reverse modulus.**  Under `π ⪰ σ` and a
margin `ε` at horizon `n` against `σ`, every prefix potential of `σ` sits a
fixed `κ > 0` below the complete potential of `π`. -/
theorem exists_uniform_gap_of_margin (Φ : (Θ → ℝ) → ℝ)
    (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ)) (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (a : ℝ) (ha : 0 < a) (hlow : ∀ θ, a ≤ α θ)
    (hrev : HasVanishingReverseModulus.{u, u} Φ α)
    {π σ : ValidCausalPolicy A O} (hdom : CausalFinitaryDominates Qs π σ)
    {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hmargin : ∀ t, ε ≤ finiteDeficiency (causalFiniteExperiment σ.1 Qs t)
      (causalFiniteExperiment π.1 Qs n)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ t, finiteBayesPotential Φ α (causalFiniteExperiment σ.1 Qs t) ≤
      causalTerminalPotential Φ α Qs hQ π - κ := by
  have hv : ∀ (ρ : ValidCausalPolicy A O) m,
      IsFiniteExperiment (causalFiniteExperiment ρ.1 Qs m) :=
    fun ρ m => causalFiniteExperiment_valid ρ.1 ρ.2 Qs hQ m
  obtain ⟨η, hη, hmod⟩ := hrev (a * ε ^ 2 / 4) (by positivity)
  refine ⟨η / 2, by positivity, fun t => ?_⟩
  obtain ⟨r, hr, hrω⟩ := potentialModulus_vanishing (Y := CausalFiniteTrace A O t) Φ hΦc α hα
    (η / 2) (by positivity)
  obtain ⟨T, hT⟩ := hdom t (min (ε / 2) r) (lt_min (half_pos hε) hr)
  set N := max T n with hN
  have hρ := hT N (le_max_left _ _)
  set ρ := finiteDeficiency (causalFiniteExperiment π.1 Qs N) (causalFiniteExperiment σ.1 Qs t)
    with hρdef
  have hρ0 : 0 ≤ ρ := finiteDeficiency_nonneg_of_valid _ _ (hv π N) (hv σ t)
  have hρε : ρ < ε / 2 := lt_of_lt_of_le hρ (min_le_left _ _)
  have hρr : ρ < r := lt_of_lt_of_le hρ (min_le_right _ _)
  have hω : potentialModulus Φ α (CausalFiniteTrace A O t) ρ ≤ η / 2 := hrω ρ hρ0 hρr
  obtain ⟨G, hG, herr⟩ := exists_decoder_eq_finiteDeficiency
    (causalFiniteExperiment π.1 Qs N) (causalFiniteExperiment σ.1 Qs t)
  have hFG : IsFiniteExperiment (finiteDecisionLaw (causalFiniteExperiment π.1 Qs N) G) :=
    finiteDecisionLaw_valid _ (hv π N) G hG
  have hdist := dist_finiteDecisionLaw_le (causalFiniteExperiment π.1 Qs N)
    (causalFiniteExperiment σ.1 Qs t) G hρ0 herr
  have hmem : |finiteBayesPotential Φ α (causalFiniteExperiment σ.1 Qs t) -
      finiteBayesPotential Φ α (finiteDecisionLaw (causalFiniteExperiment π.1 Qs N) G)| ∈
      ({0} ∪ {d | ∃ E' F' : Θ → CausalFiniteTrace A O t → ℝ,
        IsFiniteExperiment E' ∧ IsFiniteExperiment F' ∧ dist E' F' ≤ 2 * ρ ∧
        d = |finiteBayesPotential Φ α F' - finiteBayesPotential Φ α E'|}) :=
    Or.inr ⟨finiteDecisionLaw (causalFiniteExperiment π.1 Qs N) G,
      causalFiniteExperiment σ.1 Qs t, hFG, hv σ t, hdist, rfl⟩
  have hmodω : |finiteBayesPotential Φ α (causalFiniteExperiment σ.1 Qs t) -
      finiteBayesPotential Φ α (finiteDecisionLaw (causalFiniteExperiment π.1 Qs N) G)| ≤
      potentialModulus Φ α (CausalFiniteTrace A O t) ρ := by
    unfold potentialModulus
    exact le_csSup (potentialModulus_set_bddAbove Φ hΦc α hα ρ) hmem
  have hN' := prefixPotential_le_causalTerminalPotential Qs hQ Φ hΦc hΦ α hα π N
  -- the margin transfers from horizon `n` to horizon `N`
  have htri := finiteDeficiency_triangle (causalFiniteExperiment σ.1 Qs t)
    (causalFiniteExperiment π.1 Qs N) (causalFiniteExperiment π.1 Qs n)
    (hv σ t) (hv π N) (hv π n)
  rw [finiteDeficiency_causalPrefix_eq_zero π.1 π.2 Qs hQ (le_max_right T n)] at htri
  have hmarg := hmargin t
  by_contra hcon
  have hcon' : causalTerminalPotential Φ α Qs hQ π - η / 2 <
      finiteBayesPotential Φ α (causalFiniteExperiment σ.1 Qs t) := not_le.1 hcon
  have hgap : finiteBayesPotential Φ α (causalFiniteExperiment π.1 Qs N) -
      finiteBayesPotential Φ α (finiteDecisionLaw (causalFiniteExperiment π.1 Qs N) G) < η := by
    have := le_abs_self (finiteBayesPotential Φ α (causalFiniteExperiment σ.1 Qs t) -
      finiteBayesPotential Φ α (finiteDecisionLaw (causalFiniteExperiment π.1 Qs N) G))
    linarith
  obtain ⟨R, hR, hsq⟩ := hmod (causalFiniteExperiment π.1 Qs N) (hv π N) G hG hgap
  have hrow : ∀ θ, decodeErr (finiteDecisionLaw (causalFiniteExperiment π.1 Qs N) G)
      (causalFiniteExperiment π.1 Qs N) R θ ≤ ε / 2 := by
    intro θ
    have h1 := sq_le_of_weighted_sum_le α a ha hlow
      (fun θ => finiteTV (causalFiniteExperiment π.1 Qs N θ)
        (finiteDecisionLaw (finiteDecisionLaw (causalFiniteExperiment π.1 Qs N) G) R θ))
      _ le_rfl θ
    have h2 : (finiteTV (causalFiniteExperiment π.1 Qs N θ)
        (finiteDecisionLaw (finiteDecisionLaw (causalFiniteExperiment π.1 Qs N) G) R θ)) ^ 2 <
        (ε / 2) ^ 2 := by
      have h3 : (a * ε ^ 2 / 4) / a = (ε / 2) ^ 2 := by field_simp; ring
      calc _ ≤ _ := h1
        _ < (a * ε ^ 2 / 4) / a := div_lt_div_of_pos_right hsq ha
        _ = (ε / 2) ^ 2 := h3
    show finiteTV (finiteDecisionLaw (finiteDecisionLaw (causalFiniteExperiment π.1 Qs N) G) R θ)
      (causalFiniteExperiment π.1 Qs N θ) ≤ ε / 2
    rw [finiteTV_symm]
    have h0 := finiteTV_nonneg (causalFiniteExperiment π.1 Qs N θ)
      (finiteDecisionLaw (finiteDecisionLaw (causalFiniteExperiment π.1 Qs N) G) R θ)
    by_contra hge
    have hge' := not_le.1 hge
    nlinarith
  have hδ := finiteDeficiency_le_of_simulator_and_reverse (causalFiniteExperiment σ.1 Qs t)
    (causalFiniteExperiment π.1 Qs N) (hv σ t) (hv π N) G hG ρ herr R hR (ε / 2) hrow
  linarith

/-- **Strictness from a vanishing reverse modulus.** -/
theorem causalPotentialObjective_lt_of_vanishingReverseModulus (Φ : (Θ → ℝ) → ℝ)
    (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ)) (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (a : ℝ) (ha : 0 < a) (hlow : ∀ θ, a ≤ α θ)
    (hrev : HasVanishingReverseModulus.{u, u} Φ α)
    {π σ : ValidCausalPolicy A O} (hdom : CausalFinitaryDominates Qs π σ)
    (hnot : ¬ CausalFinitaryDominates Qs σ π) :
    causalPotentialObjective Φ α Qs hQ σ < causalPotentialObjective Φ α Qs hQ π := by
  obtain ⟨n, ε, hε, hmargin⟩ := exists_margin_of_not_finitaryDominates Qs hQ hnot
  obtain ⟨κ, hκ, hall⟩ := exists_uniform_gap_of_margin Qs hQ Φ hΦc hΦ α hα a ha hlow hrev hdom hε
    hmargin
  have hle : causalTerminalPotential Φ α Qs hQ σ ≤ causalTerminalPotential Φ α Qs hQ π - κ := by
    rw [causalTerminalPotential_eq_prefixSup Qs hQ Φ hΦc hΦ α hα σ]
    unfold causalPrefixPotentialSup processScoreSup
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨t, rfl⟩
    exact hall t
  unfold causalPotentialObjective
  linarith

/-- **The proposition's strict half, for every continuous strictly convex
potential**: with a full-support prior, one-sided causal finitary dominance
gives a strictly larger complete objective. -/
theorem causalPotentialObjective_lt_of_strictConvexOn (Φ : (Θ → ℝ) → ℝ)
    (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ)) (hΦ : StrictConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (hfs : FullSupport α)
    {π σ : ValidCausalPolicy A O} (hdom : CausalFinitaryDominates Qs π σ)
    (hnot : ¬ CausalFinitaryDominates Qs σ π) :
    causalPotentialObjective Φ α Qs hQ σ < causalPotentialObjective Φ α Qs hQ π := by
  obtain ⟨a, ha, hlow⟩ := exists_prior_floor α hfs
  exact causalPotentialObjective_lt_of_vanishingReverseModulus Qs hQ Φ hΦc hΦ.convexOn α hα a ha
    hlow (strictConvexOn_hasVanishingReverseModulus Φ hΦc hΦ α hα a ha hlow) hdom hnot

/-- The complete objective of a continuous strictly convex potential is
strictly finitarily monotone: monotone in causal finitary dominance and
strict for one-sided dominance. -/
theorem causalPotentialObjective_strictlyFinitaryMonotone (Φ : (Θ → ℝ) → ℝ)
    (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ)) (hΦ : StrictConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (hfs : FullSupport α) :
    (∀ π σ : ValidCausalPolicy A O, CausalFinitaryDominates Qs π σ →
        causalPotentialObjective Φ α Qs hQ σ ≤ causalPotentialObjective Φ α Qs hQ π) ∧
      (∀ π σ : ValidCausalPolicy A O, CausalFinitaryDominates Qs π σ →
        ¬ CausalFinitaryDominates Qs σ π →
          causalPotentialObjective Φ α Qs hQ σ < causalPotentialObjective Φ α Qs hQ π) :=
  ⟨fun _ _ hdom => causalPotentialObjective_mono_of_finitaryDominates Qs hQ Φ hΦc hΦ.convexOn
      α hα hdom,
    fun _ _ hdom hnot => causalPotentialObjective_lt_of_strictConvexOn Qs hQ Φ hΦc hΦ α hα hfs
      hdom hnot⟩

/-- Equality of the complete objective with a natively sufficient policy
forces native sufficiency, for every continuous strictly convex potential. -/
theorem causalNativelySufficient_of_strictConvex_objective_eq (Φ : (Θ → ℝ) → ℝ)
    (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ)) (hΦ : StrictConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (hfs : FullSupport α)
    {π σ : ValidCausalPolicy A O} (hπns : CausalNativelySufficient Qs π)
    (heq : causalPotentialObjective Φ α Qs hQ σ = causalPotentialObjective Φ α Qs hQ π) :
    CausalNativelySufficient Qs σ := by
  exact causalNativelySufficient_of_strict_objective_eq Qs hQ _
    (fun _ _ hdom hnot => causalPotentialObjective_lt_of_strictConvexOn Qs hQ Φ hΦc hΦ α hα hfs hdom hnot) hπns heq

/-- **Maximizers are exactly the natively sufficient policies** once one
natively sufficient policy exists, for every continuous strictly convex
potential; neither full revelation nor a greatest process is assumed
attainable beyond that. -/
theorem causalPotentialObjective_maximizer_iff_nativelySufficient_of_strictConvexOn
    (Φ : (Θ → ℝ) → ℝ)
    (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ)) (hΦ : StrictConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (hfs : FullSupport α)
    {π : ValidCausalPolicy A O} (hπns : CausalNativelySufficient Qs π)
    (σ : ValidCausalPolicy A O) :
    (∀ ρ : ValidCausalPolicy A O,
        causalPotentialObjective Φ α Qs hQ ρ ≤ causalPotentialObjective Φ α Qs hQ σ) ↔
      CausalNativelySufficient Qs σ := by
  exact causalObjective_maximizer_iff_nativelySufficient Qs hQ _
    (fun _ _ hdom => causalPotentialObjective_mono_of_finitaryDominates Qs hQ Φ hΦc hΦ.convexOn α hα hdom)
    (fun _ _ hdom hnot => causalPotentialObjective_lt_of_strictConvexOn Qs hQ Φ hΦc hΦ α hα hfs hdom hnot) hπns σ

end Causal

end IdExp
