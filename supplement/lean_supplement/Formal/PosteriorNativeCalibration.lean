import Formal.StrictConvexStrictness
import Formal.StrictFinitaryObjective

/-!
# Uniform native calibration of complete posterior potentials

A vanishing reverse modulus supplies one objective tolerance before choosing
policies or native target horizons. The proof passes through finite experiments:
an approximate forward decoder with sufficiently little posterior-potential loss
admits an approximate reverse decoder. A persistent target error therefore forces
a uniform positive objective gap.

Every continuous strictly convex potential has the required modulus at a fixed
full-support prior. The resulting calibration needs a sufficient comparator,
but neither an attained world-label experiment nor compactness of policy space.
Acquisition times may depend on the policy and target.
-/

namespace IdExp

open Finset Set Filter Topology

universe u v

section Finite

variable {Θ : Type v} [Fintype Θ] [Nonempty Θ]

/-- A small approximate-garbling potential gap has a uniformly small reverse
error. The tolerance precedes both finite signal alphabets and experiments;
only the continuity correction depends on the acquired signal alphabet. -/
theorem exists_reverse_tolerance_of_vanishingReverseModulus
    (Φ : (Θ → ℝ) → ℝ) (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ))
    (α : Θ → ℝ) (hα : IsDist α) (a : ℝ) (ha : 0 < a) (hlow : ∀ θ, a ≤ α θ)
    (hrev : HasVanishingReverseModulus.{u, v} Φ α) (ε : ℝ) (hε : 0 < ε) :
    ∃ η > 0, ∀ {X Y : Type u} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
      (E : FiniteExperiment Θ X) (_hE : IsFiniteExperiment E)
      (F : FiniteExperiment Θ Y) (_hF : IsFiniteExperiment F),
      finiteBayesPotential Φ α F - finiteBayesPotential Φ α E +
          potentialModulus Φ α X (finiteDeficiency F E) < η →
        finiteDeficiency E F ≤ finiteDeficiency F E + ε := by
  obtain ⟨η, hη, hmod⟩ := hrev (a * ε ^ 2) (by positivity)
  refine ⟨η, hη, ?_⟩
  intro X Y _ _ _ _ E hE F hF hsmall
  set ρ := finiteDeficiency F E
  have hρ0 : 0 ≤ ρ := finiteDeficiency_nonneg_of_valid F E hF hE
  obtain ⟨G, hG, herr⟩ := exists_decoder_eq_finiteDeficiency F E
  have hFG : IsFiniteExperiment (finiteDecisionLaw F G) := finiteDecisionLaw_valid F hF G hG
  have hdist := dist_finiteDecisionLaw_le F E G hρ0 herr
  have hmem : |finiteBayesPotential Φ α E - finiteBayesPotential Φ α (finiteDecisionLaw F G)| ∈
      ({0} ∪ {d | ∃ E' F' : Θ → X → ℝ, IsFiniteExperiment E' ∧ IsFiniteExperiment F' ∧
        dist E' F' ≤ 2 * ρ ∧
        d = |finiteBayesPotential Φ α F' - finiteBayesPotential Φ α E'|}) :=
    Or.inr ⟨finiteDecisionLaw F G, E, hFG, hE, hdist, rfl⟩
  have hω : |finiteBayesPotential Φ α E - finiteBayesPotential Φ α (finiteDecisionLaw F G)| ≤
      potentialModulus Φ α X ρ := by
    unfold potentialModulus
    exact le_csSup (potentialModulus_set_bddAbove Φ hΦc α hα ρ) hmem
  have hgap : finiteBayesPotential Φ α F -
      finiteBayesPotential Φ α (finiteDecisionLaw F G) < η := by
    have := le_abs_self (finiteBayesPotential Φ α E -
      finiteBayesPotential Φ α (finiteDecisionLaw F G))
    linarith
  obtain ⟨R, hR, hsq⟩ := hmod F hF G hG hgap
  have hrow : ∀ θ, decodeErr (finiteDecisionLaw F G) F R θ ≤ ε := by
    intro θ
    have h1 := sq_le_of_weighted_sum_le α a ha hlow
      (fun θ => finiteTV (F θ) (finiteDecisionLaw (finiteDecisionLaw F G) R θ))
      _ le_rfl θ
    have h2 : (finiteTV (F θ) (finiteDecisionLaw (finiteDecisionLaw F G) R θ)) ^ 2 < ε ^ 2 := by
      calc _ ≤ _ := h1
        _ < (a * ε ^ 2) / a := div_lt_div_of_pos_right hsq ha
        _ = ε ^ 2 := by field_simp
    show finiteTV (finiteDecisionLaw (finiteDecisionLaw F G) R θ) (F θ) ≤ ε
    rw [finiteTV_symm]
    have h0 := finiteTV_nonneg (F θ) (finiteDecisionLaw (finiteDecisionLaw F G) R θ)
    by_contra hge
    have hge' := not_le.1 hge
    nlinarith
  exact finiteDeficiency_le_of_simulator_and_reverse E F hE hF G hG ρ herr R hR ε hrow

end Finite

section Causal

set_option linter.unusedSectionVars false

variable {A O Θ : Type u} [Fintype A] [Fintype O]
  [MeasurableSpace A] [MeasurableSpace O]
  [MeasurableSingletonClass A] [MeasurableSingletonClass O]
  [Nonempty A] [Nonempty O] [Fintype Θ] [Nonempty Θ]
  [DecidableEq Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ]

variable (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))

/-- Persistent failure to simulate a dominating policy's prefix forces one
positive objective gap, chosen before either policy or the missed horizon. -/
theorem exists_policy_uniform_gap_of_margin
    (Φ : (Θ → ℝ) → ℝ) (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ))
    (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (a : ℝ) (ha : 0 < a) (hlow : ∀ θ, a ≤ α θ)
    (hrev : HasVanishingReverseModulus.{u, u} Φ α) (ε : ℝ) (hε : 0 < ε) :
    ∃ κ > 0, ∀ (π σ : ValidCausalPolicy A O), CausalFinitaryDominates Qs σ π →
      ∀ n : ℕ, (∀ t, ε ≤ finiteDeficiency (causalFiniteExperiment π.1 Qs t)
        (causalFiniteExperiment σ.1 Qs n)) →
      causalPotentialObjective Φ α Qs hQ π ≤ causalPotentialObjective Φ α Qs hQ σ - κ := by
  obtain ⟨η, hη, hreverse⟩ := exists_reverse_tolerance_of_vanishingReverseModulus
    Φ hΦc α hα a ha hlow hrev (ε / 2) (by positivity)
  refine ⟨η / 2, by positivity, ?_⟩
  intro π σ hdom n hmargin
  have hv : ∀ (ρ : ValidCausalPolicy A O) m,
      IsFiniteExperiment (causalFiniteExperiment ρ.1 Qs m) :=
    fun ρ m => causalFiniteExperiment_valid ρ.1 ρ.2 Qs hQ m
  have hall : ∀ t, finiteBayesPotential Φ α (causalFiniteExperiment π.1 Qs t) ≤
      causalTerminalPotential Φ α Qs hQ σ - η / 2 := by
    intro t
    obtain ⟨r, hr, hrω⟩ := potentialModulus_vanishing (Y := CausalFiniteTrace A O t)
      Φ hΦc α hα (η / 2) (by positivity)
    obtain ⟨T, hT⟩ := hdom t (min (ε / 2) r) (lt_min (half_pos hε) hr)
    let N := max T n
    have hρ := hT N (le_max_left _ _)
    set ρ := finiteDeficiency (causalFiniteExperiment σ.1 Qs N)
      (causalFiniteExperiment π.1 Qs t)
    have hρ0 : 0 ≤ ρ := finiteDeficiency_nonneg_of_valid _ _ (hv σ N) (hv π t)
    have hρε : ρ < ε / 2 := lt_of_lt_of_le hρ (min_le_left _ _)
    have hρr : ρ < r := lt_of_lt_of_le hρ (min_le_right _ _)
    have hω : potentialModulus Φ α (CausalFiniteTrace A O t) ρ ≤ η / 2 := hrω ρ hρ0 hρr
    have hN := prefixPotential_le_causalTerminalPotential Qs hQ Φ hΦc hΦ α hα σ N
    by_contra hcon
    have hcon' := not_le.1 hcon
    have hgap : finiteBayesPotential Φ α (causalFiniteExperiment σ.1 Qs N) -
        finiteBayesPotential Φ α (causalFiniteExperiment π.1 Qs t) +
          potentialModulus Φ α (CausalFiniteTrace A O t) ρ < η := by linarith
    have hstep := hreverse (causalFiniteExperiment π.1 Qs t) (hv π t)
      (causalFiniteExperiment σ.1 Qs N) (hv σ N) hgap
    have htri := finiteDeficiency_triangle (causalFiniteExperiment π.1 Qs t)
      (causalFiniteExperiment σ.1 Qs N) (causalFiniteExperiment σ.1 Qs n)
      (hv π t) (hv σ N) (hv σ n)
    rw [finiteDeficiency_causalPrefix_eq_zero σ.1 σ.2 Qs hQ (le_max_right T n)] at htri
    have hmarg := hmargin t
    linarith
  have hterminal : causalTerminalPotential Φ α Qs hQ π ≤
      causalTerminalPotential Φ α Qs hQ σ - η / 2 := by
    rw [causalTerminalPotential_eq_prefixSup Qs hQ Φ hΦc hΦ α hα π]
    unfold causalPrefixPotentialSup processScoreSup
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨t, rfl⟩
    exact hall t
  unfold causalPotentialObjective
  linarith

/-- Near equality with a dominating policy controls every one of its fixed
prefix targets, with a tolerance uniform over policy pairs and target horizons. -/
theorem exists_dominated_record_tolerance_of_vanishingReverseModulus
    (Φ : (Θ → ℝ) → ℝ) (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ))
    (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (a : ℝ) (ha : 0 < a) (hlow : ∀ θ, a ≤ α θ)
    (hrev : HasVanishingReverseModulus.{u, u} Φ α) (ε : ℝ) (hε : 0 < ε) :
    ∃ η > 0, ∀ (π σ : ValidCausalPolicy A O), CausalFinitaryDominates Qs σ π →
      causalPotentialObjective Φ α Qs hQ σ - causalPotentialObjective Φ α Qs hQ π ≤ η →
      ∀ n : ℕ, eventualLoss Qs π (causalFiniteExperiment σ.1 Qs n) < ε := by
  obtain ⟨κ, hκ, hmargin⟩ := exists_policy_uniform_gap_of_margin Qs hQ
    Φ hΦc hΦ α hα a ha hlow hrev ε hε
  refine ⟨κ / 2, by positivity, ?_⟩
  intro π σ hdom hgap n
  by_contra hnot
  have hbound := not_lt.1 hnot
  have hbad : ∀ t, ε ≤ finiteDeficiency (causalFiniteExperiment π.1 Qs t)
      (causalFiniteExperiment σ.1 Qs n) := fun t => hbound.trans
    (eventualLoss_le Qs hQ π _ (causalFiniteExperiment_valid σ.1 σ.2 Qs hQ n) t)
  have hforced := hmargin π σ hdom n hbad
  linarith

/-- **Uniform qualitative native calibration.** The objective tolerance is
chosen before the optimizing policy, sufficient comparator, target policy, and
target horizon. The eventual acquisition time is not asserted to be uniform. -/
theorem exists_eventualLoss_tolerance_of_strictConvexOn
    (Φ : (Θ → ℝ) → ℝ) (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ))
    (hΦ : StrictConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (hfs : FullSupport α) (ε : ℝ) (hε : 0 < ε) :
    ∃ η > 0, ∀ (π σ : ValidCausalPolicy A O), CausalNativelySufficient Qs σ →
      causalPotentialObjective Φ α Qs hQ σ - causalPotentialObjective Φ α Qs hQ π ≤ η →
      ∀ (ρ : ValidCausalPolicy A O) (n : ℕ),
        eventualLoss Qs π (causalFiniteExperiment ρ.1 Qs n) < ε := by
  obtain ⟨a, ha, hlow⟩ := exists_prior_floor α hfs
  obtain ⟨η, hη, hsmall⟩ := exists_dominated_record_tolerance_of_vanishingReverseModulus
    Qs hQ Φ hΦc hΦ.convexOn α hα a ha hlow
    (strictConvexOn_hasVanishingReverseModulus Φ hΦc hΦ α hα a ha hlow)
    (ε / 3) (by positivity)
  refine ⟨η, hη, ?_⟩
  intro π σ hσ hgap ρ n
  have hgreat := (causalNativelySufficient_iff_finitarilyGreatest Qs hQ σ).1 hσ
  obtain ⟨m, hm⟩ := hgreat ρ n (ε / 3) (by positivity)
  have hπm := hsmall π σ (hgreat π) hgap m
  obtain ⟨t, ht⟩ := exists_lt_of_ciInf_lt hπm
  have htri := finiteDeficiency_triangle (causalFiniteExperiment π.1 Qs t)
    (causalFiniteExperiment σ.1 Qs m) (causalFiniteExperiment ρ.1 Qs n)
    (causalFiniteExperiment_valid π.1 π.2 Qs hQ t)
    (causalFiniteExperiment_valid σ.1 σ.2 Qs hQ m)
    (causalFiniteExperiment_valid ρ.1 ρ.2 Qs hQ n)
  have hlim := eventualLoss_le Qs hQ π _ (causalFiniteExperiment_valid ρ.1 ρ.2 Qs hQ n) t
  have hσm := hm m le_rfl
  linarith

end Causal

end IdExp
