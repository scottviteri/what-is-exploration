import Formal.CausalObjectiveOrder
import Formal.PotentialDeficiencyContinuity
import Formal.ReverseDecoderPinsker
import Formal.CausalInformationObjective
import Formal.EntropyGeometry

/-!
# Strictness of complete potential objectives from a reverse bound

The strict half of `prop:finite-world-strict-finitary`, for every policy pair,
without path space.  The input is a *reverse bound* for the potential: every
exact garbling `F ↦ FG` can be reversed by a stochastic rule whose
prior-weighted squared row-TV error is at most `c` times the potential lost by
the garbling.  The repository's Bayes reverse-channel Pinsker bound gives this
for the negative-entropy potential with `c = 1/2`, so complete information
gain is strictly finitarily monotone on every finite world class with a
full-support prior.

The assembly is finite.  If `σ` does not finitarily dominate `π`, some prefix
of `π` is missed by every prefix of `σ` by a fixed margin `ε`.  Fix a prefix
of `σ`; a long prefix of `π` simulates it within `ρ`, with `ρ` as small as
desired because the alphabet of the fixed prefix of `σ` does not move.  The
quantitative reverse bound then forces the potential of that prefix of `σ` to
sit at least `a ε² / (8c)` below the potential of the long prefix of `π`,
hence below the complete objective of `π`.  The margin does not depend on the
prefix of `σ`, so the complete objective of `σ` is strictly smaller.
-/

namespace IdExp

open Finset Set

universe u v

/-! ## Reverse bounds -/

section Finite

variable {Θ : Type v} [Fintype Θ] [Nonempty Θ]

/-- A potential has a reverse bound with constant `c` at prior `α` when every
exact garbling `F ↦ FG` admits a stochastic reverse rule `R` with
`∑_θ α_θ · TV(F_θ, (FG R)_θ)² ≤ c · (J(F) − J(FG))`. -/
def HasReverseBound (Φ : (Θ → ℝ) → ℝ) (α : Θ → ℝ) (c : ℝ) : Prop :=
  ∀ {S T : Type u} [Fintype S] [Fintype T] [Nonempty S] (F : FiniteExperiment Θ S),
    IsFiniteExperiment F → ∀ (G : S → T → ℝ), G ∈ stochasticRules S T →
      ∃ R ∈ stochasticRules T S,
        ∑ θ, α θ * (finiteTV (F θ) (finiteDecisionLaw (finiteDecisionLaw F G) R θ)) ^ 2 ≤
          c * (finiteBayesPotential Φ α F - finiteBayesPotential Φ α (finiteDecisionLaw F G))

omit [Nonempty Θ] in
theorem finiteBayesPotential_neg {X : Type*} [Fintype X] (Φ : (Θ → ℝ) → ℝ) (α : Θ → ℝ)
    (E : FiniteExperiment Θ X) :
    finiteBayesPotential (fun p => -Φ p) α E = -finiteBayesPotential Φ α E := by
  unfold finiteBayesPotential
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

omit [Nonempty Θ] in
/-- **The negative-entropy potential has reverse constant `1/2`**, by the Bayes
reverse-channel Pinsker bound. -/
theorem negEnt_hasReverseBound (α : Θ → ℝ) (hα : IsDist α) :
    HasReverseBound.{u, v} (fun p => -ent p) α (1 / 2) := by
  intro S T _ _ _ F hF G hG
  refine ⟨bayesReverseChannel α F G, bayesReverseChannel_stochastic α hα F hF G hG, ?_⟩
  have h := weighted_reverse_sq_le_information_gap α hα F hF G hG
  rw [finiteBayesPotential_neg, finiteBayesPotential_neg]
  unfold finiteBayesInformation at h
  linarith

/-- **The quantitative reversal step.**  If `F` simulates `E` within `ρ` and
the potential has a reverse bound, then `E` simulates `F` within
`ρ + √(c (J(F) − J(E) + ω_X(ρ)) / a)`, where `ω_X` is the potential's
deficiency modulus on the alphabet of `E` and `a` is a prior floor. -/
theorem finiteDeficiency_le_of_potential_gap {X Y : Type u} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y]
    (Φ : (Θ → ℝ) → ℝ) (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ))
    (α : Θ → ℝ) (hα : IsDist α) (a : ℝ) (ha : 0 < a) (hlow : ∀ θ, a ≤ α θ)
    (c : ℝ) (hc : 0 ≤ c) (hrev : HasReverseBound.{u, v} Φ α c)
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (F : FiniteExperiment Θ Y) (hF : IsFiniteExperiment F) :
    finiteDeficiency E F ≤ finiteDeficiency F E +
      Real.sqrt (c * (finiteBayesPotential Φ α F - finiteBayesPotential Φ α E +
        potentialModulus Φ α X (finiteDeficiency F E)) / a) := by
  set ρ := finiteDeficiency F E with hρ
  have hρ0 : 0 ≤ ρ := finiteDeficiency_nonneg_of_valid F E hF hE
  obtain ⟨G, hG, herr⟩ := exists_decoder_eq_finiteDeficiency F E
  have hFG : IsFiniteExperiment (finiteDecisionLaw F G) := finiteDecisionLaw_valid F hF G hG
  have hdist := dist_finiteDecisionLaw_le F E G hρ0 herr
  have hmem : |finiteBayesPotential Φ α E - finiteBayesPotential Φ α (finiteDecisionLaw F G)| ∈
      ({0} ∪ {d | ∃ E' F' : Θ → X → ℝ, IsFiniteExperiment E' ∧ IsFiniteExperiment F' ∧
        dist E' F' ≤ 2 * ρ ∧
        d = |finiteBayesPotential Φ α F' - finiteBayesPotential Φ α E'|}) :=
    Or.inr ⟨finiteDecisionLaw F G, E, hFG, hE, hdist, rfl⟩
  have hmod : |finiteBayesPotential Φ α E - finiteBayesPotential Φ α (finiteDecisionLaw F G)| ≤
      potentialModulus Φ α X ρ := by
    unfold potentialModulus
    exact le_csSup (potentialModulus_set_bddAbove Φ hΦc α hα ρ) hmem
  have hgap : finiteBayesPotential Φ α F - finiteBayesPotential Φ α (finiteDecisionLaw F G) ≤
      finiteBayesPotential Φ α F - finiteBayesPotential Φ α E + potentialModulus Φ α X ρ := by
    have := le_abs_self (finiteBayesPotential Φ α E -
      finiteBayesPotential Φ α (finiteDecisionLaw F G))
    linarith
  obtain ⟨R, hR, hsq⟩ := hrev F hF G hG
  set b := Real.sqrt (c * (finiteBayesPotential Φ α F - finiteBayesPotential Φ α E +
    potentialModulus Φ α X ρ) / a) with hb
  have hrow : ∀ θ, decodeErr (finiteDecisionLaw F G) F R θ ≤ b := by
    intro θ
    have h1 : (finiteTV (F θ) (finiteDecisionLaw (finiteDecisionLaw F G) R θ)) ^ 2 ≤
        c * (finiteBayesPotential Φ α F - finiteBayesPotential Φ α E +
          potentialModulus Φ α X ρ) / a := by
      have h0 := sq_le_of_weighted_sum_le α a ha hlow _ _ hsq θ
      refine h0.trans (div_le_div_of_nonneg_right ?_ ha.le)
      exact mul_le_mul_of_nonneg_left hgap hc
    show finiteTV (finiteDecisionLaw (finiteDecisionLaw F G) R θ) (F θ) ≤ b
    rw [finiteTV_symm, hb, ← Real.sqrt_sq (finiteTV_nonneg _ _)]
    exact Real.sqrt_le_sqrt h1
  exact finiteDeficiency_le_of_simulator_and_reverse E F hE hF G hG ρ herr R hR b hrow

end Finite

/-! ## The causal assembly -/

section Causal

set_option linter.unusedSectionVars false

variable {A O Θ : Type u} [Fintype A] [Fintype O]
  [MeasurableSpace A] [MeasurableSpace O]
  [MeasurableSingletonClass A] [MeasurableSingletonClass O]
  [Nonempty A] [Nonempty O] [Fintype Θ] [Nonempty Θ]
  [DecidableEq Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ]

variable (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))

include hQ in
/-- Failure of finitary dominance gives a fixed margin at some horizon: some
prefix of `π` is missed by every prefix of `σ` by at least `ε`. -/
theorem exists_margin_of_not_finitaryDominates {π σ : ValidCausalPolicy A O}
    (hnot : ¬ CausalFinitaryDominates Qs σ π) :
    ∃ n : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ t,
      ε ≤ finiteDeficiency (causalFiniteExperiment σ.1 Qs t) (causalFiniteExperiment π.1 Qs n) := by
  simp only [CausalFinitaryDominates, not_forall, not_exists, not_lt] at hnot
  obtain ⟨n, ε, hε, hall⟩ := hnot
  refine ⟨n, ε, hε, fun t => ?_⟩
  obtain ⟨t', htt', hle⟩ := hall t
  have hv : ∀ (ρ : ValidCausalPolicy A O) m,
      IsFiniteExperiment (causalFiniteExperiment ρ.1 Qs m) :=
    fun ρ m => causalFiniteExperiment_valid ρ.1 ρ.2 Qs hQ m
  have htri := finiteDeficiency_triangle (causalFiniteExperiment σ.1 Qs t')
    (causalFiniteExperiment σ.1 Qs t) (causalFiniteExperiment π.1 Qs n)
    (hv σ t') (hv σ t) (hv π n)
  rw [finiteDeficiency_causalPrefix_eq_zero σ.1 σ.2 Qs hQ htt'] at htri
  linarith

/-- Every prefix potential is at most the complete (terminal) potential. -/
theorem prefixPotential_le_causalTerminalPotential (Φ : (Θ → ℝ) → ℝ)
    (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ)) (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (π : ValidCausalPolicy A O) (t : ℕ) :
    finiteBayesPotential Φ α (causalFiniteExperiment π.1 Qs t) ≤
      causalTerminalPotential Φ α Qs hQ π := by
  rw [causalTerminalPotential_eq_prefixSup Qs hQ Φ hΦc hΦ α hα]
  unfold causalPrefixPotentialSup processScoreSup
  exact le_csSup (prefixPotential_bddAbove Qs hQ Φ hΦc α hα π) ⟨t, rfl⟩

/-- **Uniform gap.**  Under a reverse bound with constant `c`, a prior floor
`a`, finitary dominance `π ⪰ σ`, and a margin `ε` at horizon `n` against
`σ`, every prefix potential of `σ` sits at least `a ε² / (8 c)` below the
complete potential of `π`. -/
theorem prefixPotential_le_terminal_sub_of_margin (Φ : (Θ → ℝ) → ℝ)
    (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ)) (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (a : ℝ) (ha : 0 < a) (hlow : ∀ θ, a ≤ α θ)
    (c : ℝ) (hc : 0 < c) (hrev : HasReverseBound.{u, u} Φ α c)
    {π σ : ValidCausalPolicy A O} (hdom : CausalFinitaryDominates Qs π σ)
    {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hmargin : ∀ t, ε ≤ finiteDeficiency (causalFiniteExperiment σ.1 Qs t)
      (causalFiniteExperiment π.1 Qs n)) (t : ℕ) :
    finiteBayesPotential Φ α (causalFiniteExperiment σ.1 Qs t) ≤
      causalTerminalPotential Φ α Qs hQ π - a * ε ^ 2 / (8 * c) := by
  have hv : ∀ (ρ : ValidCausalPolicy A O) m,
      IsFiniteExperiment (causalFiniteExperiment ρ.1 Qs m) :=
    fun ρ m => causalFiniteExperiment_valid ρ.1 ρ.2 Qs hQ m
  set κ := a * ε ^ 2 / (8 * c) with hκ
  have hκpos : 0 < κ := by positivity
  obtain ⟨η, hη, hηκ⟩ := potentialModulus_vanishing (Y := CausalFiniteTrace A O t) Φ hΦc α hα κ hκpos
  obtain ⟨T, hT⟩ := hdom t (min (ε / 2) η) (lt_min (half_pos hε) hη)
  set N := max T n with hN
  have hρ := hT N (le_max_left _ _)
  set ρ := finiteDeficiency (causalFiniteExperiment π.1 Qs N) (causalFiniteExperiment σ.1 Qs t)
    with hρdef
  have hρ0 : 0 ≤ ρ := finiteDeficiency_nonneg_of_valid _ _ (hv π N) (hv σ t)
  have hρε : ρ < ε / 2 := lt_of_lt_of_le hρ (min_le_left _ _)
  have hρη : ρ < η := lt_of_lt_of_le hρ (min_le_right _ _)
  have hω : potentialModulus Φ α (CausalFiniteTrace A O t) ρ ≤ κ := hηκ ρ hρ0 hρη
  -- the quantitative reversal step with `E := K_σ t`, `F := K_π N`
  have hstep := finiteDeficiency_le_of_potential_gap Φ hΦc α hα a ha hlow c hc.le hrev
    (causalFiniteExperiment σ.1 Qs t) (hv σ t) (causalFiniteExperiment π.1 Qs N) (hv π N)
  -- the margin transfers from horizon `n` to horizon `N`
  have htri := finiteDeficiency_triangle (causalFiniteExperiment σ.1 Qs t)
    (causalFiniteExperiment π.1 Qs N) (causalFiniteExperiment π.1 Qs n)
    (hv σ t) (hv π N) (hv π n)
  rw [finiteDeficiency_causalPrefix_eq_zero π.1 π.2 Qs hQ (le_max_right T n)] at htri
  have hmarg := hmargin t
  set D := finiteBayesPotential Φ α (causalFiniteExperiment π.1 Qs N) -
    finiteBayesPotential Φ α (causalFiniteExperiment σ.1 Qs t) with hD
  set ω := potentialModulus Φ α (CausalFiniteTrace A O t) ρ with hωdef
  have hsqrt : ε / 2 ≤ Real.sqrt (c * (D + ω) / a) := by linarith
  have hsq : (ε / 2) ^ 2 ≤ c * (D + ω) / a :=
    (Real.le_sqrt' (half_pos hε)).1 hsqrt
  have hsq' : (ε / 2) ^ 2 * a ≤ c * (D + ω) := (le_div_iff₀ ha).1 hsq
  have h2κ : 2 * κ ≤ D + ω := by
    have h1 : 2 * κ = (ε / 2) ^ 2 * a / c := by
      rw [hκ]; field_simp; ring
    rw [h1, div_le_iff₀ hc]
    linarith
  have hN' := prefixPotential_le_causalTerminalPotential Qs hQ Φ hΦc hΦ α hα π N
  linarith

/-- **Strictness from a reverse bound.**  With a prior floor and a potential
continuous and convex on the simplex that has a reverse bound, one-sided
causal finitary dominance gives a strictly larger complete objective. -/
theorem causalPotentialObjective_lt_of_reverseBound (Φ : (Θ → ℝ) → ℝ)
    (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ)) (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (a : ℝ) (ha : 0 < a) (hlow : ∀ θ, a ≤ α θ)
    (c : ℝ) (hc : 0 < c) (hrev : HasReverseBound.{u, u} Φ α c)
    {π σ : ValidCausalPolicy A O} (hdom : CausalFinitaryDominates Qs π σ)
    (hnot : ¬ CausalFinitaryDominates Qs σ π) :
    causalPotentialObjective Φ α Qs hQ σ < causalPotentialObjective Φ α Qs hQ π := by
  obtain ⟨n, ε, hε, hmargin⟩ := exists_margin_of_not_finitaryDominates Qs hQ hnot
  have hκpos : 0 < a * ε ^ 2 / (8 * c) := by positivity
  have hle : causalTerminalPotential Φ α Qs hQ σ ≤
      causalTerminalPotential Φ α Qs hQ π - a * ε ^ 2 / (8 * c) := by
    rw [causalTerminalPotential_eq_prefixSup Qs hQ Φ hΦc hΦ α hα σ]
    unfold causalPrefixPotentialSup processScoreSup
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨t, rfl⟩
    exact prefixPotential_le_terminal_sub_of_margin Qs hQ Φ hΦc hΦ α hα a ha hlow c hc hrev
      hdom hε hmargin t
  unfold causalPotentialObjective
  linarith

/-- Equality of the complete objective with a natively sufficient policy
forces native sufficiency. -/
theorem causalNativelySufficient_of_reverseBound_objective_eq (Φ : (Θ → ℝ) → ℝ)
    (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ)) (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (a : ℝ) (ha : 0 < a) (hlow : ∀ θ, a ≤ α θ)
    (c : ℝ) (hc : 0 < c) (hrev : HasReverseBound.{u, u} Φ α c)
    {π σ : ValidCausalPolicy A O} (hπns : CausalNativelySufficient Qs π)
    (heq : causalPotentialObjective Φ α Qs hQ σ = causalPotentialObjective Φ α Qs hQ π) :
    CausalNativelySufficient Qs σ := by
  exact causalNativelySufficient_of_strict_objective_eq Qs hQ _
    (fun _ _ hdom hnot => causalPotentialObjective_lt_of_reverseBound Qs hQ Φ hΦc hΦ α hα a ha hlow c hc hrev hdom hnot) hπns heq

/-- **Maximizers are exactly the natively sufficient policies** once one
natively sufficient policy exists. -/
theorem causalPotentialObjective_maximizer_iff_nativelySufficient_of_reverseBound
    (Φ : (Θ → ℝ) → ℝ)
    (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ)) (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (a : ℝ) (ha : 0 < a) (hlow : ∀ θ, a ≤ α θ)
    (c : ℝ) (hc : 0 < c) (hrev : HasReverseBound.{u, u} Φ α c)
    {π : ValidCausalPolicy A O} (hπns : CausalNativelySufficient Qs π)
    (σ : ValidCausalPolicy A O) :
    (∀ ρ : ValidCausalPolicy A O,
        causalPotentialObjective Φ α Qs hQ ρ ≤ causalPotentialObjective Φ α Qs hQ σ) ↔
      CausalNativelySufficient Qs σ := by
  exact causalObjective_maximizer_iff_nativelySufficient Qs hQ _
    (fun _ _ hdom => causalPotentialObjective_mono_of_finitaryDominates Qs hQ Φ hΦc hΦ α hα hdom)
    (fun _ _ hdom hnot => causalPotentialObjective_lt_of_reverseBound Qs hQ Φ hΦc hΦ α hα a ha hlow c hc hrev hdom hnot) hπns σ

/-! ## Complete information gain -/

/-- A full-support prior on a finite class has a positive floor. -/
theorem exists_prior_floor (α : Θ → ℝ) (hfs : FullSupport α) :
    ∃ a : ℝ, 0 < a ∧ ∀ θ, a ≤ α θ := by
  obtain ⟨θ₀, -, hθ₀⟩ := Finset.exists_min_image Finset.univ α Finset.univ_nonempty
  exact ⟨α θ₀, hfs θ₀, fun θ => hθ₀ θ (Finset.mem_univ θ)⟩

/-- **Complete information gain is strictly finitarily monotone** on a finite
world class with a full-support prior: one-sided causal finitary dominance
gives strictly more complete information.  No attainability of full
revelation or of a greatest process is assumed. -/
theorem causalInformationObjective_lt_of_strict_finitaryDominates (α : Θ → ℝ) (hα : IsDist α)
    (hfs : FullSupport α) {π σ : ValidCausalPolicy A O}
    (hdom : CausalFinitaryDominates Qs π σ) (hnot : ¬ CausalFinitaryDominates Qs σ π) :
    causalInformationObjective α Qs hQ σ < causalInformationObjective α Qs hQ π := by
  obtain ⟨a, ha, hlow⟩ := exists_prior_floor α hfs
  rw [causalInformationObjective_eq_negEntropyPotential, causalInformationObjective_eq_negEntropyPotential]
  exact causalPotentialObjective_lt_of_reverseBound Qs hQ (fun p => -ent p)
    continuous_ent.neg.continuousOn strictConvexOn_neg_ent_simplex.convexOn α hα a ha hlow
    (1 / 2) (by norm_num) (negEnt_hasReverseBound α hα) hdom hnot

/-- A policy with the complete information of a natively sufficient policy is
natively sufficient. -/
theorem causalNativelySufficient_of_information_eq (α : Θ → ℝ) (hα : IsDist α)
    (hfs : FullSupport α) {π σ : ValidCausalPolicy A O} (hπns : CausalNativelySufficient Qs π)
    (heq : causalInformationObjective α Qs hQ σ = causalInformationObjective α Qs hQ π) :
    CausalNativelySufficient Qs σ := by
  obtain ⟨a, ha, hlow⟩ := exists_prior_floor α hfs
  rw [causalInformationObjective_eq_negEntropyPotential,
    causalInformationObjective_eq_negEntropyPotential] at heq
  exact causalNativelySufficient_of_reverseBound_objective_eq Qs hQ (fun p => -ent p)
    continuous_ent.neg.continuousOn strictConvexOn_neg_ent_simplex.convexOn α hα a ha hlow
    (1 / 2) (by norm_num) (negEnt_hasReverseBound α hα) hπns heq

/-- **Complete-information maximizers are exactly the natively sufficient
policies** whenever one natively sufficient policy exists; full revelation
need not be attainable. -/
theorem causalInformationObjective_maximizer_iff_nativelySufficient (α : Θ → ℝ)
    (hα : IsDist α) (hfs : FullSupport α) {π : ValidCausalPolicy A O}
    (hπns : CausalNativelySufficient Qs π) (σ : ValidCausalPolicy A O) :
    (∀ ρ : ValidCausalPolicy A O,
        causalInformationObjective α Qs hQ ρ ≤ causalInformationObjective α Qs hQ σ) ↔
      CausalNativelySufficient Qs σ := by
  obtain ⟨a, ha, hlow⟩ := exists_prior_floor α hfs
  simp_rw [causalInformationObjective_eq_negEntropyPotential]
  exact causalPotentialObjective_maximizer_iff_nativelySufficient_of_reverseBound Qs hQ
    (fun p => -ent p) continuous_ent.neg.continuousOn strictConvexOn_neg_ent_simplex.convexOn
    α hα a ha hlow (1 / 2) (by norm_num) (negEnt_hasReverseBound α hα) hπns σ

theorem causalInformationObjective_argmax_eq_nativelySufficient_of_exists (α : Θ → ℝ)
    (hα : IsDist α) (hfs : FullSupport α) {π : ValidCausalPolicy A O}
    (hπns : CausalNativelySufficient Qs π) :
    {σ | ∀ ρ, causalInformationObjective α Qs hQ ρ ≤ causalInformationObjective α Qs hQ σ} =
      {σ | CausalNativelySufficient Qs σ} := by
  ext σ
  exact causalInformationObjective_maximizer_iff_nativelySufficient Qs hQ α hα hfs hπns σ

end Causal

end IdExp
