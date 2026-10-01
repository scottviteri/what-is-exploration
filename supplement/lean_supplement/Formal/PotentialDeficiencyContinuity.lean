import Formal.ScoreProcessMonotonicity
import Formal.InformationDeficiencyContinuity
import Formal.ConvexPotentialPolytopeAdmissibility
import Formal.FiniteDecoderAttainment
import Formal.CausalPosteriorLimit
import Formal.CausalPotentialObjective

/-!
# Every continuous posterior potential is deficiency-continuous

`InformationDeficiencyContinuity` proves that information gain respects the
finitary process order, with an explicit entropy modulus.  This module proves
the same for *every* potential that is continuous and convex on the simplex,
at the price of a nonconstructive modulus: on a finite world class the valid
experiments on a fixed finite alphabet form a compact set, the expected
posterior potential is continuous on it, hence uniformly continuous, and a
decoder attaining the deficiency turns a simulation error `r` into a
sup-norm perturbation of size at most `2r`.  Together with data processing
(`finiteBayesPotential_garble_le`) this gives

`J^Φ(F) ≤ J^Φ(E) + ω_Y(δ(E, F))`, with `ω_Y` vanishing at zero.

Through `ScoreProcessMonotonicity`, the supremum of the prefix potentials is
monotone in causal finitary dominance; since the prefix potentials increase
and converge to the terminal integral (`tendsto_causalBayesPotential`), the
actual complete potential objective `causalPotentialObjective` is monotone in
the finitary order, and a natively sufficient policy maximizes it.  This is
the monotone half of `prop:finite-world-strict-finitary` for the actual
terminal objective; the strict half (terminal strict Jensen) is not here.
-/

namespace IdExp

open Finset Set Filter Topology

/-! ## Uniform continuity of the potential on valid experiments -/

section Modulus

variable {Θ Y : Type*} [Fintype Θ] [Fintype Y]

omit [Fintype Θ] in
/-- Valid experiments on a finite alphabet are exactly the stochastic rules
from worlds to signals, hence compact. -/
theorem validExperiments_eq_stochasticRules :
    {E : Θ → Y → ℝ | IsFiniteExperiment E} = stochasticRules Θ Y := by
  ext E
  simp [IsFiniteExperiment, stochasticRules]

omit [Fintype Θ] in
theorem isCompact_validExperiments :
    IsCompact {E : Θ → Y → ℝ | IsFiniteExperiment E} := by
  rw [validExperiments_eq_stochasticRules]
  exact isCompact_stochasticRules Θ Y

/-- A bound on the potential over the simplex bounds the expected potential
of every valid experiment. -/
theorem abs_finiteBayesPotential_le (Φ : (Θ → ℝ) → ℝ) (α : Θ → ℝ) (hα : IsDist α)
    (E : Θ → Y → ℝ) (hE : IsFiniteExperiment E) (M : ℝ)
    (hM : ∀ p ∈ stdSimplex ℝ Θ, |Φ p| ≤ M) :
    |finiteBayesPotential Φ α E| ≤ M := by
  have hEnn : ∀ θ x, 0 ≤ E θ x := fun θ x => (hE θ).1 x
  have hmass := finiteBayesMass_isDist α hα E hE
  calc |finiteBayesPotential Φ α E|
      ≤ ∑ x, |finiteBayesMass α E x * Φ (finiteBayesPosterior α E x)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, finiteBayesMass α E x * M := by
        apply Finset.sum_le_sum
        intro x _
        by_cases hx : finiteBayesMass α E x = 0
        · rw [hx]; simp
        · rw [abs_mul, abs_of_nonneg (finiteBayesMass_nonneg α E hα.1 hEnn x)]
          exact mul_le_mul_of_nonneg_left
            (hM _ (finiteBayesPosterior_mem_simplex α E hα.1 hEnn x hx))
            (finiteBayesMass_nonneg α E hα.1 hEnn x)
    _ = M := by rw [← Finset.sum_mul, hmass.2, one_mul]

theorem uniformContinuousOn_finiteBayesPotential (Φ : (Θ → ℝ) → ℝ)
    (hΦ : ContinuousOn Φ (stdSimplex ℝ Θ)) (α : Θ → ℝ) (hα : ∀ θ, 0 ≤ α θ) :
    UniformContinuousOn (fun E : Θ → Y → ℝ => finiteBayesPotential Φ α E)
      {E : Θ → Y → ℝ | IsFiniteExperiment E} :=
  isCompact_validExperiments.uniformContinuousOn_of_continuous
    ((continuousOn_finiteBayesPotential Φ hΦ α hα).mono
      (fun _ hE θ y => (hE θ).1 y))

/-- The (nonconstructive) modulus: the largest change of the expected
potential between valid experiments on `Y` at sup-norm distance at most
`2r`, together with `0`. -/
noncomputable def potentialModulus (Φ : (Θ → ℝ) → ℝ) (α : Θ → ℝ) (Y : Type*) [Fintype Y]
    (r : ℝ) : ℝ :=
  sSup ({0} ∪ {d | ∃ E F : Θ → Y → ℝ, IsFiniteExperiment E ∧ IsFiniteExperiment F ∧
    dist E F ≤ 2 * r ∧ d = |finiteBayesPotential Φ α F - finiteBayesPotential Φ α E|})

theorem potentialModulus_set_bddAbove (Φ : (Θ → ℝ) → ℝ) (hΦ : ContinuousOn Φ (stdSimplex ℝ Θ))
    (α : Θ → ℝ) (hα : IsDist α) (r : ℝ) :
    BddAbove ({0} ∪ {d | ∃ E F : Θ → Y → ℝ, IsFiniteExperiment E ∧ IsFiniteExperiment F ∧
      dist E F ≤ 2 * r ∧ d = |finiteBayesPotential Φ α F - finiteBayesPotential Φ α E|}) := by
  obtain ⟨M, hM⟩ : ∃ M, ∀ p ∈ stdSimplex ℝ Θ, |Φ p| ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_stdSimplex ℝ Θ).bddAbove_image hΦ.abs
    exact ⟨M, fun p hp => hM ⟨p, hp, rfl⟩⟩
  refine ⟨max 0 (2 * M), ?_⟩
  intro d hd
  rcases hd with hd | hd
  · rw [Set.mem_singleton_iff] at hd; rw [hd]; exact le_max_left _ _
  · obtain ⟨E, F, hE, hF, -, rfl⟩ := hd
    refine le_trans ?_ (le_max_right _ _)
    have h1 := abs_finiteBayesPotential_le Φ α hα E hE M hM
    have h2 := abs_finiteBayesPotential_le Φ α hα F hF M hM
    calc |finiteBayesPotential Φ α F - finiteBayesPotential Φ α E|
        ≤ |finiteBayesPotential Φ α F| + |finiteBayesPotential Φ α E| := abs_sub _ _
      _ ≤ 2 * M := by linarith

theorem potentialModulus_nonneg (Φ : (Θ → ℝ) → ℝ) (hΦ : ContinuousOn Φ (stdSimplex ℝ Θ))
    (α : Θ → ℝ) (hα : IsDist α) (r : ℝ) : 0 ≤ potentialModulus Φ α Y r :=
  le_csSup (potentialModulus_set_bddAbove Φ hΦ α hα r) (Or.inl rfl)

/-- The modulus vanishes at zero, by uniform continuity on the compact set of
valid experiments. -/
theorem potentialModulus_vanishing (Φ : (Θ → ℝ) → ℝ) (hΦ : ContinuousOn Φ (stdSimplex ℝ Θ))
    (α : Θ → ℝ) (hα : IsDist α) :
    VanishingModulus (potentialModulus Φ α Y) := by
  intro ε hε
  obtain ⟨η, hη, hηε⟩ := Metric.uniformContinuousOn_iff.1
    (uniformContinuousOn_finiteBayesPotential (Y := Y) Φ hΦ α hα.1) ε hε
  refine ⟨η / 2, half_pos hη, fun r hr0 hr => ?_⟩
  unfold potentialModulus
  refine csSup_le ⟨0, Or.inl rfl⟩ (fun d hd => ?_)
  rcases hd with hd | hd
  · rw [Set.mem_singleton_iff] at hd; rw [hd]; exact hε.le
  · obtain ⟨E, F, hE, hF, hdist, rfl⟩ := hd
    have hlt : dist E F < η := by linarith
    have := hηε E hE F hF hlt
    rw [Real.dist_eq] at this
    rw [abs_sub_comm]
    exact this.le

end Modulus

/-! ## Deficiency continuity at a fixed valid target -/

section Continuity

variable {Θ X Y : Type*} [Fintype Θ] [Nonempty Θ] [Fintype X] [Fintype Y] [Nonempty Y]

omit [Nonempty Θ] [Nonempty Y] in
/-- A decoder whose worldwise error is at most `r` moves the experiment by at
most `2r` in the sup norm. -/
theorem dist_finiteDecisionLaw_le (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (G : X → Y → ℝ) {r : ℝ} (hr : 0 ≤ r) (herr : ∀ θ, decodeErr E F G θ ≤ r) :
    dist (finiteDecisionLaw E G) F ≤ 2 * r := by
  rw [dist_pi_le_iff (by linarith)]
  intro θ
  rw [dist_pi_le_iff (by linarith)]
  intro y
  rw [Real.dist_eq]
  have hsum : |(∑ x, E θ x * G x y) - F θ y| ≤
      ∑ y', |(∑ x, E θ x * G x y') - F θ y'| :=
    Finset.single_le_sum (f := fun y' => |(∑ x, E θ x * G x y') - F θ y'|)
      (fun y' _ => abs_nonneg _) (Finset.mem_univ y)
  have h := herr θ
  unfold decodeErr at h
  simp only [finiteDecisionLaw]
  linarith

/-- **Deficiency continuity of the expected potential.**  For a convex
continuous potential and a valid prior, simulating a valid target `F` from a
valid source `E` to directed error `δ(E, F)` bounds the potential shortfall
by the modulus of `F`'s alphabet. -/
theorem finiteBayesPotential_le_add_modulus (Φ : (Θ → ℝ) → ℝ)
    (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ)) (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α)
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (F : FiniteExperiment Θ Y) (hF : IsFiniteExperiment F) :
    finiteBayesPotential Φ α F ≤
      finiteBayesPotential Φ α E + potentialModulus Φ α Y (finiteDeficiency E F) := by
  obtain ⟨G, hG, herr⟩ := exists_decoder_eq_finiteDeficiency E F
  have hδ : 0 ≤ finiteDeficiency E F :=
    finiteDeficiency_nonneg_of_valid E F hE hF
  have hEG : IsFiniteExperiment (finiteDecisionLaw E G) := finiteDecisionLaw_valid E hE G hG
  have hdist := dist_finiteDecisionLaw_le E F G hδ herr
  have hmem : |finiteBayesPotential Φ α F - finiteBayesPotential Φ α (finiteDecisionLaw E G)| ∈
      ({0} ∪ {d | ∃ E' F' : Θ → Y → ℝ, IsFiniteExperiment E' ∧ IsFiniteExperiment F' ∧
        dist E' F' ≤ 2 * finiteDeficiency E F ∧
        d = |finiteBayesPotential Φ α F' - finiteBayesPotential Φ α E'|}) :=
    Or.inr ⟨finiteDecisionLaw E G, F, hEG, hF, hdist, rfl⟩
  have hle := le_csSup (potentialModulus_set_bddAbove Φ hΦc α hα _) hmem
  have hgarble := finiteBayesPotential_garble_le α hα E hE G hG Φ hΦ
  have habs := le_abs_self (finiteBayesPotential Φ α F -
    finiteBayesPotential Φ α (finiteDecisionLaw E G))
  unfold potentialModulus
  linarith

end Continuity

/-! ## The actual causal chain -/

section Causal

set_option linter.unusedSectionVars false

universe u

variable {A O Θ : Type u} [Fintype A] [Fintype O] [Nonempty A] [Nonempty O]
  [Fintype Θ] [Nonempty Θ]
  [DecidableEq Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ]
  [MeasurableSpace A] [MeasurableSpace O]
  [MeasurableSingletonClass A] [MeasurableSingletonClass O]

/-- The expected potential of a packaged prefix experiment. -/
noncomputable def prefixPotential (Φ : (Θ → ℝ) → ℝ) (α : Θ → ℝ)
    (x : ValidCausalPrefix A O Θ) : ℝ :=
  finiteBayesPotential Φ α x.2.1

theorem prefixPotential_deficiencyContinuousAt (Φ : (Θ → ℝ) → ℝ)
    (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ)) (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (F : ValidCausalPrefix A O Θ) :
    DeficiencyContinuousAt validCausalPrefixDeficiency (prefixPotential Φ α)
      (potentialModulus Φ α (CausalFiniteTrace A O F.1)) F := by
  intro E
  exact finiteBayesPotential_le_add_modulus Φ hΦc hΦ α hα E.2.1 E.2.2 F.2.1 F.2.2

variable (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))

/-- The supremum of the prefix potentials along a policy. -/
noncomputable def causalPrefixPotentialSup (Φ : (Θ → ℝ) → ℝ) (α : Θ → ℝ)
    (π : ValidCausalPolicy A O) : ℝ :=
  processScoreSup (validCausalPrefixChain Qs hQ) (prefixPotential Φ α) π

theorem prefixPotential_bddAbove (Φ : (Θ → ℝ) → ℝ)
    (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ)) (α : Θ → ℝ) (hα : IsDist α)
    (π : ValidCausalPolicy A O) :
    BddAbove (Set.range fun t => prefixPotential Φ α (validCausalPrefixChain Qs hQ π t)) := by
  obtain ⟨M, hM⟩ : ∃ M, ∀ p ∈ stdSimplex ℝ Θ, |Φ p| ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_stdSimplex ℝ Θ).bddAbove_image hΦc.abs
    exact ⟨M, fun p hp => hM ⟨p, hp, rfl⟩⟩
  refine ⟨M, ?_⟩
  rintro _ ⟨t, rfl⟩
  exact (le_abs_self _).trans
    (abs_finiteBayesPotential_le Φ α hα _ (causalFiniteExperiment_valid π.1 π.2 Qs hQ t) M hM)

/-- **Prefix-potential suprema are monotone in the finitary order**, for every
continuous convex potential and valid prior on a finite world class. -/
theorem causalPrefixPotentialSup_mono_of_finitaryDominates (Φ : (Θ → ℝ) → ℝ)
    (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ)) (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α)
    {π ρ : ValidCausalPolicy A O} (hdom : CausalFinitaryDominates Qs π ρ) :
    causalPrefixPotentialSup Qs hQ Φ α ρ ≤ causalPrefixPotentialSup Qs hQ Φ α π := by
  unfold causalPrefixPotentialSup processScoreSup
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨n, rfl⟩
  exact score_le_processScoreSup_of_finitaryDominates
    (validCausalPrefixChain Qs hQ) validCausalPrefixDeficiency
    validCausalPrefixDeficiency_nonneg (prefixPotential Φ α)
    (potentialModulus Φ α (CausalFiniteTrace A O n))
    (potentialModulus_vanishing Φ hΦc α hα)
    ((causalFinitaryDominates_iff_packaged Qs hQ π ρ).1 hdom)
    (prefixPotential_bddAbove Qs hQ Φ hΦc α hα π) n
    (prefixPotential_deficiencyContinuousAt Φ hΦc hΦ α hα _)

include hQ in
/-- Prefix potentials increase with the horizon: a shorter prefix is an exact
garbling of a longer one. -/
theorem prefixPotential_monotone (Φ : (Θ → ℝ) → ℝ) (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (π : ValidCausalPolicy A O) :
    Monotone fun t => finiteBayesPotential Φ α (causalFiniteExperiment π.1 Qs t) := by
  intro m n hmn
  obtain ⟨G, hG, hEq⟩ := causalFiniteExperiment_prefix_blackwell_of_le π.1 π.2 Qs hQ hmn
  have h := finiteBayesPotential_garble_le α hα (causalFiniteExperiment π.1 Qs n)
    (causalFiniteExperiment_valid π.1 π.2 Qs hQ n) G hG Φ hΦ
  rw [hEq] at h
  exact h

/-- **The terminal potential is the supremum of the prefix potentials.** -/
theorem causalTerminalPotential_eq_prefixSup (Φ : (Θ → ℝ) → ℝ)
    (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ)) (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (π : ValidCausalPolicy A O) :
    causalTerminalPotential Φ α Qs hQ π = causalPrefixPotentialSup Qs hQ Φ α π := by
  have hlim := tendsto_causalBayesPotential α hα Qs hQ π Φ hΦc
  have hsup := tendsto_atTop_ciSup (prefixPotential_monotone Qs hQ Φ hΦ α hα π)
    (prefixPotential_bddAbove Qs hQ Φ hΦc α hα π)
  exact tendsto_nhds_unique hlim hsup

/-- **Terminal potentials are monotone in the finitary order.** -/
theorem causalTerminalPotential_mono_of_finitaryDominates (Φ : (Θ → ℝ) → ℝ)
    (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ)) (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α)
    {π ρ : ValidCausalPolicy A O} (hdom : CausalFinitaryDominates Qs π ρ) :
    causalTerminalPotential Φ α Qs hQ ρ ≤ causalTerminalPotential Φ α Qs hQ π := by
  rw [causalTerminalPotential_eq_prefixSup Qs hQ Φ hΦc hΦ α hα,
    causalTerminalPotential_eq_prefixSup Qs hQ Φ hΦc hΦ α hα]
  exact causalPrefixPotentialSup_mono_of_finitaryDominates Qs hQ Φ hΦc hΦ α hα hdom

/-- **Complete potential objectives are finitarily monotone** (the monotone
half of `prop:finite-world-strict-finitary`, for the actual terminal
objective and any prior that is a distribution). -/
theorem causalPotentialObjective_mono_of_finitaryDominates (Φ : (Θ → ℝ) → ℝ)
    (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ)) (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α)
    {π ρ : ValidCausalPolicy A O} (hdom : CausalFinitaryDominates Qs π ρ) :
    causalPotentialObjective Φ α Qs hQ ρ ≤ causalPotentialObjective Φ α Qs hQ π := by
  unfold causalPotentialObjective
  have := causalTerminalPotential_mono_of_finitaryDominates Qs hQ Φ hΦc hΦ α hα hdom
  linarith

theorem causalPotentialObjective_eq_of_mutual_finitaryDominates (Φ : (Θ → ℝ) → ℝ)
    (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ)) (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α)
    {π ρ : ValidCausalPolicy A O} (h1 : CausalFinitaryDominates Qs π ρ)
    (h2 : CausalFinitaryDominates Qs ρ π) :
    causalPotentialObjective Φ α Qs hQ ρ = causalPotentialObjective Φ α Qs hQ π :=
  le_antisymm (causalPotentialObjective_mono_of_finitaryDominates Qs hQ Φ hΦc hΦ α hα h1)
    (causalPotentialObjective_mono_of_finitaryDominates Qs hQ Φ hΦc hΦ α hα h2)

/-- A natively sufficient policy maximizes every complete continuous convex
potential objective. -/
theorem causalPotentialObjective_le_of_nativelySufficient (Φ : (Θ → ℝ) → ℝ)
    (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ)) (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α)
    {π : ValidCausalPolicy A O} (hπ : CausalNativelySufficient Qs π)
    (ρ : ValidCausalPolicy A O) :
    causalPotentialObjective Φ α Qs hQ ρ ≤ causalPotentialObjective Φ α Qs hQ π :=
  causalPotentialObjective_mono_of_finitaryDominates Qs hQ Φ hΦc hΦ α hα
    (((causalNativelySufficient_iff_finitarilyGreatest Qs hQ π).1 hπ) ρ)

end Causal

end IdExp
