import Formal.StrictConvexStrictness
import Formal.PotentialDeficiencyContinuity
import Formal.PosteriorGarblingStrict
import Formal.FiniteDecoderAttainment
import Formal.AbsorbingExperiment

/-!
# Strictness of complete potential objectives for finitely determined policies

The strict half of `prop:finite-world-strict-finitary` needs strict Jensen at
the terminal experiments.  For policies whose prefix at some finite time
already simulates every later prefix exactly, *finitely determined* policies,
the terminal experiment is equivalent to that prefix, and the checked
finite-signal strict Jensen (`signalPosterior_potential_lt_of_no_reverse`)
suffices.  Every policy on an absorbing interface is finitely determined,
which covers the paper's two-bit, crossing-partition, Three Doors, and gate
examples.

Results, on a finite world class with a prior positive on every world and a
potential continuous and strictly convex on the simplex:

* finitary dominance between finitely determined policies is exact Blackwell
  dominance between their determining prefixes;
* the complete objective of a finitely determined policy is the potential of
  its determining prefix;
* one-sided finitary dominance gives a strictly larger complete objective;
* if a finitely determined natively sufficient policy exists, a finitely
  determined policy maximizes the complete objective iff it is natively
  sufficient.
-/

namespace IdExp

open Finset Set

/-! ## Strict Jensen for prior-weighted experiments -/

section Finite

variable {Θ X Y : Type*} [Fintype Θ] [Nonempty Θ] [Fintype X] [Fintype Y]

/-- The prior-weighted experiment `(θ, x) ↦ α θ · E θ x`. -/
def priorWeighted (α : Θ → ℝ) (E : FiniteExperiment Θ X) : FiniteExperiment Θ X :=
  fun θ x => α θ * E θ x

omit [Fintype Θ] [Nonempty Θ] [Fintype Y] in
theorem finiteDecisionLaw_priorWeighted (α : Θ → ℝ) (E : FiniteExperiment Θ X)
    (G : X → Y → ℝ) :
    finiteDecisionLaw (priorWeighted α E) G = priorWeighted α (finiteDecisionLaw E G) := by
  funext θ y
  unfold finiteDecisionLaw priorWeighted
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

omit [Nonempty Θ] [Fintype Y] in
theorem finiteBayesMass_finiteDecisionLaw (α : Θ → ℝ) (E : FiniteExperiment Θ X)
    (G : X → Y → ℝ) (y : Y) :
    ∑ x, finiteBayesMass α E x * G x y = finiteBayesMass α (finiteDecisionLaw E G) y := by
  unfold finiteBayesMass finiteDecisionLaw
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun θ _ => Finset.sum_congr rfl fun x _ => ?_
  ring

omit [Nonempty Θ] in
/-- **Strict Jensen with a full-support prior.**  If `F` is an exact garbling
of `E` but `E` is not an exact garbling of `F`, a strictly convex potential's
expected posterior value is strictly smaller at `F`. -/
theorem finiteBayesPotential_lt_of_garble_no_reverse [Nonempty X] (α : Θ → ℝ) (hα : IsDist α)
    (hfs : FullSupport α) (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (F : FiniteExperiment Θ Y) (hF : IsFiniteExperiment F)
    (hEF : FiniteBlackwellLE F E) (hnot : ¬ FiniteBlackwellLE E F)
    (Φ : (Θ → ℝ) → ℝ) (hΦ : StrictConvexOn ℝ (stdSimplex ℝ Θ) Φ) :
    finiteBayesPotential Φ α F < finiteBayesPotential Φ α E := by
  obtain ⟨G, hG, hGF⟩ := hEF
  let P := finitePriorPosteriorSystem α hα E hE
  let Q := finitePriorPosteriorSystem α hα F hF
  have hGF' : finiteDecisionLaw (fun θ x => α θ * E θ x) G = fun θ y => α θ * F θ y := by
    have h := finiteDecisionLaw_priorWeighted α E G
    unfold priorWeighted at h
    rw [h, hGF]
  have hmass : ∀ y, ∑ x, P.mass x * G x y = Q.mass y := by
    intro y
    show ∑ x, finiteBayesMass α E x * G x y = finiteBayesMass α F y
    rw [finiteBayesMass_finiteDecisionLaw α E G y, hGF]
  have hnot' : ¬ ∃ R ∈ stochasticRules Y X,
      finiteDecisionLaw (fun θ y => α θ * F θ y) R = fun θ x => α θ * E θ x := by
    rintro ⟨R, hR, hRE⟩
    apply hnot
    refine ⟨R, hR, ?_⟩
    funext θ x
    have h := finiteDecisionLaw_priorWeighted α F R
    unfold priorWeighted at h
    rw [h] at hRE
    have hθx := congrFun (congrFun hRE θ) x
    exact mul_left_cancel₀ (ne_of_gt (hfs θ)) hθx
  rw [← finitePriorPosteriorSystem_potential α hα E hE Φ,
    ← finitePriorPosteriorSystem_potential α hα F hF Φ]
  exact signalPosterior_potential_lt_of_no_reverse P Q G hG hGF' hmass Φ (stdSimplex ℝ Θ) hΦ
    (finitePriorPosteriorSystem_density_mem α hα E hE) hnot'

end Finite

/-! ## Finitely determined policies -/

section Causal

set_option linter.unusedSectionVars false

universe u

variable {A O Θ : Type u} [Fintype A] [Fintype O]
  [MeasurableSpace A] [MeasurableSpace O]
  [MeasurableSingletonClass A] [MeasurableSingletonClass O]
  [Nonempty A] [Nonempty O] [Fintype Θ] [Nonempty Θ]
  [DecidableEq Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ]

variable (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))

/-- A policy is finitely determined at `T` when its prefix at `T` simulates every
later prefix exactly: the record stops acquiring information after `T`. -/
def CausalFinitelyDetermined (π : ValidCausalPolicy A O) (T : ℕ) : Prop :=
  ∀ t, T ≤ t →
    finiteDeficiency (causalFiniteExperiment π.1 Qs T) (causalFiniteExperiment π.1 Qs t) = 0

include hQ in
/-- A shorter prefix is an exact garbling of a longer one (zero deficiency). -/
theorem finiteDeficiency_prefix_zero (π : ValidCausalPolicy A O) {m n : ℕ} (hmn : m ≤ n) :
    finiteDeficiency (causalFiniteExperiment π.1 Qs n) (causalFiniteExperiment π.1 Qs m) = 0 :=
  finiteDeficiency_causalPrefix_eq_zero π.1 π.2 Qs hQ hmn

include hQ in
/-- A finitely determined policy's prefixes at and after `T` are all exactly
equivalent, so their potentials agree. -/
theorem finiteBayesPotential_eq_of_finitelyDetermined (Φ : (Θ → ℝ) → ℝ)
    (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ) (α : Θ → ℝ) (hα : IsDist α)
    {π : ValidCausalPolicy A O} {T : ℕ} (hπ : CausalFinitelyDetermined Qs π T)
    {t : ℕ} (ht : T ≤ t) :
    finiteBayesPotential Φ α (causalFiniteExperiment π.1 Qs t) =
      finiteBayesPotential Φ α (causalFiniteExperiment π.1 Qs T) := by
  apply le_antisymm
  · obtain ⟨G, hG, hEq⟩ := finiteBlackwellLE_of_finiteDeficiency_eq_zero _ _ (hπ t ht)
    have h := finiteBayesPotential_garble_le α hα (causalFiniteExperiment π.1 Qs T)
      (causalFiniteExperiment_valid π.1 π.2 Qs hQ T) G hG Φ hΦ
    rw [hEq] at h
    exact h
  · exact prefixPotential_monotone Qs hQ Φ hΦ α hα π ht

/-- **The complete objective of a finitely determined policy is the potential
of its determining prefix.** -/
theorem causalTerminalPotential_eq_of_finitelyDetermined (Φ : (Θ → ℝ) → ℝ)
    (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ)) (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α)
    {π : ValidCausalPolicy A O} {T : ℕ} (hπ : CausalFinitelyDetermined Qs π T) :
    causalTerminalPotential Φ α Qs hQ π =
      finiteBayesPotential Φ α (causalFiniteExperiment π.1 Qs T) := by
  rw [causalTerminalPotential_eq_prefixSup Qs hQ Φ hΦc hΦ α hα]
  unfold causalPrefixPotentialSup processScoreSup
  apply IsGreatest.csSup_eq
  refine ⟨⟨T, rfl⟩, ?_⟩
  rintro _ ⟨t, rfl⟩
  show finiteBayesPotential Φ α (causalFiniteExperiment π.1 Qs t) ≤
    finiteBayesPotential Φ α (causalFiniteExperiment π.1 Qs T)
  rcases le_or_gt t T with htT | hTt
  · exact prefixPotential_monotone Qs hQ Φ hΦ α hα π htT
  · exact le_of_eq (finiteBayesPotential_eq_of_finitelyDetermined Qs hQ Φ hΦ α hα hπ hTt.le)

include hQ in
/-- **Finitary dominance between finitely determined policies is exact
dominance between their determining prefixes.** -/
theorem causalFinitaryDominates_iff_of_finitelyDetermined
    {π σ : ValidCausalPolicy A O} {T m : ℕ}
    (hπ : CausalFinitelyDetermined Qs π T) (hσ : CausalFinitelyDetermined Qs σ m) :
    CausalFinitaryDominates Qs π σ ↔
      finiteDeficiency (causalFiniteExperiment π.1 Qs T) (causalFiniteExperiment σ.1 Qs m) = 0 := by
  have hv : ∀ (ρ : ValidCausalPolicy A O) n, IsFiniteExperiment (causalFiniteExperiment ρ.1 Qs n) :=
    fun ρ n => causalFiniteExperiment_valid ρ.1 ρ.2 Qs hQ n
  constructor
  · intro hdom
    apply le_antisymm _ (finiteDeficiency_nonneg_of_valid _ _ (hv π T) (hv σ m))
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨T₀, hT₀⟩ := hdom m ε hε
    have ht := hT₀ (max T T₀) (le_max_right _ _)
    have htri := finiteDeficiency_triangle (causalFiniteExperiment π.1 Qs T)
      (causalFiniteExperiment π.1 Qs (max T T₀)) (causalFiniteExperiment σ.1 Qs m)
      (hv π T) (hv π _) (hv σ m)
    rw [hπ _ (le_max_left _ _)] at htri
    linarith
  · intro hzero n ε hε
    refine ⟨T, fun t ht => ?_⟩
    have h1 : finiteDeficiency (causalFiniteExperiment π.1 Qs t)
        (causalFiniteExperiment π.1 Qs T) = 0 := finiteDeficiency_prefix_zero Qs hQ π ht
    have h2 : finiteDeficiency (causalFiniteExperiment σ.1 Qs m)
        (causalFiniteExperiment σ.1 Qs n) = 0 := by
      rcases le_or_gt n m with hnm | hmn
      · exact finiteDeficiency_prefix_zero Qs hQ σ hnm
      · exact hσ n hmn.le
    have htri1 := finiteDeficiency_triangle (causalFiniteExperiment π.1 Qs t)
      (causalFiniteExperiment π.1 Qs T) (causalFiniteExperiment σ.1 Qs n)
      (hv π t) (hv π T) (hv σ n)
    have htri2 := finiteDeficiency_triangle (causalFiniteExperiment π.1 Qs T)
      (causalFiniteExperiment σ.1 Qs m) (causalFiniteExperiment σ.1 Qs n)
      (hv π T) (hv σ m) (hv σ n)
    have hnn := finiteDeficiency_nonneg_of_valid _ _ (hv π t) (hv σ n)
    rw [h1] at htri1
    rw [hzero, h2] at htri2
    linarith

/-- **Strictness for finitely determined policies.**  With a full-support
prior and a strictly convex potential, one-sided finitary dominance between
finitely determined policies gives a strictly larger complete objective. -/
theorem causalPotentialObjective_lt_of_finitelyDetermined (Φ : (Θ → ℝ) → ℝ)
    (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ)) (hΦ : StrictConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (hfs : FullSupport α)
    {π σ : ValidCausalPolicy A O} {T m : ℕ}
    (hπ : CausalFinitelyDetermined Qs π T) (hσ : CausalFinitelyDetermined Qs σ m)
    (hdom : CausalFinitaryDominates Qs π σ) (hnot : ¬ CausalFinitaryDominates Qs σ π) :
    causalPotentialObjective Φ α Qs hQ σ < causalPotentialObjective Φ α Qs hQ π := by
  exact causalPotentialObjective_lt_of_strictConvexOn Qs hQ Φ hΦc hΦ α hα hfs hdom hnot

/-- Equality of the complete objective with a natively sufficient finitely
determined policy forces native sufficiency. -/
theorem causalNativelySufficient_of_finitelyDetermined_objective_eq (Φ : (Θ → ℝ) → ℝ)
    (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ)) (hΦ : StrictConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (hfs : FullSupport α)
    {π σ : ValidCausalPolicy A O} {T m : ℕ}
    (hπ : CausalFinitelyDetermined Qs π T) (hσ : CausalFinitelyDetermined Qs σ m)
    (hπns : CausalNativelySufficient Qs π)
    (heq : causalPotentialObjective Φ α Qs hQ σ = causalPotentialObjective Φ α Qs hQ π) :
    CausalNativelySufficient Qs σ := by
  exact causalNativelySufficient_of_strictConvex_objective_eq Qs hQ Φ hΦc hΦ α hα hfs hπns heq

/-- **Maximizers among finitely determined policies are exactly the natively
sufficient ones**, when a finitely determined natively sufficient policy exists. -/
theorem finitelyDetermined_maximizer_iff_nativelySufficient (Φ : (Θ → ℝ) → ℝ)
    (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ)) (hΦ : StrictConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (hfs : FullSupport α)
    {π : ValidCausalPolicy A O} {T : ℕ} (hπ : CausalFinitelyDetermined Qs π T)
    (hπns : CausalNativelySufficient Qs π)
    {σ : ValidCausalPolicy A O} {m : ℕ} (hσ : CausalFinitelyDetermined Qs σ m) :
    (∀ ρ : ValidCausalPolicy A O,
        causalPotentialObjective Φ α Qs hQ ρ ≤ causalPotentialObjective Φ α Qs hQ σ) ↔
      CausalNativelySufficient Qs σ := by
  exact causalPotentialObjective_maximizer_iff_nativelySufficient_of_strictConvexOn
    Qs hQ Φ hΦc hΦ α hα hfs hπns σ

/-! ## Absorbing interfaces: every policy is finitely determined -/

variable [DecidableEq A] [DecidableEq O]

/-- On an absorbing interface (one informative root step, then a silent
symbol), every valid policy is finitely determined at time `1`: the root
record already simulates every longer prefix exactly. -/
theorem absorbing_finitelyDetermined (o0 : O) (R : A → FiniteExperiment Θ O)
    (hR : ∀ a, IsFiniteExperiment (R a)) (π : ValidCausalPolicy A O) :
    CausalFinitelyDetermined (absorbingResponse o0 R) π 1 := by
  intro t ht
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  apply finiteDeficiency_eq_zero_of_finiteBlackwellLE
  exact finiteBlackwellLE_trans
    (absorbingCausalExperiment_root_blackwell_equiv o0 R hR π.1 π.2 n).1
    (absorbingCausalExperiment_root_blackwell_equiv o0 R hR π.1 π.2 0).2

/-- **Strictness on absorbing interfaces**: with a full-support prior and a
strictly convex potential, one-sided finitary dominance on an absorbing
interface gives a strictly larger complete objective. -/
theorem absorbing_causalPotentialObjective_lt (o0 : O) (R : A → FiniteExperiment Θ O)
    (hR : ∀ a, IsFiniteExperiment (R a)) (Φ : (Θ → ℝ) → ℝ)
    (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ)) (hΦ : StrictConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (hfs : FullSupport α) {π σ : ValidCausalPolicy A O}
    (hdom : CausalFinitaryDominates (absorbingResponse o0 R) π σ)
    (hnot : ¬ CausalFinitaryDominates (absorbingResponse o0 R) σ π) :
    causalPotentialObjective Φ α (absorbingResponse o0 R) (absorbingResponse_valid o0 R hR) σ <
      causalPotentialObjective Φ α (absorbingResponse o0 R) (absorbingResponse_valid o0 R hR) π :=
  causalPotentialObjective_lt_of_finitelyDetermined _ _ Φ hΦc hΦ α hα hfs
    (absorbing_finitelyDetermined o0 R hR π) (absorbing_finitelyDetermined o0 R hR σ) hdom hnot

end Causal

end IdExp
