import Formal.CausalProcess

/-!
# Run-law surrogates are blind to unobserved native separation

**Relevance:** direct current-paper support for the family-level statement behind
`prop:bonus-classes` and Experiment 44.

The original examples compared one collected experiment with one unvisited revealing test.  This
file identifies the broader class.  For a two-world source experiment whose rows coincide, the
directed deficiency to *every* valid finite target experiment is exactly one half of the target
rows' total-variation distance.  Thus the phenomenon is not tied to a particular fair-coin gadget:
one fixed collected experiment is compatible with a continuum of target-relative deficiencies
from zero through one half.

The same identity lifts pointwise to causal native tests.  When the policy-induced experiment is
class-independent, its complete depth-`n` native audit is the maximum half-TV separation among the
depth-`n` native target experiments.  Consequently a functional of the collected experiment alone
cannot recover two settings with the same run law and different native radii; class-uniform lower
and upper bounds depending only on that run law inherit the corresponding endpoint vacuity.
-/

namespace IdExp

open Finset Set

set_option linter.unusedSectionVars false

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- An experiment is class-independent when every parameter has the same signal law. -/
def ClassIndependentFiniteExperiment {Θ Z : Type*}
    (E : FiniteExperiment Θ Z) : Prop :=
  ∀ θ θ', E θ = E θ'

/-- The decoder which ignores its input and emits the midpoint of a two-world target. -/
noncomputable def binaryMidpointDecoder
    (F : FiniteExperiment (Fin 2) Y) : X → Y → ℝ :=
  fun _ y => (F 0 y + F 1 y) / 2

theorem binaryMidpointDecoder_mem_stochasticRules
    (F : FiniteExperiment (Fin 2) Y) (hF : IsFiniteExperiment F) :
    binaryMidpointDecoder (X := X) F ∈ stochasticRules X Y := by
  intro x _
  constructor
  · intro y
    exact div_nonneg (add_nonneg ((hF 0).1 y) ((hF 1).1 y)) (by norm_num)
  · unfold binaryMidpointDecoder
    rw [← Finset.sum_div, Finset.sum_add_distrib, (hF 0).2, (hF 1).2]
    norm_num

theorem finiteDecisionLaw_binaryMidpointDecoder
    (E : FiniteExperiment (Fin 2) X) (hE : IsFiniteExperiment E)
    (F : FiniteExperiment (Fin 2) Y) :
    finiteDecisionLaw E (binaryMidpointDecoder F) =
      fun _ y => (F 0 y + F 1 y) / 2 := by
  funext θ y
  unfold finiteDecisionLaw binaryMidpointDecoder
  rw [← Finset.sum_mul, (hE θ).2, one_mul]

theorem finiteTV_midpoint_left (p q : Y → ℝ) :
    finiteTV (fun y => (p y + q y) / 2) p = finiteTV p q / 2 := by
  unfold finiteTV
  have hpoint : ∀ y, |(p y + q y) / 2 - p y| = |p y - q y| / 2 := by
    intro y
    rw [show (p y + q y) / 2 - p y = (q y - p y) / 2 by ring]
    rw [abs_div, abs_sub_comm]
    norm_num
  simp_rw [hpoint]
  rw [← Finset.sum_div]
  ring

theorem finiteTV_midpoint_right (p q : Y → ℝ) :
    finiteTV (fun y => (p y + q y) / 2) q = finiteTV p q / 2 := by
  rw [show (fun y => (p y + q y) / 2) = (fun y => (q y + p y) / 2) by
    funext y
    ring]
  rw [finiteTV_midpoint_left, finiteTV_symm]

theorem decodeErr_binaryMidpointDecoder
    (E : FiniteExperiment (Fin 2) X) (hE : IsFiniteExperiment E)
    (F : FiniteExperiment (Fin 2) Y) (θ : Fin 2) :
    decodeErr E F (binaryMidpointDecoder F) θ = finiteTV (F 0) (F 1) / 2 := by
  change finiteTV (finiteDecisionLaw E (binaryMidpointDecoder F) θ) (F θ) = _
  rw [finiteDecisionLaw_binaryMidpointDecoder E hE F]
  fin_cases θ
  · exact finiteTV_midpoint_left (F 0) (F 1)
  · exact finiteTV_midpoint_right (F 0) (F 1)

/-- **Binary class-independent deficiency formula.** If the collected signal has the same law in
both worlds, its deficiency to any valid finite target is exactly half the target pair's TV
separation.  The upper bound emits the midpoint target law; the lower bound is data processing and
the TV triangle inequality. -/
theorem finiteDeficiency_classIndependent_binary_eq_half_pairTV
    [Nonempty Y]
    (E : FiniteExperiment (Fin 2) X) (F : FiniteExperiment (Fin 2) Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (hclass : ClassIndependentFiniteExperiment E) :
    finiteDeficiency E F = finiteTV (F 0) (F 1) / 2 := by
  apply le_antisymm
  · apply finiteDeficiency_le_of_decoder E F
      (binaryMidpointDecoder F)
      (binaryMidpointDecoder_mem_stochasticRules F hF)
      (finiteTV (F 0) (F 1) / 2)
    intro θ
    exact (decodeErr_binaryMidpointDecoder E hE F θ).le
  · unfold finiteDeficiency
    apply le_csInf (finiteDeficiencyCandidates_nonempty_of_valid E F hE hF)
    rintro c ⟨G, hG, herr⟩
    have hsource : finiteTV (E 0) (E 1) = 0 := by
      rw [hclass 0 1]
      simp [finiteTV]
    have hlower := finiteTV_pairwise_decoder_lower E F G hG 0 1 c
      (herr 0) (herr 1)
    rw [hsource] at hlower
    linarith

/-! ## A continuum of exact witnesses sharing one collected experiment -/

/-- Symmetric binary target with half-separation parameter `r`.  At `r = 0` it is
class-independent; at `r = 1/2` it fully reveals the world. -/
noncomputable def symmetricBinaryTarget (r : ℝ) : FiniteExperiment (Fin 2) (Fin 2) :=
  fun θ y => if θ = y then 1 / 2 + r else 1 / 2 - r

theorem symmetricBinaryTarget_valid {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2) :
    IsFiniteExperiment (symmetricBinaryTarget r) := by
  intro θ
  constructor
  · intro y
    fin_cases θ <;> fin_cases y <;> simp [symmetricBinaryTarget] <;> linarith
  · fin_cases θ <;>
      norm_num [symmetricBinaryTarget, Fin.sum_univ_succ]

theorem finiteTV_symmetricBinaryTarget {r : ℝ} (hr0 : 0 ≤ r) :
    finiteTV (symmetricBinaryTarget r 0) (symmetricBinaryTarget r 1) = 2 * r := by
  have hr2 : 0 ≤ r + r := add_nonneg hr0 hr0
  norm_num [finiteTV, symmetricBinaryTarget, Fin.sum_univ_succ]
  rw [abs_of_nonneg hr2]
  rw [show 1 / 2 - r - (1 / 2 + r) = -(r + r) by ring]
  rw [abs_neg, abs_of_nonneg hr2]
  ring

/-- Every radius in `[0, 1/2]` is realized exactly while the collected experiment `E` is held
fixed.  This packages the original `0` versus `1/2` witness as the endpoints of a continuum. -/
theorem finiteDeficiency_symmetricBinaryTarget_eq
    (E : FiniteExperiment (Fin 2) X) (hE : IsFiniteExperiment E)
    (hclass : ClassIndependentFiniteExperiment E)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2) :
    finiteDeficiency E (symmetricBinaryTarget r) = r := by
  rw [finiteDeficiency_classIndependent_binary_eq_half_pairTV E
    (symmetricBinaryTarget r) hE (symmetricBinaryTarget_valid hr0 hr1) hclass]
  rw [finiteTV_symmetricBinaryTarget hr0]
  ring

/-- No scalar functional of the collected matrix can equal the target-relative deficiency for
the entire symmetric family: its input is fixed while the exact answer ranges over `[0, 1/2]`. -/
theorem no_runLaw_functional_recovers_symmetricBinary_family
    (E : FiniteExperiment (Fin 2) X) (hE : IsFiniteExperiment E)
    (hclass : ClassIndependentFiniteExperiment E) :
    ¬ ∃ f : FiniteExperiment (Fin 2) X → ℝ,
      ∀ r, 0 ≤ r → r ≤ 1 / 2 →
        f E = finiteDeficiency E (symmetricBinaryTarget r) := by
  rintro ⟨f, hf⟩
  have h0 := hf 0 (by norm_num) (by norm_num)
  have hhalf := hf (1 / 2) (by norm_num) (by norm_num)
  rw [finiteDeficiency_symmetricBinaryTarget_eq E hE hclass (by norm_num) (by norm_num)] at h0
  rw [finiteDeficiency_symmetricBinaryTarget_eq E hE hclass (by norm_num) (by norm_num)] at hhalf
  linarith

/-- A class-uniform lower bound depending only on the shared run law is forced to be nonpositive,
because the family contains the zero-deficiency endpoint. -/
theorem runLaw_lower_bound_le_zero_on_symmetricBinary_family
    (E : FiniteExperiment (Fin 2) X) (hE : IsFiniteExperiment E)
    (hclass : ClassIndependentFiniteExperiment E)
    (L : FiniteExperiment (Fin 2) X → ℝ)
    (hL : ∀ r, 0 ≤ r → r ≤ 1 / 2 →
      L E ≤ finiteDeficiency E (symmetricBinaryTarget r)) :
    L E ≤ 0 := by
  have h := hL 0 (by norm_num) (by norm_num)
  rw [finiteDeficiency_symmetricBinaryTarget_eq E hE hclass
    (r := 0) (by norm_num) (by norm_num)] at h
  exact h

/-- A class-uniform upper bound depending only on the shared run law must be at least `1/2`,
because the family contains the fully revealing endpoint. -/
theorem half_le_runLaw_upper_bound_on_symmetricBinary_family
    (E : FiniteExperiment (Fin 2) X) (hE : IsFiniteExperiment E)
    (hclass : ClassIndependentFiniteExperiment E)
    (U : FiniteExperiment (Fin 2) X → ℝ)
    (hU : ∀ r, 0 ≤ r → r ≤ 1 / 2 →
      finiteDeficiency E (symmetricBinaryTarget r) ≤ U E) :
    1 / 2 ≤ U E := by
  have h := hU (1 / 2) (by norm_num) (by norm_num)
  rw [finiteDeficiency_symmetricBinaryTarget_eq E hE hclass
    (r := 1 / 2) (by norm_num) (by norm_num)] at h
  exact h

/-! ## Lift to the full family of causal native tests -/

variable {A O : Type*} [Fintype A] [Fintype O]

/-- For a two-world causal class, the depth-`n` native separation radius is the maximum half-TV
distance between the worlds under a deterministic native plan. -/
noncomputable def binaryNativeRadius [Nonempty A]
    (Qs : Fin 2 → CausalResponse A O) (n : ℕ) : ℝ := by
  classical
  exact (Finset.univ : Finset (CausalPlan A O n)).sup'
    Finset.univ_nonempty
    (fun τ => finiteTV
      (causalPlanObservationExperiment n τ Qs 0)
      (causalPlanObservationExperiment n τ Qs 1) / 2)

/-- When the collected experiment is class-independent, the *entire* causal native audit equals
the class's native separation radius.  This turns an isolated counterexample mechanism into a
characterization of every two-world setting with an uninformative collected run law. -/
theorem causalNativeDeficiency_eq_binaryNativeRadius_of_classIndependent
    [Nonempty A] [Nonempty O]
    (E : FiniteExperiment (Fin 2) X) (hE : IsFiniteExperiment E)
    (hclass : ClassIndependentFiniteExperiment E)
    (Qs : Fin 2 → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (n : ℕ) :
    causalNativeDeficiency E Qs n = binaryNativeRadius Qs n := by
  classical
  unfold causalNativeDeficiency binaryNativeRadius
  apply Finset.sup'_congr Finset.univ_nonempty rfl
  intro τ _
  exact finiteDeficiency_classIndependent_binary_eq_half_pairTV E
    (causalPlanObservationExperiment n τ Qs) hE
    (causalPlanObservationExperiment_valid n τ Qs hQ) hclass

/-- If two declared causal classes have different native radii behind the same class-independent
collected experiment, no functional of that collected matrix can recover both audits. -/
theorem no_runLaw_functional_recovers_distinct_binary_native_radii
    [Nonempty A] [Nonempty O]
    (E : FiniteExperiment (Fin 2) X) (hE : IsFiniteExperiment E)
    (hclass : ClassIndependentFiniteExperiment E)
    (Qs Qs' : Fin 2 → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hQ' : ∀ θ, IsCausalResponse (Qs' θ)) (n : ℕ)
    (hradius : binaryNativeRadius Qs n ≠ binaryNativeRadius Qs' n) :
    ¬ ∃ f : FiniteExperiment (Fin 2) X → ℝ,
      f E = causalNativeDeficiency E Qs n ∧
      f E = causalNativeDeficiency E Qs' n := by
  rintro ⟨f, hf, hf'⟩
  apply hradius
  rw [← causalNativeDeficiency_eq_binaryNativeRadius_of_classIndependent
      E hE hclass Qs hQ n,
    ← causalNativeDeficiency_eq_binaryNativeRadius_of_classIndependent
      E hE hclass Qs' hQ' n,
    ← hf, ← hf']

/-- Any common run-law lower bound for two such settings is at most the smaller native radius. -/
theorem runLaw_lower_bound_le_min_binary_native_radius
    [Nonempty A] [Nonempty O]
    (E : FiniteExperiment (Fin 2) X) (hE : IsFiniteExperiment E)
    (hclass : ClassIndependentFiniteExperiment E)
    (Qs Qs' : Fin 2 → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hQ' : ∀ θ, IsCausalResponse (Qs' θ)) (n : ℕ)
    (L : FiniteExperiment (Fin 2) X → ℝ)
    (hL : L E ≤ causalNativeDeficiency E Qs n)
    (hL' : L E ≤ causalNativeDeficiency E Qs' n) :
    L E ≤ min (binaryNativeRadius Qs n) (binaryNativeRadius Qs' n) := by
  rw [← causalNativeDeficiency_eq_binaryNativeRadius_of_classIndependent
      E hE hclass Qs hQ n,
    ← causalNativeDeficiency_eq_binaryNativeRadius_of_classIndependent
      E hE hclass Qs' hQ' n]
  exact le_min hL hL'

/-- Any common run-law upper bound for two such settings is at least the larger native radius. -/
theorem max_binary_native_radius_le_runLaw_upper_bound
    [Nonempty A] [Nonempty O]
    (E : FiniteExperiment (Fin 2) X) (hE : IsFiniteExperiment E)
    (hclass : ClassIndependentFiniteExperiment E)
    (Qs Qs' : Fin 2 → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hQ' : ∀ θ, IsCausalResponse (Qs' θ)) (n : ℕ)
    (U : FiniteExperiment (Fin 2) X → ℝ)
    (hU : causalNativeDeficiency E Qs n ≤ U E)
    (hU' : causalNativeDeficiency E Qs' n ≤ U E) :
    max (binaryNativeRadius Qs n) (binaryNativeRadius Qs' n) ≤ U E := by
  rw [← causalNativeDeficiency_eq_binaryNativeRadius_of_classIndependent
      E hE hclass Qs hQ n,
    ← causalNativeDeficiency_eq_binaryNativeRadius_of_classIndependent
      E hE hclass Qs' hQ' n]
  exact max_le hU hU'

end IdExp
