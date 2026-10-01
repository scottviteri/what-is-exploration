import Formal.DeficiencyTriangle
import Formal.FinitePolicyPerturbation
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Assembling the approximate-admissibility bound

The quantitative admissibility theorem for near-optimal information bounds
the improvement offered by any feasible dominating experiment.  Its proof
has three separable parts:

1. an attained `ρ`-simulator `G` of the near-optimum `E` from a dominator `F`;
2. one prior-dependent, world-independent reverse decoder `R` whose squared
   worldwise error from `F G` back to `F` has small prior average `g`;
3. **uniformization**: a modulus `c` on prior balls of mass at least `m`
   turns that average bound into the worldwise bound `c + √(g/m)`.

This module proves (3) as a measure-theoretic lemma and assembles (1)–(3)
into `δ(E, F) ≤ ρ + c + √(g/m)` by the deficiency triangle inequality.  The
information-theoretic steps that produce (2) from an objective gap — the
coupling/Fano score-continuity bound and the reverse-decoder Pinsker bound —
enter only as hypotheses and are *not* proved here.  Nothing assumes a
greatest feasible experiment, an attained optimum, world identification, or
compactness of the world class.
-/

namespace IdExp

open MeasureTheory Set

noncomputable section

/-! ## Uniformization on prior balls -/

/-- **Uniformization.**  Let `e ≥ 0` have squared prior average at most
`g`.  Suppose every world `θ` has a measurable neighborhood `B θ` of prior
mass at least `m > 0` on which `e` drops by at most `c` below `e θ`.  Then
`e θ ≤ c + √(g / m)` at every world.  No maximizing world is needed. -/
theorem uniform_bound_of_sq_integral {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsFiniteMeasure μ]
    (e : Θ → ℝ) (he0 : ∀ θ, 0 ≤ e θ) (hint : Integrable (fun θ => (e θ) ^ 2) μ)
    (B : Θ → Set Θ) (hB : ∀ θ, MeasurableSet (B θ))
    (m : ℝ) (hm : 0 < m) (hmass : ∀ θ, m ≤ μ.real (B θ))
    (c : ℝ) (hmod : ∀ θ θ', θ' ∈ B θ → e θ - c ≤ e θ')
    (g : ℝ) (hg : ∫ θ, (e θ) ^ 2 ∂μ ≤ g) (θ : Θ) :
    e θ ≤ c + Real.sqrt (g / m) := by
  set a := max (e θ - c) 0 with ha
  have ha0 : 0 ≤ a := le_max_right _ _
  have hlow : ∀ θ' ∈ B θ, a ^ 2 ≤ (e θ') ^ 2 := by
    intro θ' hθ'
    have h1 : a ≤ e θ' := max_le (hmod θ θ' hθ') (he0 θ')
    have := mul_self_le_mul_self ha0 h1
    nlinarith
  have hball : μ.real (B θ) * a ^ 2 ≤ ∫ θ' in B θ, (e θ') ^ 2 ∂μ := by
    have hconst : IntegrableOn (fun _ : Θ => a ^ 2) (B θ) μ :=
      (integrable_const _).integrableOn
    have := setIntegral_mono_on hconst hint.integrableOn (hB θ) hlow
    rwa [setIntegral_const, smul_eq_mul] at this
  have hle : ∫ θ' in B θ, (e θ') ^ 2 ∂μ ≤ ∫ θ', (e θ') ^ 2 ∂μ :=
    setIntegral_le_integral hint (Filter.Eventually.of_forall fun θ' => sq_nonneg _)
  have hmul : m * a ^ 2 ≤ g := by
    have h := mul_le_mul_of_nonneg_right (hmass θ) (sq_nonneg a)
    linarith
  have hsq : a ^ 2 ≤ g / m := by
    rw [le_div_iff₀ hm]
    linarith
  have hsqrt : a ≤ Real.sqrt (g / m) := Real.le_sqrt_of_sq_le hsq
  have hea : e θ - c ≤ a := le_max_left _ _
  linarith

/-! ## Measurability and integrability of finite decoder errors -/

/-- Decoder error is measurable whenever every experiment likelihood is measurable. -/
theorem measurable_finiteDecodeErr {Θ X Y : Type*} [MeasurableSpace Θ]
    [Fintype X] [Fintype Y] (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : ∀ x, Measurable (fun θ => E θ x))
    (hF : ∀ y, Measurable (fun θ => F θ y)) (G : X → Y → ℝ) :
    Measurable (decodeErr E F G) := by
  unfold decodeErr
  exact measurable_const.mul (Finset.measurable_sum _ fun y _ =>
    ((Finset.measurable_sum _ fun x _ => (hE x).mul_const (G x y)).sub (hF y)).abs)

/-- Valid finite experiment rows discharge the squared-error integrability
premise of the neighborhood uniformization bound for every finite prior measure. -/
theorem integrable_sq_finiteDecodeErr {Θ X Y : Type*} [MeasurableSpace Θ]
    [Fintype X] [Fintype Y] (μ : Measure Θ) [IsFiniteMeasure μ]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (hEm : ∀ x, Measurable (fun θ => E θ x))
    (hFm : ∀ y, Measurable (fun θ => F θ y))
    (G : X → Y → ℝ) (hG : G ∈ stochasticRules X Y) :
    Integrable (fun θ => (decodeErr E F G θ) ^ 2) μ := by
  apply Integrable.of_bound ((measurable_finiteDecodeErr E F hEm hFm G).pow_const 2).aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro θ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h0 := decodeErr_nonneg E F G θ
  have h1 := decodeErr_le_one E F hE hF G hG θ
  nlinarith

/-! ## Assembly -/

variable {Θ X Y : Type*} [Fintype X] [Fintype Y] [Nonempty Θ]

/-- **Assembly of a simulator and a reverse decoder.**  If `G` simulates
`E` from `F` within `ρ` in every world, and `R` decodes the simulator's
output `F G` back to `F` within `b` in every world, then `δ(E, F) ≤ ρ + b`.
The simulator's output need not belong to any feasible family. -/
theorem finiteDeficiency_le_of_simulator_and_reverse
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (G : Y → X → ℝ) (hG : G ∈ stochasticRules Y X)
    (ρ : ℝ) (hGρ : ∀ θ, decodeErr F E G θ ≤ ρ)
    (R : X → Y → ℝ) (hR : R ∈ stochasticRules X Y)
    (b : ℝ) (hRb : ∀ θ, decodeErr (finiteDecisionLaw F G) F R θ ≤ b) :
    finiteDeficiency E F ≤ ρ + b := by
  have hFG : IsFiniteExperiment (finiteDecisionLaw F G) := finiteDecisionLaw_valid F hF G hG
  have h1 : finiteDeficiency E (finiteDecisionLaw F G) ≤ ρ := by
    apply finiteDeficiency_le_of_rowTV E _ ρ
    intro θ
    rw [finiteTV_symm]
    exact hGρ θ
  have h2 : finiteDeficiency (finiteDecisionLaw F G) F ≤ b :=
    finiteDeficiency_le_of_decoder _ F R hR b hRb
  have htri := finiteDeficiency_triangle E (finiteDecisionLaw F G) F hE hFG hF
  linarith

/-- **The assembled admissibility bound.**  With a `ρ`-simulator `G`, a
reverse decoder `R` whose squared worldwise error has prior average at
most `g`, and a uniformization modulus `c` on prior balls of mass at least
`m`, the dominator is simulated within `ρ + c + √(g/m)`.  The prior enters
only through `R`'s average error and the ball masses. -/
theorem finiteDeficiency_le_of_simulator_reverse_uniformization
    [MeasurableSpace Θ] (μ : Measure Θ) [IsFiniteMeasure μ]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (G : Y → X → ℝ) (hG : G ∈ stochasticRules Y X)
    (ρ : ℝ) (hGρ : ∀ θ, decodeErr F E G θ ≤ ρ)
    (R : X → Y → ℝ) (hR : R ∈ stochasticRules X Y)
    (hint : Integrable (fun θ => (decodeErr (finiteDecisionLaw F G) F R θ) ^ 2) μ)
    (B : Θ → Set Θ) (hB : ∀ θ, MeasurableSet (B θ))
    (m : ℝ) (hm : 0 < m) (hmass : ∀ θ, m ≤ μ.real (B θ))
    (c : ℝ) (hmod : ∀ θ θ', θ' ∈ B θ →
      decodeErr (finiteDecisionLaw F G) F R θ - c ≤ decodeErr (finiteDecisionLaw F G) F R θ')
    (g : ℝ) (hg : ∫ θ, (decodeErr (finiteDecisionLaw F G) F R θ) ^ 2 ∂μ ≤ g) :
    finiteDeficiency E F ≤ ρ + c + Real.sqrt (g / m) := by
  have hb : ∀ θ, decodeErr (finiteDecisionLaw F G) F R θ ≤ c + Real.sqrt (g / m) :=
    uniform_bound_of_sq_integral μ _ (fun θ => decodeErr_nonneg _ _ _ θ) hint B hB m hm hmass
      c hmod g hg
  have := finiteDeficiency_le_of_simulator_and_reverse E F hE hF G hG ρ hGρ R hR _ hb
  linarith

/-- The modulus hypothesis follows from a common row-TV modulus: if both the
simulator output and its decoded experiment move by at most `ω` between
worlds in the same ball, then the error moves by at most `2ω`. -/
theorem error_modulus_of_rowTV
    (F : FiniteExperiment Θ Y) (G : Y → X → ℝ) (R : X → Y → ℝ)
    (ω : ℝ) (θ θ' : Θ)
    (hFG : finiteTV (finiteDecisionLaw (finiteDecisionLaw F G) R θ)
      (finiteDecisionLaw (finiteDecisionLaw F G) R θ') ≤ ω)
    (hF : finiteTV (F θ) (F θ') ≤ ω) :
    decodeErr (finiteDecisionLaw F G) F R θ - 2 * ω ≤
      decodeErr (finiteDecisionLaw F G) F R θ' := by
  change finiteTV (finiteDecisionLaw (finiteDecisionLaw F G) R θ) (F θ) - 2 * ω ≤
    finiteTV (finiteDecisionLaw (finiteDecisionLaw F G) R θ') (F θ')
  have h1 := finiteTV_triangle (finiteDecisionLaw (finiteDecisionLaw F G) R θ)
    (finiteDecisionLaw (finiteDecisionLaw F G) R θ') (F θ)
  have h2 := finiteTV_triangle (finiteDecisionLaw (finiteDecisionLaw F G) R θ') (F θ') (F θ)
  have h3 : finiteTV (F θ') (F θ) ≤ ω := by rw [finiteTV_symm]; exact hF
  linarith

end

end IdExp
