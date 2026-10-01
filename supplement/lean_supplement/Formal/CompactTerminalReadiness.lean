import Formal.CompactDecisionUniformity
import Formal.FinitePrefixDecoderApproximation

/-!
# Compact classes: terminal decoding implies uniform prefix simulation

The finite signal alphabets may grow with time. A measurable terminal
randomized decoder is approximated under each probability-valued decision
task. Compactness then upgrades this fixed-prior approximation to uniform
worst-world deficiency convergence. No common dominating path law or compact
family of path densities is assumed.
-/

namespace IdExp

open MeasureTheory ProbabilityTheory Filter Topology Finset Set
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

private theorem integrable_unitFunction {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsFiniteMeasure μ] (f : S → ℝ) (hf : Measurable f)
    (hb : ∀ s, f s ∈ Icc (0 : ℝ) 1) : Integrable f μ := by
  apply Integrable.of_bound (μ := μ) hf.aestronglyMeasurable 1
  filter_upwards with s
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hb s).1] using (hb s).2

private theorem dist_coordinate_unit {S : Type*} [Fintype S]
    (p : S → ℝ) (hp : IsDist p) (s : S) : p s ∈ Icc (0 : ℝ) 1 :=
  ⟨hp.1 s, (Finset.single_le_sum (fun x _ => hp.1 x) (Finset.mem_univ s)).trans_eq hp.2⟩

/-- Changing finite experiment rows changes every probability-task value by
at most their integrated coordinate error. The bound need not be sharp. -/
theorem compactDecisionValue_sub_le_integral_l1
    {Θ Y : Type*} [MeasurableSpace Θ] [TopologicalSpace Θ]
    [T2Space Θ] [BorelSpace Θ] [CompactSpace Θ] [Fintype Y] [Nonempty Y]
    (F B : FiniteExperiment Θ Y)
    (hcF : ∀ y, Continuous (fun θ => F θ y))
    (hcB : ∀ y, Continuous (fun θ => B θ y))
    (μ : CompactDecisionTask Θ Y) :
    compactDecisionValue F μ - compactDecisionValue B μ ≤
      ∑ y, ∫ z, |F z.1 y - B z.1 y| ∂(μ : Measure (CompactDecisionParameter Θ Y)) := by
  have hi (E : FiniteExperiment Θ Y) (hc : ∀ y, Continuous (fun θ => E θ y)) y d :
      Integrable (fun z : CompactDecisionParameter Θ Y => E z.1 y * (z.2 d : ℝ))
        (μ : Measure (CompactDecisionParameter Θ Y)) := by
    have h : Continuous (fun z : CompactDecisionParameter Θ Y => E z.1 y * (z.2 d : ℝ)) := by
      fun_prop
    exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have herr y : Integrable (fun z : CompactDecisionParameter Θ Y => |F z.1 y - B z.1 y|)
      (μ : Measure (CompactDecisionParameter Θ Y)) := by
    have h : Continuous (fun z : CompactDecisionParameter Θ Y => |F z.1 y - B z.1 y|) := by
      fun_prop
    exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold compactDecisionValue
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro y _
  apply sub_le_iff_le_add.2
  apply Finset.sup'_le
  intro d _
  have hdiff :
      (∫ z, F z.1 y * (z.2 d : ℝ) ∂(μ : Measure (CompactDecisionParameter Θ Y))) -
      (∫ z, B z.1 y * (z.2 d : ℝ) ∂(μ : Measure (CompactDecisionParameter Θ Y))) ≤
      ∫ z, |F z.1 y - B z.1 y| ∂(μ : Measure (CompactDecisionParameter Θ Y)) := by
    rw [← integral_sub (hi F hcF y d) (hi B hcB y d)]
    apply integral_mono ((hi F hcF y d).sub (hi B hcB y d)) (herr y)
    intro z
    dsimp only [Pi.sub_apply]
    rw [← sub_mul]
    exact (mul_le_mul_of_nonneg_right (le_abs_self _) (z.2 d).property.1).trans
      (mul_le_of_le_one_right (abs_nonneg _) (z.2 d).property.2)
  have hmax := Finset.le_sup'
    (fun d => ∫ z, B z.1 y * (z.2 d : ℝ) ∂(μ : Measure (CompactDecisionParameter Θ Y)))
    (Finset.mem_univ d)
  linarith

/-- Evaluating a rule on a finite statistic is exactly finite matrix decoding. -/
theorem integral_finiteStatistic_rule
    {Ω X Y : Type*} [MeasurableSpace Ω] [Fintype X] [Fintype Y]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (q : Ω → X) (hq : Measurable q)
    (H : X → Y → ℝ) (hH : H ∈ stochasticRules X Y) (y : Y) :
    (∫ ω, H (q ω) y ∂μ) = ∑ x, μ.real (q ⁻¹' {x}) * H x y := by
  have hi : Integrable (fun x => H x y) (μ.map q) :=
    integrable_unitFunction (μ.map q) _ (measurable_of_countable _)
      (fun x => dist_coordinate_unit _ (hH x trivial) y)
  rw [← integral_map hq.aemeasurable hi.aestronglyMeasurable, integral_fintype hi]
  apply Finset.sum_congr rfl
  intro x _
  simp only [measureReal_def, Measure.map_apply hq (measurableSet_singleton x), smul_eq_mul]

private theorem integral_measure_comp {S Ω : Type*}
    [MeasurableSpace S] [MeasurableSpace Ω]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (κ : Kernel S Ω) [IsMarkovKernel κ] (f : Ω → ℝ)
    (hi : Integrable f (κ ∘ₘ μ)) :
    (∫ ω, f ω ∂(κ ∘ₘ μ)) = ∫ s, ∫ ω, f ω ∂κ s ∂μ := by
  rw [Measure.comp_eq_comp_const_apply] at hi ⊢
  simpa using ProbabilityTheory.Kernel.integral_comp hi

/-- **Compact terminal-to-prefix theorem.** A single measurable terminal
randomized decoder for a finite target, together with continuous finite rows
on a compact world class, implies uniform finite-prefix simulation. The path
laws themselves need not vary continuously in total variation, and there is
no assumption of a common dominating measure over all worlds. -/
theorem compactDeficiency_tendsto_zero_of_terminal_decoder
    {Θ Ω Y : Type*} [MeasurableSpace Θ] [TopologicalSpace Θ]
    [T2Space Θ] [BorelSpace Θ] [CompactSpace Θ] [Nonempty Θ]
    [mΩ : MeasurableSpace Ω] [Fintype Y] [Nonempty Y]
    {Xt : ℕ → Type*} [∀ t, Fintype (Xt t)]
    [∀ t, MeasurableSpace (Xt t)] [∀ t, MeasurableSingletonClass (Xt t)]
    (E : ∀ t, FiniteExperiment Θ (Xt t)) (F : FiniteExperiment Θ Y)
    (hE : ∀ t, IsFiniteExperiment (E t)) (hF : IsFiniteExperiment F)
    (hcE : ∀ t x, Continuous (fun θ => E t θ x))
    (hcF : ∀ y, Continuous (fun θ => F θ y))
    (hchain : ∀ s t, s ≤ t → FiniteBlackwellLE (E s) (E t))
    (κ : Kernel Θ Ω) [IsMarkovKernel κ]
    (q : ∀ t, Ω → Xt t) (hq : ∀ t, Measurable (q t))
    (ℱ : Filtration ℕ mΩ)
    (hℱ : ∀ t, ℱ t = MeasurableSpace.comap (q t) inferInstance)
    (hgenerate : (⨆ t, ℱ t) = mΩ)
    (hmass : ∀ t θ x, (κ θ).real (q t ⁻¹' {x}) = E t θ x)
    (G : Ω → Y → ℝ) (hG : ∀ ω, IsDist (G ω))
    (hGm : ∀ y, Measurable (fun ω => G ω y))
    (hdec : ∀ θ y, (∫ ω, G ω y ∂κ θ) = F θ y) :
    Tendsto (fun t => finiteDeficiency (E t) F) atTop (𝓝 0) := by
  apply compactDeficiency_tendsto_zero_of_pointwise_readiness E F hE hF hcE hcF hchain
  intro μ
  let κ' : Kernel (CompactDecisionParameter Θ Y) Ω := κ.comap Prod.fst measurable_fst
  let ν : Measure Ω := κ' ∘ₘ (μ : Measure (CompactDecisionParameter Θ Y))
  have hκ' : IsMarkovKernel κ' := by dsimp [κ']; infer_instance
  let : IsMarkovKernel κ' := hκ'
  have hν : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  let : IsProbabilityMeasure ν := hν
  obtain ⟨H, hH, hlim⟩ := exists_finitePrefix_decoder_L1 ν q hq ℱ hℱ hgenerate G hG hGm
  let R : ℕ → ℝ := fun t => ∑ y, ∫ ω, |H t (q t ω) y - G ω y| ∂ν
  have hR0 t : 0 ≤ R t := Finset.sum_nonneg fun y _ => integral_nonneg fun ω => abs_nonneg _
  have hB (t : ℕ) : ∀ y, Continuous (fun θ => finiteDecisionLaw (E t) (H t) θ y) := by
    intro y
    unfold finiteDecisionLaw
    fun_prop
  have hGint (ξ : Measure Ω) [IsFiniteMeasure ξ] y : Integrable (fun ω => G ω y) ξ :=
    integrable_unitFunction ξ _ (hGm y) (fun ω => dist_coordinate_unit _ (hG ω) y)
  have hHint (ξ : Measure Ω) [IsFiniteMeasure ξ] t y :
      Integrable (fun ω => H t (q t ω) y) ξ :=
    integrable_unitFunction ξ _ ((measurable_of_countable (fun x => H t x y)).comp (hq t))
      (fun ω => dist_coordinate_unit _ (hH t (q t ω) trivial) y)
  have hBint t θ y : finiteDecisionLaw (E t) (H t) θ y =
      ∫ ω, H t (q t ω) y ∂κ θ := by
    rw [integral_finiteStatistic_rule (κ θ) (q t) (hq t) (H t) (hH t) y]
    simp only [finiteDecisionLaw, hmass]
  have hbound t :
      max (compactDecisionValue F μ - compactDecisionValue (E t) μ) 0 ≤ R t := by
    have hmono := compactDecisionValue_mono_of_finiteBlackwellLE (E t)
      (finiteDecisionLaw (E t) (H t)) (hcE t) ⟨H t, hH t, rfl⟩ μ
    have hgap := compactDecisionValue_sub_le_integral_l1 F
      (finiteDecisionLaw (E t) (H t)) hcF (hB t) μ
    have herror :
        (∑ y, ∫ z, |F z.1 y - finiteDecisionLaw (E t) (H t) z.1 y|
          ∂(μ : Measure (CompactDecisionParameter Θ Y))) ≤ R t := by
      apply Finset.sum_le_sum
      intro y _
      let e : Ω → ℝ := fun ω => |H t (q t ω) y - G ω y|
      have heint (ξ : Measure Ω) [IsFiniteMeasure ξ] : Integrable e ξ :=
        ((hHint ξ t y).sub (hGint ξ y)).abs
      have hintouter : Integrable (fun z => ∫ ω, e ω ∂κ' z)
          (μ : Measure (CompactDecisionParameter Θ Y)) := by
        have h := Measure.integrable_integral_norm_of_integrable_comp (heint ν)
        simpa only [Real.norm_eq_abs, e, abs_abs] using h
      have hrow : Integrable
          (fun z : CompactDecisionParameter Θ Y =>
            |F z.1 y - finiteDecisionLaw (E t) (H t) z.1 y|)
          (μ : Measure (CompactDecisionParameter Θ Y)) := by
        have h : Continuous (fun z : CompactDecisionParameter Θ Y =>
            |F z.1 y - finiteDecisionLaw (E t) (H t) z.1 y|) := by
          fun_prop
        exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      calc
        _ ≤ ∫ z, ∫ ω, e ω ∂κ' z ∂(μ : Measure (CompactDecisionParameter Θ Y)) := by
          apply integral_mono hrow hintouter
          intro z
          change |F z.1 y - finiteDecisionLaw (E t) (H t) z.1 y| ≤ ∫ ω, e ω ∂κ z.1
          rw [abs_sub_comm, hBint, ← hdec, ← integral_sub (hHint _ t y) (hGint _ y)]
          exact abs_integral_le_integral_abs
        _ = ∫ ω, e ω ∂ν :=
          (integral_measure_comp (μ : Measure (CompactDecisionParameter Θ Y)) κ' e (heint ν)).symm
    apply max_le _ (hR0 t)
    linarith
  exact squeeze_zero (fun _ => le_max_right _ _) hbound hlim

end IdExp
