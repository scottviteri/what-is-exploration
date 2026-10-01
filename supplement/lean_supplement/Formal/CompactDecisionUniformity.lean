import Formal.CausalProcess
import Formal.DecisionFiniteWitness
import Mathlib.Topology.UniformSpace.Dini
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Compact parameter classes: the decision-adversary uniformity step

A task is a probability measure on worlds paired with bounded utility rows.
This is a compact space when the world space is compact. Finite-support
quantitative Blackwell duality embeds into these tasks, without a finiteness
assumption on the world class. Dini then upgrades decreasing pointwise
positive regret to actual uniform finite-signal deficiency convergence.

This module does not assume uniform convergence as a premise. The companion
CompactTerminalReadiness discharges pointwise readiness from an actual terminal
decoder and generating filtration; CompactCausalIdentification supplies the
canonical causal application. Blackwell refinement discharges monotonicity here.
-/

namespace IdExp

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Finset Set Filter Topology
open scoped ENNReal

variable {Θ X Y : Type*} [MeasurableSpace Θ] [TopologicalSpace Θ]
  [T2Space Θ] [BorelSpace Θ] [CompactSpace Θ]
  [Fintype X] [Fintype Y] [Nonempty Y]

/-- A bounded utility row is part of the parameter for the decision game. -/
abbrev CompactDecisionParameter (Θ Y : Type*) := Θ × (Y → unitInterval)

/-- General probability-valued decision tasks, including finite-support tasks. -/
abbrev CompactDecisionTask (Θ Y : Type*) [MeasurableSpace Θ] [Fintype Y] :=
  ProbabilityMeasure (CompactDecisionParameter Θ Y)

/-- Signalwise optimized value; the decision alphabet is the target alphabet. -/
noncomputable def compactDecisionValue (E : FiniteExperiment Θ X)
    (μ : CompactDecisionTask Θ Y) : ℝ :=
  ∑ x, Finset.univ.sup' Finset.univ_nonempty
    (fun y => ∫ z, E z.1 x * (z.2 y : ℝ) ∂(μ : Measure (CompactDecisionParameter Θ Y)))

/-- Only continuity of finite row coordinates is needed for continuity on
the compact space of adversaries. No total-variation continuity of path laws. -/
theorem continuous_compactDecisionValue (E : FiniteExperiment Θ X)
    (hc : ∀ x, Continuous (fun θ => E θ x)) :
    Continuous (compactDecisionValue E : CompactDecisionTask Θ Y → ℝ) := by
  unfold compactDecisionValue
  apply continuous_finsetSum
  intro x _
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro y _
  let f : C(CompactDecisionParameter Θ Y, ℝ) :=
    ⟨fun z => E z.1 x * (z.2 y : ℝ), by fun_prop⟩
  exact ProbabilityMeasure.continuous_integral_continuousMap f

/-- A finite-support prior and utility array define a probability task by
putting the utility row into the atom along with its world. -/
noncomputable def compactDecisionFiniteTask {I : Type*} [Fintype I]
    (j : I → Θ) (α : I → ℝ) (hα : IsDist α) (u : I → Y → ℝ)
    (hu : ∀ i y, u i y ∈ Icc (0 : ℝ) 1) : CompactDecisionTask Θ Y :=
  ⟨∑ i, ENNReal.ofReal (α i) • Measure.dirac (j i, fun y => (⟨u i y, hu i y⟩ : unitInterval)), by
    constructor
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
      measure_univ, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hα.1 i), hα.2, ENNReal.ofReal_one]⟩

/-- The embedded probability-valued task has exactly the finite matrix
Bayes value. It is not merely a bound or an approximation. -/
theorem compactDecisionValue_finiteTask {I : Type*} [Fintype I]
    (E : FiniteExperiment Θ X) (j : I → Θ) (α : I → ℝ) (hα : IsDist α)
    (u : I → Y → ℝ) (hu : ∀ i y, u i y ∈ Icc (0 : ℝ) 1) :
    compactDecisionValue E (compactDecisionFiniteTask j α hα u hu) =
      finiteBayesValue (fun i => E (j i)) α u := by
  unfold compactDecisionValue finiteBayesValue finiteDecisionScore
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  funext y
  change (∫ z, E z.1 x * (z.2 y : ℝ) ∂(∑ i, ENNReal.ofReal (α i) •
    Measure.dirac (j i, fun y => (⟨u i y, hu i y⟩ : unitInterval)))) = _
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hα.1 _),
      smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · intro i _
    exact (integrable_dirac (by finiteness)).smul_measure (by simp)

/-- Uniformly bounding the probability-valued task gaps bounds actual
worst-world deficiency, using finite-support witnesses of any failure. -/
theorem finiteDeficiency_le_of_compactDecision_gaps [Nonempty Θ]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F) (c : ℝ)
    (hgap : ∀ μ : CompactDecisionTask Θ Y,
      compactDecisionValue F μ - compactDecisionValue E μ ≤ c) :
    finiteDeficiency E F ≤ c := by
  classical
  by_contra h
  obtain ⟨S, hS, α, u, hα, hu, hfail⟩ :=
    exists_finiteSupport_bayesGap_gt_of_lt_finiteDeficiency E F hE hF (lt_of_not_ge h)
  have htask := hgap (compactDecisionFiniteTask (fun θ : {θ // θ ∈ S} => θ.1) α hα u hu)
  rw [compactDecisionValue_finiteTask, compactDecisionValue_finiteTask] at htask
  exact (not_lt_of_ge htask) hfail

/-- Blackwell garbling can only reduce the value of a probability-valued
task. Integrability follows from finite-coordinate continuity on the compact
world space, rather than being supplied as an independent hypothesis. -/
theorem compactDecisionValue_mono_of_finiteBlackwellLE
    {Z : Type*} [Fintype Z] (E : FiniteExperiment Θ X) (B : FiniteExperiment Θ Z)
    (hc : ∀ x, Continuous (fun θ => E θ x))
    (hBE : FiniteBlackwellLE B E) (μ : CompactDecisionTask Θ Y) :
    compactDecisionValue B μ ≤ compactDecisionValue E μ := by
  obtain ⟨G, hG, hdec⟩ := hBE
  let S : X → Y → ℝ := fun x y => ∫ z, E z.1 x * (z.2 y : ℝ) ∂(μ : Measure (CompactDecisionParameter Θ Y))
  have hint x y : Integrable (fun z : CompactDecisionParameter Θ Y =>
      E z.1 x * (z.2 y : ℝ)) (μ : Measure (CompactDecisionParameter Θ Y)) := by
    have hc' : Continuous (fun z : CompactDecisionParameter Θ Y => E z.1 x * (z.2 y : ℝ)) := by
      fun_prop
    exact hc'.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hscore (b : Z) (y : Y) :
      (∫ z, B z.1 b * (z.2 y : ℝ) ∂(μ : Measure (CompactDecisionParameter Θ Y))) = ∑ x, G x b * S x y := by
    have hfun : (fun z : CompactDecisionParameter Θ Y => B z.1 b * (z.2 y : ℝ)) =
        fun z => ∑ x, G x b * (E z.1 x * (z.2 y : ℝ)) := by
      funext z
      rw [← hdec]
      simp only [finiteDecisionLaw, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hfun, integral_finsetSum]
    · simp only [integral_const_mul, S]
    · intro x _
      exact (hint x y).const_mul _
  unfold compactDecisionValue
  simp_rw [hscore]
  calc
    _ ≤ ∑ b, ∑ x, G x b * Finset.univ.sup' Finset.univ_nonempty (S x) := by
      apply Finset.sum_le_sum
      intro b _
      apply Finset.sup'_le
      intro y _
      exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
        (Finset.le_sup' (S x) (Finset.mem_univ y)) ((hG x trivial).1 b)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.sum_mul, (hG x trivial).2, one_mul]

/-- **Compact-class pointwise-to-uniform deficiency.** The source signal
spaces may grow with time. The world class can be uncountable. -/
theorem compactDecisionDeficiency_tendsto_zero [Nonempty Θ]
    {Xt : ℕ → Type*} [∀ t, Fintype (Xt t)]
    (E : ∀ t, FiniteExperiment Θ (Xt t)) (F : FiniteExperiment Θ Y)
    (hE : ∀ t, IsFiniteExperiment (E t)) (hF : IsFiniteExperiment F)
    (hcE : ∀ t x, Continuous (fun θ => E t θ x))
    (hcF : ∀ y, Continuous (fun θ => F θ y))
    (hmono : ∀ μ : CompactDecisionTask Θ Y, Monotone (fun t => compactDecisionValue (E t) μ))
    (hready : ∀ μ : CompactDecisionTask Θ Y,
      Tendsto (fun t => max (compactDecisionValue F μ - compactDecisionValue (E t) μ) 0)
        atTop (𝓝 0)) :
    Tendsto (fun t => finiteDeficiency (E t) F) atTop (𝓝 0) := by
  let R : ℕ → CompactDecisionTask Θ Y → ℝ := fun t μ =>
    max (compactDecisionValue F μ - compactDecisionValue (E t) μ) 0
  have hcont t : Continuous (R t) :=
    ((continuous_compactDecisionValue F hcF).sub (continuous_compactDecisionValue (E t) (hcE t))).max
      continuous_const
  have hanti : ∀ μ ∈ (Set.univ : Set (CompactDecisionTask Θ Y)), Antitone (fun t => R t μ) := by
    intro μ _ s t hst
    exact max_le_max (sub_le_sub_left (hmono μ hst) _) le_rfl
  have hunif : TendstoUniformlyOn R (fun _ => 0) atTop Set.univ :=
    Antitone.tendstoUniformlyOn_of_forall_tendsto isCompact_univ
      (fun t => (hcont t).continuousOn) hanti continuousOn_const (fun μ _ => hready μ)
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.1 hunif) (ε / 2) (half_pos hε)] with t ht
  have hbound : finiteDeficiency (E t) F ≤ ε / 2 := by
    apply finiteDeficiency_le_of_compactDecision_gaps (E t) F (hE t) hF
    intro μ
    have hm := ht μ trivial
    have hpos : 0 ≤ R t μ := le_max_right _ _
    simp only [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hpos] at hm
    exact (le_max_left _ _).trans hm.le
  have hnon : 0 ≤ finiteDeficiency (E t) F := finiteDeficiency_nonneg_of_valid _ _ (hE t) hF
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnon]
  exact hbound.trans_lt (half_lt_self hε)

/-- The same uniformity result with actual Blackwell refinement of the
finite experiments, discharging task-value monotonicity. -/
theorem compactDeficiency_tendsto_zero_of_pointwise_readiness [Nonempty Θ]
    {Xt : ℕ → Type*} [∀ t, Fintype (Xt t)]
    (E : ∀ t, FiniteExperiment Θ (Xt t)) (F : FiniteExperiment Θ Y)
    (hE : ∀ t, IsFiniteExperiment (E t)) (hF : IsFiniteExperiment F)
    (hcE : ∀ t x, Continuous (fun θ => E t θ x))
    (hcF : ∀ y, Continuous (fun θ => F θ y))
    (hchain : ∀ s t, s ≤ t → FiniteBlackwellLE (E s) (E t))
    (hready : ∀ μ : CompactDecisionTask Θ Y,
      Tendsto (fun t => max (compactDecisionValue F μ - compactDecisionValue (E t) μ) 0)
        atTop (𝓝 0)) :
    Tendsto (fun t => finiteDeficiency (E t) F) atTop (𝓝 0) :=
  compactDecisionDeficiency_tendsto_zero E F hE hF hcE hcF
    (fun μ s t hst => compactDecisionValue_mono_of_finiteBlackwellLE
      (E t) (E s) (hcE t) (hchain s t hst) μ) hready

end IdExp
