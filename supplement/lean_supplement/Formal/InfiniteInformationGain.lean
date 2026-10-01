import Formal.InfinitePriorPosterior
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Strict information-gain comparison on continuous infinite world classes

The information functional is the expected KL of posterior likelihood-ratio
densities relative to the actual prior. Its entropy is defined by an
integral of `f * log f`; no differential-entropy subtraction occurs.
Continuity and full topological support make that integral strictly convex
on bounded nonnegative continuous densities. No compactness, finite-world,
or exact-identification assumption is used.
-/

set_option maxHeartbeats 1000000

namespace IdExp

open MeasureTheory Set Finset

variable {Θ X : Type*} [TopologicalSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]

/-- Nonnegative bounded continuous functions, an ambient convex domain
containing every finite-signal posterior likelihood-ratio density. -/
def boundedContinuousDensityDomain : Set (Θ → ℝ) :=
  {f | Continuous f ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ θ, f θ ∈ Icc 0 M}

theorem convex_boundedContinuousDensityDomain :
    Convex ℝ (boundedContinuousDensityDomain (Θ := Θ)) := by
  rintro f ⟨hf, M, hM, hfM⟩ g ⟨hg, N, hN, hgN⟩ a b ha hb hab
  refine ⟨(hf.const_smul a).add (hg.const_smul b),
    a * M + b * N, add_nonneg (mul_nonneg ha hM) (mul_nonneg hb hN), ?_⟩
  intro θ
  change a * f θ + b * g θ ∈ Icc 0 (a * M + b * N)
  exact ⟨add_nonneg (mul_nonneg ha (hfM θ).1) (mul_nonneg hb (hgN θ).1),
    add_le_add (mul_le_mul_of_nonneg_left (hfM θ).2 ha)
      (mul_le_mul_of_nonneg_left (hgN θ).2 hb)⟩

noncomputable def densityInformationPotential (μ : Measure Θ) (f : Θ → ℝ) : ℝ :=
  ∫ θ, f θ * Real.log (f θ) ∂μ

/-- Bounded continuous density entropy is integrable under every finite prior. -/
theorem integrable_density_mul_log (μ : Measure Θ) [IsFiniteMeasure μ]
    {f : Θ → ℝ} (hf : f ∈ boundedContinuousDensityDomain) :
    Integrable (fun θ => f θ * Real.log (f θ)) μ := by
  obtain ⟨hc, M, hM, hbound⟩ := hf
  have hb : BddAbove ((fun x : ℝ => |x * Real.log x|) '' Icc 0 M) :=
    (isCompact_Icc.image Real.continuous_mul_log.abs).bddAbove
  obtain ⟨B, hB⟩ := hb
  apply (integrable_const B).mono'
    (Real.continuous_mul_log.comp hc).measurable.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro θ
  exact hB ⟨f θ, hbound θ, rfl⟩

/-- Full support supplies strictness in the world-uniform sense: a
continuous density distinction is visible on a positive-prior open set. -/
theorem strictConvexOn_densityInformationPotential
    (μ : Measure Θ) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] :
    StrictConvexOn ℝ boundedContinuousDensityDomain (densityInformationPotential μ) := by
  refine ⟨convex_boundedContinuousDensityDomain, ?_⟩
  intro f hf g hg hne a b ha hb hab
  obtain ⟨θ, hθ⟩ : ∃ θ, f θ ≠ g θ := Function.ne_iff.mp hne
  let k : Θ → ℝ := a • f + b • g
  have hk : k ∈ boundedContinuousDensityDomain :=
    convex_boundedContinuousDensityDomain hf hg ha.le hb.le hab
  let d : Θ → ℝ := fun θ => a * (f θ * Real.log (f θ)) +
    b * (g θ * Real.log (g θ)) - k θ * Real.log (k θ)
  have hdcont : Continuous d :=
    (((Real.continuous_mul_log.comp hf.1).const_smul a).add
      ((Real.continuous_mul_log.comp hg.1).const_smul b)).sub
      (Real.continuous_mul_log.comp hk.1)
  have hdint : Integrable d μ :=
    (((integrable_density_mul_log μ hf).const_mul a).add
      ((integrable_density_mul_log μ hg).const_mul b)).sub
      (integrable_density_mul_log μ hk)
  have hfn (z : Θ) : 0 ≤ f z := hf.2.choose_spec.2 z |>.1
  have hgn (z : Θ) : 0 ≤ g z := hg.2.choose_spec.2 z |>.1
  have hdnonneg : 0 ≤ d := by
    intro z
    have hj := Real.strictConvexOn_mul_log.convexOn.2 (hfn z) (hgn z) ha.le hb.le hab
    change 0 ≤ a * (f z * Real.log (f z)) + b * (g z * Real.log (g z)) -
      (a * f z + b * g z) * Real.log (a * f z + b * g z)
    exact sub_nonneg.mpr hj
  have hdpos : 0 < d θ := by
    have hj := Real.strictConvexOn_mul_log.2 (hfn θ) (hgn θ) hθ ha hb hab
    exact sub_pos.mpr hj
  have hp := integral_pos_of_integrable_nonneg_nonzero hdcont hdint hdnonneg (ne_of_gt hdpos)
  have hfi := integrable_density_mul_log μ hf
  have hgi := integrable_density_mul_log μ hg
  have hki := integrable_density_mul_log μ hk
  dsimp [d] at hp
  have hsub := integral_sub ((hfi.const_mul a).add (hgi.const_mul b)) hki
  have hadd := integral_add (hfi.const_mul a) (hgi.const_mul b)
  simp only [Pi.add_apply] at hsub hadd
  rw [hsub, hadd, integral_const_mul, integral_const_mul] at hp
  exact sub_pos.mp hp

/-- Literal finite-signal posterior densities belong to the strict domain,
including the prior density one at every null signal. -/
theorem priorSignalDensity_mem_boundedContinuousDensityDomain
    (μ : Measure Θ) [IsFiniteMeasure μ]
    (E : FiniteExperiment Θ X) [Fintype X] (hE : IsFiniteExperiment E)
    (hc : ∀ x, Continuous (fun θ => E θ x)) (x : X) :
    priorSignalDensity μ E x ∈ boundedContinuousDensityDomain := by
  by_cases hx : priorSignalMass μ E x = 0
  · refine ⟨?_, 1, zero_le_one, ?_⟩
    · change Continuous (fun θ => if priorSignalMass μ E x = 0 then 1 else E θ x / priorSignalMass μ E x)
      simp only [if_pos hx]
      exact continuous_const
    · intro θ; simp [priorSignalDensity, hx]
  · have hm : 0 ≤ priorSignalMass μ E x := integral_nonneg fun θ => (hE θ).1 x
    have hmp : 0 < priorSignalMass μ E x := lt_of_le_of_ne hm (Ne.symm hx)
    refine ⟨?_, 1 / priorSignalMass μ E x, div_nonneg zero_le_one hm, ?_⟩
    · change Continuous (fun θ => if priorSignalMass μ E x = 0 then 1 else E θ x / priorSignalMass μ E x)
      simp only [if_neg hx]
      exact (hc x).div_const (priorSignalMass μ E x)
    · intro θ
      simp only [priorSignalDensity, if_neg hx]
      refine ⟨div_nonneg ((hE θ).1 x) hm, div_le_div_of_nonneg_right ?_ hm⟩
      exact (Finset.single_le_sum (fun z _ => (hE θ).1 z) (mem_univ x)).trans_eq (hE θ).2

/-- Finite-signal information gain on an arbitrary measurable world class,
written directly as expected relative entropy of posterior densities. -/
noncomputable def infinitePriorInformation [Fintype X]
    (μ : Measure Θ) (E : FiniteExperiment Θ X) : ℝ :=
  priorSignalPotential μ E (densityInformationPotential μ)

/-- Strict Blackwell domination forces strictly less information gain under
a full-support prior and continuous finite-signal laws. -/
theorem continuous_infinitePriorInformation_lt_of_no_reverse
    {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X]
    (μ : Measure Θ) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (hcE : ∀ x, Continuous (fun θ => E θ x))
    (hcF : ∀ y, Continuous (fun θ => F θ y))
    (G : X → Y → ℝ) (hG : G ∈ stochasticRules X Y)
    (hGF : finiteDecisionLaw E G = F)
    (hnot : ¬ ∃ R ∈ stochasticRules Y X, finiteDecisionLaw F R = E) :
    infinitePriorInformation μ F < infinitePriorInformation μ E :=
  continuous_priorSignalPotential_lt_of_no_reverse μ E F hE hF hcE hcF G hG hGF
    (densityInformationPotential μ) boundedContinuousDensityDomain
    (strictConvexOn_densityInformationPotential μ)
    (priorSignalDensity_mem_boundedContinuousDensityDomain μ E hE hcE) hnot

end IdExp
