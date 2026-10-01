import Mathlib

/-!
# Total variation of finite measures

The common TV calculus: metric laws, Markov data processing, and the
measurable-event characterization for probability laws. No domination,
prefix process, sensor, or finiteness of the signal alphabet is assumed.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace IdExp

/-- Total variation distance for finite measures: one half of the total mass
of the variation of their signed difference. For probability measures this
is the usual supremum over measurable events. -/
noncomputable def finiteMeasureTV
    {Ω : Type*} [MeasurableSpace Ω]
    (ν ξ : Measure Ω) [IsFiniteMeasure ν] [IsFiniteMeasure ξ] : ℝ :=
  (1 / 2) * (ν.toSignedMeasure - ξ.toSignedMeasure).totalVariation.real Set.univ

theorem finiteMeasureTV_congr_left
    {Ω : Type*} [MeasurableSpace Ω]
    (ν ν' ξ : Measure Ω)
    [IsFiniteMeasure ν] [IsFiniteMeasure ν'] [IsFiniteMeasure ξ]
    (hν : ν = ν') : finiteMeasureTV ν ξ = finiteMeasureTV ν' ξ := by
  subst ν'
  rfl

theorem finiteMeasureTV_nonneg
    {X : Type*} [MeasurableSpace X] (ν ξ : Measure X)
    [IsFiniteMeasure ν] [IsFiniteMeasure ξ] : 0 ≤ finiteMeasureTV ν ξ := by
  unfold finiteMeasureTV
  positivity

/-! ## Total variation calculus -/

section TV

variable {Ω : Type*} [MeasurableSpace Ω]

theorem finiteMeasureTV_self (ν : Measure Ω) [IsFiniteMeasure ν] :
    finiteMeasureTV ν ν = 0 := by
  unfold finiteMeasureTV
  rw [sub_self, SignedMeasure.totalVariation_zero]
  simp

theorem finiteMeasureTV_symm (ν ξ : Measure Ω)
    [IsFiniteMeasure ν] [IsFiniteMeasure ξ] :
    finiteMeasureTV ν ξ = finiteMeasureTV ξ ν := by
  unfold finiteMeasureTV
  rw [← SignedMeasure.totalVariation_neg (ξ.toSignedMeasure - ν.toSignedMeasure),
    neg_sub]

/-- Rewriting both arguments of `finiteMeasureTV` by measure equalities. -/
theorem finiteMeasureTV_congr (ν ν' ξ ξ' : Measure Ω)
    [IsFiniteMeasure ν] [IsFiniteMeasure ν'] [IsFiniteMeasure ξ] [IsFiniteMeasure ξ']
    (hν : ν = ν') (hξ : ξ = ξ') : finiteMeasureTV ν ξ = finiteMeasureTV ν' ξ' := by
  subst ν'
  subst ξ'
  rfl

/-- The variation of the signed difference is dominated by the sum of the
variation measures of the two summands, through Mathlib's
`VectorMeasure.variation`.  Stated on `totalVariation` so every measure in
sight carries a finiteness instance. -/
theorem totalVariation_sub_le_add (ν ξ ρ : Measure Ω)
    [IsFiniteMeasure ν] [IsFiniteMeasure ξ] [IsFiniteMeasure ρ] :
    (ν.toSignedMeasure - ρ.toSignedMeasure).totalVariation ≤
      (ν.toSignedMeasure - ξ.toSignedMeasure).totalVariation +
        (ξ.toSignedMeasure - ρ.toSignedMeasure).totalVariation := by
  have hsplit : ν.toSignedMeasure - ρ.toSignedMeasure =
      (ν.toSignedMeasure - ξ.toSignedMeasure) +
        (ξ.toSignedMeasure - ρ.toSignedMeasure) := by
    abel
  rw [SignedMeasure.totalVariation_eq_variation,
    SignedMeasure.totalVariation_eq_variation,
    SignedMeasure.totalVariation_eq_variation, hsplit]
  exact VectorMeasure.variation_add_le

theorem finiteMeasureTV_triangle (ν ξ ρ : Measure Ω)
    [IsFiniteMeasure ν] [IsFiniteMeasure ξ] [IsFiniteMeasure ρ] :
    finiteMeasureTV ν ρ ≤ finiteMeasureTV ν ξ + finiteMeasureTV ξ ρ := by
  unfold finiteMeasureTV
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hle := totalVariation_sub_le_add ν ξ ρ Set.univ
  rw [Measure.add_apply] at hle
  rw [measureReal_def, measureReal_def, measureReal_def,
    ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  exact ENNReal.toReal_mono
    (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩) hle

/-- The total variation measure of a signed difference is at most the sum
of the two measures. -/
theorem totalVariation_sub_le (ν ξ : Measure Ω)
    [IsFiniteMeasure ν] [IsFiniteMeasure ξ] :
    (ν.toSignedMeasure - ξ.toSignedMeasure).totalVariation ≤ ν + ξ := by
  rw [SignedMeasure.totalVariation_eq_variation]
  calc _ ≤ ν.toSignedMeasure.variation + ξ.toSignedMeasure.variation :=
        VectorMeasure.variation_sub_le
    _ = ν + ξ := by
        rw [Measure.variation_toSignedMeasure, Measure.variation_toSignedMeasure]

/-- Total variation is at most half the sum of the two total masses. -/
theorem finiteMeasureTV_le_half_add_mass (ν ξ : Measure Ω)
    [IsFiniteMeasure ν] [IsFiniteMeasure ξ] :
    finiteMeasureTV ν ξ ≤ (1 / 2) * (ν.real Set.univ + ξ.real Set.univ) := by
  unfold finiteMeasureTV
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hle := totalVariation_sub_le ν ξ Set.univ
  rw [Measure.add_apply] at hle
  rw [measureReal_def, measureReal_def, measureReal_def,
    ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  exact ENNReal.toReal_mono
    (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩) hle

/-- Total variation between probability measures is at most one. -/
theorem finiteMeasureTV_le_one (ν ξ : Measure Ω)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ] :
    finiteMeasureTV ν ξ ≤ 1 := by
  refine (finiteMeasureTV_le_half_add_mass ν ξ).trans ?_
  rw [measureReal_def, measureReal_def, measure_univ, measure_univ, ENNReal.toReal_one]
  norm_num

end TV

/-! ## Data processing under Markov kernels -/

section DataProcessing

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- **Data processing for total variation.**  Pushing two finite measures
through the same Markov kernel cannot increase their total variation.  The
proof writes the signed difference `ν - ξ` through its Jordan decomposition
`p - n`, so that `p + ξ = ν + n` as measures; applying the kernel to both
sides and taking variations gives
`(κν - κξ).totalVariation ≤ κp + κn`, whose total mass is
`p(univ) + n(univ) = (ν - ξ).totalVariation(univ)` because Markov kernels
preserve mass. -/
theorem finiteMeasureTV_comp_le
    (κ : Kernel X Y) [IsMarkovKernel κ] (ν ξ : Measure X)
    [IsFiniteMeasure ν] [IsFiniteMeasure ξ] :
    finiteMeasureTV (κ ∘ₘ ν) (κ ∘ₘ ξ) ≤ finiteMeasureTV ν ξ := by
  let s : SignedMeasure X := ν.toSignedMeasure - ξ.toSignedMeasure
  let p : Measure X := s.toJordanDecomposition.posPart
  let n : Measure X := s.toJordanDecomposition.negPart
  have hjordan : p.toSignedMeasure - n.toSignedMeasure =
      ν.toSignedMeasure - ξ.toSignedMeasure :=
    SignedMeasure.toSignedMeasure_toJordanDecomposition s
  have hbal : p + ξ = ν + n := by
    rw [← Measure.toSignedMeasure_eq_toSignedMeasure_iff,
      Measure.toSignedMeasure_add, Measure.toSignedMeasure_add]
    exact sub_eq_sub_iff_add_eq_add.mp hjordan
  have hcomp : κ ∘ₘ p + κ ∘ₘ ξ = κ ∘ₘ ν + κ ∘ₘ n := by
    rw [← Measure.comp_add, ← Measure.comp_add, hbal]
  have hsigned : (κ ∘ₘ ν).toSignedMeasure - (κ ∘ₘ ξ).toSignedMeasure =
      (κ ∘ₘ p).toSignedMeasure - (κ ∘ₘ n).toSignedMeasure := by
    have h := Measure.toSignedMeasure_eq_toSignedMeasure_iff.mpr hcomp
    rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add] at h
    exact sub_eq_sub_iff_add_eq_add.mpr h.symm
  have hvar : ((κ ∘ₘ ν).toSignedMeasure - (κ ∘ₘ ξ).toSignedMeasure).totalVariation ≤
      κ ∘ₘ p + κ ∘ₘ n := by
    rw [hsigned]
    exact totalVariation_sub_le (κ ∘ₘ p) (κ ∘ₘ n)
  have huniv := hvar Set.univ
  rw [Measure.add_apply, Measure.comp_apply_univ, Measure.comp_apply_univ] at huniv
  have htv : (ν.toSignedMeasure - ξ.toSignedMeasure).totalVariation Set.univ =
      p Set.univ + n Set.univ := by
    show (p + n) Set.univ = _
    rw [Measure.add_apply]
  unfold finiteMeasureTV
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  rw [measureReal_def, measureReal_def, htv]
  exact ENNReal.toReal_mono
    (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩) huniv

/-- Deterministic special case of data processing: pushing forward along a
measurable map cannot increase total variation. -/
theorem finiteMeasureTV_map_le
    {f : X → Y} (hf : Measurable f) (ν ξ : Measure X)
    [IsFiniteMeasure ν] [IsFiniteMeasure ξ] :
    finiteMeasureTV (ν.map f) (ξ.map f) ≤ finiteMeasureTV ν ξ := by
  calc finiteMeasureTV (ν.map f) (ξ.map f)
      = finiteMeasureTV (Kernel.deterministic f hf ∘ₘ ν)
          (Kernel.deterministic f hf ∘ₘ ξ) :=
        finiteMeasureTV_congr _ _ _ _ (Measure.deterministic_comp_eq_map hf).symm
          (Measure.deterministic_comp_eq_map hf).symm
    _ ≤ finiteMeasureTV ν ξ := finiteMeasureTV_comp_le _ ν ξ

end DataProcessing

/-- Zero total variation of finite measures means equality of those measures. -/
theorem finiteMeasureTV_eq_zero_iff_eq
    {Y : Type*} [MeasurableSpace Y] (μ ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    finiteMeasureTV μ ν = 0 ↔ μ = ν := by
  constructor
  · intro h
    have hreal : (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation.real Set.univ = 0 := by
      unfold finiteMeasureTV at h
      linarith
    have huniv : (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation Set.univ = 0 :=
      ((ENNReal.toReal_eq_zero_iff _).1 hreal).resolve_right (measure_ne_top _ _)
    have hvar := Measure.measure_univ_eq_zero.1 huniv
    rw [SignedMeasure.totalVariation_eq_variation, VectorMeasure.variation_eq_zero] at hvar
    exact Measure.toSignedMeasure_eq_toSignedMeasure_iff.1 (sub_eq_zero.1 hvar)
  · rintro rfl
    exact finiteMeasureTV_self μ

section Events

variable {Y : Type*} [MeasurableSpace Y]

/-- For probability measures the half-variation is attained by a measurable
event. This is the Hahn/Jordan event, not a finite-output approximation. -/
theorem finiteMeasureTV_exists_event (μ ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ∃ B, MeasurableSet B ∧ finiteMeasureTV μ ν = μ.real B - ν.real B := by
  let s := μ.toSignedMeasure - ν.toSignedMeasure
  let p := s.toJordanDecomposition.posPart
  let n := s.toJordanDecomposition.negPart
  have hbal : p + ν = μ + n := by
    rw [← Measure.toSignedMeasure_eq_toSignedMeasure_iff,
      Measure.toSignedMeasure_add, Measure.toSignedMeasure_add]
    exact sub_eq_sub_iff_add_eq_add.mp
      (SignedMeasure.toSignedMeasure_toJordanDecomposition s)
  have hmass : p.real univ = n.real univ := by
    have h := congrArg (fun ξ : Measure Y => ξ.real univ) hbal
    rw [measureReal_add_apply, measureReal_add_apply,
      probReal_univ (μ := μ), probReal_univ (μ := ν)] at h
    linarith
  have hsing : p ⟂ₘ n := s.toJordanDecomposition.mutuallySingular
  let B := hsing.nullSetᶜ
  have hp : p.real B = p.real univ := by
    have h := measure_add_measure_compl hsing.measurableSet_nullSet (μ := p)
    rw [hsing.measure_nullSet, zero_add] at h
    exact congrArg ENNReal.toReal h
  have hn : n.real B = 0 := by
    exact congrArg ENNReal.toReal hsing.measure_compl_nullSet
  refine ⟨B, hsing.measurableSet_nullSet.compl, ?_⟩
  have h := congrArg (fun ξ : Measure Y => ξ.real B) hbal
  rw [measureReal_add_apply, measureReal_add_apply, hp, hn, add_zero] at h
  unfold finiteMeasureTV
  change (1 / 2 : ℝ) * (p + n).real univ = _
  rw [measureReal_add_apply, ← hmass]
  linarith

/-- Sharp measurable-event bound for probability laws. -/
theorem abs_measureReal_sub_le_finiteMeasureTV (μ ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (B : Set Y) (_hB : MeasurableSet B) :
    |μ.real B - ν.real B| ≤ finiteMeasureTV μ ν := by
  let s := μ.toSignedMeasure - ν.toSignedMeasure
  let p := s.toJordanDecomposition.posPart
  let n := s.toJordanDecomposition.negPart
  have hbal : p + ν = μ + n := by
    rw [← Measure.toSignedMeasure_eq_toSignedMeasure_iff,
      Measure.toSignedMeasure_add, Measure.toSignedMeasure_add]
    exact sub_eq_sub_iff_add_eq_add.mp
      (SignedMeasure.toSignedMeasure_toJordanDecomposition s)
  have hmass : p.real univ = n.real univ := by
    have h := congrArg (fun ξ : Measure Y => ξ.real univ) hbal
    rw [measureReal_add_apply, measureReal_add_apply,
      probReal_univ (μ := μ), probReal_univ (μ := ν)] at h
    linarith
  have heq : finiteMeasureTV μ ν = p.real univ := by
    unfold finiteMeasureTV
    change (1 / 2 : ℝ) * (p + n).real univ = _
    rw [measureReal_add_apply, ← hmass]
    ring
  have h := congrArg (fun ξ : Measure Y => ξ.real B) hbal
  rw [measureReal_add_apply, measureReal_add_apply] at h
  rw [heq]
  have hp := measureReal_mono (μ := p) (subset_univ B)
  have hn := measureReal_mono (μ := n) (subset_univ B)
  have hp0 := measureReal_nonneg (μ := p) (s := B)
  have hn0 := measureReal_nonneg (μ := n) (s := B)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Eventwise bounds suffice for TV, with no countability assumption. -/
theorem finiteMeasureTV_le_of_events (μ ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (c : ℝ)
    (h : ∀ B, MeasurableSet B → |μ.real B - ν.real B| ≤ c) :
    finiteMeasureTV μ ν ≤ c := by
  obtain ⟨B, hB, heq⟩ := finiteMeasureTV_exists_event μ ν
  rw [heq]
  exact (le_abs_self _).trans (h B hB)

end Events

end IdExp
