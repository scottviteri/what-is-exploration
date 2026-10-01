import Formal.MeasureDeficiencyCore
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Total variation controls weak convergence

This bridge is stated for finite measures, not just probability laws. It
supports compactness arguments for exact garbling into compact signal spaces.
-/

namespace IdExp

open MeasureTheory Filter Topology Set BoundedContinuousFunction

variable {Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y] [OpensMeasurableSpace Y]

/-- A bounded continuous test function detects at most twice its sup norm
times the half-variation distance. -/
theorem norm_integral_sub_le_finiteMeasureTV
    (μ ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : Y →ᵇ ℝ) :
    ‖(∫ y, f y ∂μ) - ∫ y, f y ∂ν‖ ≤ 2 * ‖f‖ * finiteMeasureTV μ ν := by
  let s := μ.toSignedMeasure - ν.toSignedMeasure
  let p := s.toJordanDecomposition.posPart
  let n := s.toJordanDecomposition.negPart
  have hjordan : p.toSignedMeasure - n.toSignedMeasure =
      μ.toSignedMeasure - ν.toSignedMeasure :=
    SignedMeasure.toSignedMeasure_toJordanDecomposition s
  have hbal : p + ν = μ + n := by
    rw [← Measure.toSignedMeasure_eq_toSignedMeasure_iff,
      Measure.toSignedMeasure_add, Measure.toSignedMeasure_add]
    exact sub_eq_sub_iff_add_eq_add.mp hjordan
  have hint : (∫ y, f y ∂p) + ∫ y, f y ∂ν =
      (∫ y, f y ∂μ) + ∫ y, f y ∂n := by
    rw [← integral_add_measure (f.integrable p) (f.integrable ν),
      ← integral_add_measure (f.integrable μ) (f.integrable n), hbal]
  have hmass : p.real univ + n.real univ = 2 * finiteMeasureTV μ ν := by
    unfold finiteMeasureTV
    change p.real univ + n.real univ = 2 * ((1 / 2) * (p + n).real univ)
    rw [measureReal_add_apply]
    ring
  calc
    ‖(∫ y, f y ∂μ) - ∫ y, f y ∂ν‖ =
        ‖(∫ y, f y ∂p) - ∫ y, f y ∂n‖ := by congr 1; linarith
    _ ≤ ‖∫ y, f y ∂p‖ + ‖∫ y, f y ∂n‖ := norm_sub_le _ _
    _ ≤ ‖f‖ * p.real univ + ‖f‖ * n.real univ :=
      add_le_add
        (norm_integral_le_of_norm_le_const (Eventually.of_forall f.norm_coe_le_norm))
        (norm_integral_le_of_norm_le_const (Eventually.of_forall f.norm_coe_le_norm))
    _ = 2 * ‖f‖ * finiteMeasureTV μ ν := by rw [← mul_add, hmass]; ring

/-- Convergence in total variation implies weak convergence of finite measures. -/
theorem tendsto_finiteMeasure_of_tendsto_TV_zero
    {ι : Type*} {l : Filter ι} {μs : ι → FiniteMeasure Y} {μ : FiniteMeasure Y}
    (h : Tendsto (fun i => finiteMeasureTV (μs i : Measure Y) (μ : Measure Y))
      l (𝓝 0)) :
    Tendsto μs l (𝓝 μ) := by
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro f
  apply tendsto_iff_norm_sub_tendsto_zero.2
  exact squeeze_zero (fun _ => norm_nonneg _) (fun i =>
    norm_integral_sub_le_finiteMeasureTV (μs i : Measure Y) (μ : Measure Y) f)
    (by simpa using h.const_mul (2 * ‖f‖))

end IdExp
