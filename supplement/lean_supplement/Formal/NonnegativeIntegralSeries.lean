import Formal.FiniteProbability

/-!
# Integrable nonnegative series from summable expectations

This measure-theoretic helper closes the gap between a series of expected
rewards and the expectation of their pathwise total. Nonnegativity is needed
only almost surely, separately at each countably many time indices. The
theorem establishes almost-sure summability and integrability of the total;
it does not hide divergent paths behind the real `tsum` convention.
-/

namespace IdExp

open MeasureTheory Filter
open scoped ENNReal

/-- A series of a.e. nonnegative integrable rewards with summable
expectations is a.s. summable, has an integrable pathwise total, and commutes
with expectation. No common bound on the individual rewards is assumed. -/
theorem integrable_tsum_of_nonneg_hasSum_integral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : ℕ → Ω → ℝ) (hf : ∀ n, Integrable (f n) μ)
    (hpos : ∀ n, 0 ≤ᵐ[μ] f n) (L : ℝ)
    (hsum : HasSum (fun n => ∫ ω, f n ω ∂μ) L) :
    (∀ᵐ ω ∂μ, Summable (fun n => f n ω)) ∧
      Integrable (fun ω => ∑' n, f n ω) μ ∧
      (∫ ω, ∑' n, f n ω ∂μ) = L := by
  have hnorm (n : ℕ) : (∫ ω, ‖f n ω‖ ∂μ) = ∫ ω, f n ω ∂μ := by
    apply integral_congr_ae
    filter_upwards [hpos n] with ω hω
    exact Real.norm_of_nonneg hω
  have hnormSum : Summable (fun n => ∫ ω, ‖f n ω‖ ∂μ) := by
    simpa only [hnorm] using hsum.summable
  have henorm (n : ℕ) : (∫⁻ ω, ‖f n ω‖ₑ ∂μ) =
      ENNReal.ofReal (∫ ω, ‖f n ω‖ ∂μ) :=
    (ofReal_integral_norm_eq_lintegral_enorm (hf n)).symm
  have hfinite : (∑' n, ∫⁻ ω, ‖f n ω‖ₑ ∂μ) ≠ ∞ := by
    simp_rw [henorm]
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun n => integral_nonneg (fun ω => norm_nonneg (f n ω))) hnormSum]
    exact ENNReal.ofReal_ne_top
  have hmeas (n : ℕ) : AEMeasurable (fun ω => ‖f n ω‖ₑ) μ :=
    (hf n).aestronglyMeasurable.enorm
  have hlin : (∫⁻ ω, ∑' n, ‖f n ω‖ₑ ∂μ) < ∞ := by
    rw [lintegral_tsum hmeas]
    exact lt_top_iff_ne_top.mpr hfinite
  have hae : ∀ᵐ ω ∂μ, Summable (fun n => f n ω) := by
    filter_upwards [ae_lt_top' (AEMeasurable.tsum hmeas) hlin.ne] with ω hω
    have hnormPoint : Summable (fun n => (‖f n ω‖₊ : ℝ)) := by
      rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
      exact hω.ne
    exact hnormPoint.of_norm
  have hint : Integrable (fun ω => ∑' n, f n ω) μ := by
    refine ⟨(AEMeasurable.tsum (fun n => (hf n).aemeasurable)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    exact (lintegral_mono (fun ω => enorm_tsum_le_tsum_enorm)).trans_lt hlin
  refine ⟨hae, hint, ?_⟩
  exact ((hasSum_integral_of_summable_integral_norm hf hnormSum).unique hsum)

end IdExp
