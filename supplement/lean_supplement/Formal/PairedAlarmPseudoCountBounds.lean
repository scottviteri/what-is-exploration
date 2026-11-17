import Formal.AlarmPanelPseudoCountBounds

/-!
# Square-root gap for the alternating-play witness

`countSum n = Σ_{k<n} 1/√(k+1)` is the cumulative inverse-square-root bonus
`S(n)` of the paper; its interface-independent bounds
`2√(n+1)-2 ≤ S(n) ≤ 2√n` and `S(a+b) ≤ S(a)+S(b)` are reused from
`Formal.AlarmPanelPseudoCountBounds`. On the simultaneous interface the
alternating PLAY₀/PLAY₁ witness guarantees, on every supported history of
length `H`, at least `⌊H/2⌋-1` monitor-zero labels with low display and
`⌊(H-1)/2⌋-1` with high display. The gap below compares the resulting
`S(⌊H/2⌋-1)+S(⌊(H-1)/2⌋-1) ≥ 4√(H/2-1)-4 = 2√(2H-4)-4` with the
inspection-branch ceiling `2√H+2`; `H ≥ 64` is a convenient sufficient
threshold, not asserted minimal.
-/

noncomputable section
namespace IdExp.PairedAlarm.PseudoCount
open Finset IdExp.AlarmPanel.PseudoCountBounds

/-- The uniform gap behind the large-horizon optimizer theorem. -/
theorem countSum_alternating_gap (H : ℕ) (hH : 64 ≤ H) :
    2 * Real.sqrt (H : ℝ) + 2 <
      countSum (H / 2 - 1) + countSum ((H - 1) / 2 - 1) := by
  have hHr : (64 : ℝ) ≤ H := by exact_mod_cast hH
  have hx : 0 ≤ (H : ℝ) / 2 - 1 := by linarith
  have hy := Real.sqrt_nonneg (H : ℝ)
  have hz := Real.sqrt_nonneg ((H : ℝ) / 2 - 1)
  have hy2 := Real.sq_sqrt (Nat.cast_nonneg H : 0 ≤ (H : ℝ))
  have hz2 := Real.sq_sqrt hx
  have hy8 : 8 ≤ Real.sqrt (H : ℝ) := by nlinarith
  -- `√H + 3 < 2√(H/2-1)`, i.e. `H - 6√H - 13 > 0` once `√H ≥ 8`.
  have hgap : Real.sqrt (H : ℝ) + 3 < 2 * Real.sqrt ((H : ℝ) / 2 - 1) := by
    by_contra hn
    push Not at hn
    have hprod := mul_nonneg
      (show 0 ≤ Real.sqrt (H : ℝ) + 3 - 2 * Real.sqrt ((H : ℝ) / 2 - 1) by linarith)
      (show 0 ≤ Real.sqrt (H : ℝ) + 3 + 2 * Real.sqrt ((H : ℝ) / 2 - 1) by positivity)
    have hquad := mul_nonneg
      (show 0 ≤ Real.sqrt (H : ℝ) - 8 by linarith)
      (show 0 ≤ Real.sqrt (H : ℝ) + 2 by positivity)
    nlinarith
  -- Both natural-number arguments are at least `H/2 - 1` after adding one.
  have hnPos : 1 ≤ H / 2 := by omega
  have hmPos : 1 ≤ (H - 1) / 2 := by omega
  have hnNat : H ≤ 2 * (H / 2) + 2 := by omega
  have hmNat : H ≤ 2 * ((H - 1) / 2) + 2 := by omega
  have hnReal : (H : ℝ) ≤ 2 * ((H / 2 : ℕ) : ℝ) + 2 := by exact_mod_cast hnNat
  have hmReal : (H : ℝ) ≤ 2 * (((H - 1) / 2 : ℕ) : ℝ) + 2 := by exact_mod_cast hmNat
  have hnSqrt : Real.sqrt ((H : ℝ) / 2 - 1) ≤ Real.sqrt ((H / 2 : ℕ) : ℝ) :=
    Real.sqrt_le_sqrt (by linarith)
  have hmSqrt : Real.sqrt ((H : ℝ) / 2 - 1) ≤ Real.sqrt (((H - 1) / 2 : ℕ) : ℝ) :=
    Real.sqrt_le_sqrt (by linarith)
  have hnLower := two_sqrt_sub_two_le_countSum (H / 2 - 1)
  have hmLower := two_sqrt_sub_two_le_countSum ((H - 1) / 2 - 1)
  have hne : (((H / 2 - 1 : ℕ)) : ℝ) + 1 = ((H / 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hnPos
  have hme : (((H - 1) / 2 - 1 : ℕ) : ℝ) + 1 = (((H - 1) / 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hmPos
  rw [hne] at hnLower
  rw [hme] at hmLower
  linarith

end IdExp.PairedAlarm.PseudoCount
