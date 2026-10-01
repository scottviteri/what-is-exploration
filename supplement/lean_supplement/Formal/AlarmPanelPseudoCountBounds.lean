import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! Bounds for the actual continuing inverse-square-root count bonus. -/
noncomputable section
namespace IdExp.AlarmPanel.PseudoCountBounds
open Finset

def countSum (n : ℕ) : ℝ := ∑ k ∈ range n, 1 / Real.sqrt ((k : ℝ) + 1)
@[simp] theorem countSum_zero : countSum 0 = 0 := by simp [countSum]
theorem countSum_succ (n : ℕ) :
    countSum (n+1) = countSum n + 1 / Real.sqrt ((n : ℝ)+1) := by
  simp [countSum, sum_range_succ]
theorem countSum_nonneg (n : ℕ) : 0 ≤ countSum n := by
  apply sum_nonneg; intro k hk; positivity
theorem countSum_mono : Monotone countSum := by
  apply monotone_nat_of_le_succ
  intro n
  rw [countSum_succ]
  exact le_add_of_nonneg_right (by positivity)
theorem countTerm_antitone : Antitone (fun n : ℕ => 1 / Real.sqrt ((n : ℝ)+1)) := by
  intro a b hab
  apply one_div_le_one_div_of_le (Real.sqrt_pos.2 (by positivity))
  apply Real.sqrt_le_sqrt
  exact_mod_cast Nat.add_le_add_right hab 1
theorem countSum_add_le (a b : ℕ) :
    countSum (a+b) ≤ countSum a + countSum b := by
  unfold countSum
  rw [sum_range_add]
  apply add_le_add le_rfl
  apply sum_le_sum
  intro k hk
  exact countTerm_antitone (Nat.le_add_left k a)
theorem countSum_le_nat (n : ℕ) : countSum n ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [countSum_succ]
    have hb := countTerm_antitone (Nat.zero_le n)
    simp only [Nat.cast_zero, zero_add, Real.sqrt_one, div_one] at hb
    push_cast
    linarith
theorem countTerm_upper (n : ℕ) :
    1 / Real.sqrt ((n : ℝ)+1) ≤
      2 * (Real.sqrt ((n : ℝ)+1) - Real.sqrt (n : ℝ)) := by
  have hp : 0 < Real.sqrt ((n : ℝ)+1) := Real.sqrt_pos.2 (by positivity)
  apply (div_le_iff₀ hp).2
  have ha := Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ)+1)
  have hb := Real.sq_sqrt (Nat.cast_nonneg n : 0 ≤ (n : ℝ))
  nlinarith [sq_nonneg (Real.sqrt ((n : ℝ)+1) - Real.sqrt (n : ℝ))]
theorem countTerm_lower (n : ℕ) :
    2 * (Real.sqrt ((n : ℝ)+2) - Real.sqrt ((n : ℝ)+1)) ≤
      1 / Real.sqrt ((n : ℝ)+1) := by
  have hp : 0 < Real.sqrt ((n : ℝ)+1) := Real.sqrt_pos.2 (by positivity)
  apply (le_div_iff₀ hp).2
  have ha := Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ)+1)
  have hb := Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ)+2)
  nlinarith [sq_nonneg (Real.sqrt ((n : ℝ)+2) - Real.sqrt ((n : ℝ)+1))]
theorem countSum_le_two_sqrt (n : ℕ) : countSum n ≤ 2 * Real.sqrt (n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [countSum_succ]
    push_cast
    linarith [countTerm_upper n]
theorem two_sqrt_sub_two_le_countSum (n : ℕ) :
    2 * Real.sqrt ((n : ℝ)+1) - 2 ≤ countSum n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [countSum_succ]
    push_cast
    have he : (n : ℝ)+1+1 = (n : ℝ)+2 := by ring
    rw [he]
    linarith [countTerm_lower n]
theorem sqrt_le_countSum (n : ℕ) : Real.sqrt (n : ℝ) ≤ countSum n := by
  cases n with
  | zero => simp
  | succ n =>
    have hp : 0 < Real.sqrt ((n+1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
    have hb : ((n+1 : ℕ) : ℝ) * (1 / Real.sqrt ((n+1 : ℕ) : ℝ)) ≤ countSum (n+1) := by
      calc
        _ = ∑ k ∈ range (n+1), 1 / Real.sqrt ((n+1 : ℕ) : ℝ) := by simp
        _ ≤ _ := by
          apply sum_le_sum
          intro k hk
          apply one_div_le_one_div_of_le (Real.sqrt_pos.2 (by positivity))
          apply Real.sqrt_le_sqrt
          exact_mod_cast (mem_range.mp hk)
    have he : ((n+1 : ℕ) : ℝ) * (1 / Real.sqrt ((n+1 : ℕ) : ℝ)) =
        Real.sqrt ((n+1 : ℕ) : ℝ) := by
      have hs := Real.sq_sqrt (by positivity : 0 ≤ ((n+1 : ℕ) : ℝ))
      field_simp
      nlinarith
    rwa [he] at hb

/-- A conservative uniform gap; the threshold is not asserted minimal. -/
theorem countSum_large_horizon_gap (T : ℕ) (hT : 64 ≤ T) :
    2 * Real.sqrt (T : ℝ) + 2 <
      countSum (T/2) + countSum ((T-1)/2-1) := by
  have hTr : (64 : ℝ) ≤ T := by exact_mod_cast hT
  have hx : 0 ≤ (T : ℝ)/2-1 := by linarith
  have hy := Real.sqrt_nonneg (T : ℝ)
  have hz := Real.sqrt_nonneg ((T : ℝ)/2-1)
  have hy2 := Real.sq_sqrt (Nat.cast_nonneg T : 0 ≤ (T : ℝ))
  have hz2 := Real.sq_sqrt hx
  have hy8 : 8 ≤ Real.sqrt (T : ℝ) := by nlinarith
  have hgap : Real.sqrt (T : ℝ)+3 < 2*Real.sqrt ((T : ℝ)/2-1) := by
    by_contra hn
    push Not at hn
    have hprod := mul_nonneg
      (show 0 ≤ Real.sqrt (T : ℝ)+3-2*Real.sqrt ((T : ℝ)/2-1) by linarith)
      (show 0 ≤ Real.sqrt (T : ℝ)+3+2*Real.sqrt ((T : ℝ)/2-1) by positivity)
    have hquad := mul_nonneg
      (show 0 ≤ Real.sqrt (T : ℝ)-8 by linarith)
      (show 0 ≤ Real.sqrt (T : ℝ)+2 by positivity)
    nlinarith
  have hnNat : T ≤ 2*(T/2+1) := by omega
  have hmNat : T ≤ 2*((T-1)/2)+2 := by omega
  have hnReal : (T : ℝ) ≤ 2*((T/2 : ℕ)+1 : ℝ) := by exact_mod_cast hnNat
  have hmReal : (T : ℝ) ≤ 2*((T-1)/2 : ℕ)+2 := by exact_mod_cast hmNat
  have hnSqrt : Real.sqrt ((T : ℝ)/2-1) ≤ Real.sqrt ((T/2 : ℕ)+1 : ℝ) :=
    Real.sqrt_le_sqrt (by linarith)
  have hmSqrt : Real.sqrt ((T : ℝ)/2-1) ≤ Real.sqrt (((T-1)/2 : ℕ) : ℝ) :=
    Real.sqrt_le_sqrt (by linarith)
  have hnLower := two_sqrt_sub_two_le_countSum (T/2)
  have hmLower := two_sqrt_sub_two_le_countSum ((T-1)/2-1)
  have hmPos : 1 ≤ (T-1)/2 := by omega
  have he : (((T-1)/2-1 : ℕ) : ℝ)+1 = (((T-1)/2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hmPos
  rw [he] at hmLower
  linarith

end IdExp.AlarmPanel.PseudoCountBounds
