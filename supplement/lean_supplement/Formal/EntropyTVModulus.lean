import Formal.FiniteProbability
import Formal.FiniteTV
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen

/-!
# An explicit total-variation modulus for finite entropy

Two elementary facts about `negMulLog x = -x log x` on `[0, 1]` give an
explicit modulus of continuity for entropy on a `k`-letter alphabet:

* subadditivity, `negMulLog (a + b) ≤ negMulLog a + negMulLog b`;
* `negMulLog y - negMulLog x ≤ x - y` for `0 ≤ y ≤ x ≤ 1`, because
  `t ↦ t log t - t` is nonincreasing on `[0, 1]`.

Together they give `|negMulLog x - negMulLog y| ≤ negMulLog |x - y| + |x - y|`,
and concavity (Jensen with uniform weights) turns the coordinatewise bound
into

`|ent p - ent q| ≤ k · negMulLog (2 TV(p,q) / k) + 4 TV(p,q)`.

The right-hand side is `entropyModulus k`, evaluated at the total variation.
It is monotone-usable (a bound at a larger radius dominates) and vanishes at
zero, so it is a `VanishingModulus` in the sense used for process-order
monotonicity.  No Fano inequality or coupling is needed.
-/

namespace IdExp

open Finset Real

noncomputable section

/-! ## Two one-line inequalities for `negMulLog` -/

/-- Subadditivity of `negMulLog` on the nonnegative reals. -/
theorem negMulLog_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    negMulLog (a + b) ≤ negMulLog a + negMulLog b := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp
  rcases eq_or_lt_of_le hb with rfl | hb'
  · simp
  simp only [negMulLog]
  have h1 : Real.log a ≤ Real.log (a + b) := Real.log_le_log ha' (by linarith)
  have h2 : Real.log b ≤ Real.log (a + b) := Real.log_le_log hb' (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left h1 ha'.le, mul_le_mul_of_nonneg_left h2 hb'.le]

/-- `t ↦ t log t - t` is nonincreasing on `[0, 1]`: for `0 ≤ y ≤ x ≤ 1`,
`negMulLog y - negMulLog x ≤ x - y`. -/
theorem negMulLog_sub_le_sub {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) (hx : x ≤ 1) :
    negMulLog y - negMulLog x ≤ x - y := by
  rcases eq_or_lt_of_le hy with rfl | hy'
  · have hx0 : 0 ≤ x := hyx
    have hlog : Real.log x ≤ 0 := Real.log_nonpos hx0 hx
    rw [negMulLog_zero, zero_sub, sub_zero, negMulLog]
    nlinarith [mul_nonneg hx0 (neg_nonneg.mpr hlog)]
  · have hx' : 0 < x := hy'.trans_le hyx
    simp only [negMulLog]
    have hlogx : Real.log x ≤ 0 := Real.log_nonpos hx'.le hx
    -- log x - log y = log (x / y) ≤ x / y - 1
    have hdiv : Real.log x - Real.log y ≤ x / y - 1 := by
      rw [← Real.log_div hx'.ne' hy'.ne']
      exact Real.log_le_sub_one_of_pos (div_pos hx' hy')
    have hyne : y ≠ 0 := hy'.ne'
    have hcancel : x / y * y = x := div_mul_cancel₀ x hyne
    have hxy' : y * (x / y - 1) = x - y := by
      rw [mul_sub, mul_one, mul_comm y (x / y), hcancel]
    have hy_mul : y * (Real.log x - Real.log y) ≤ x - y := by
      have := mul_le_mul_of_nonneg_left hdiv hy'.le
      linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hyx) (neg_nonneg.mpr hlogx), hy_mul]

/-- Coordinatewise modulus: `|negMulLog x - negMulLog y| ≤ negMulLog |x - y| + |x - y|`
on `[0, 1]`. -/
theorem abs_negMulLog_sub_le {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    |negMulLog x - negMulLog y| ≤ negMulLog |x - y| + |x - y| := by
  rcases le_total y x with hyx | hxy
  · have hd : |x - y| = x - y := abs_of_nonneg (by linarith : (0:ℝ) ≤ x - y)
    rw [hd, abs_le]
    constructor
    · have := negMulLog_sub_le_sub hy0 hyx hx1
      have := negMulLog_nonneg (by linarith : (0:ℝ) ≤ x - y) (by linarith)
      linarith
    · have hsub := negMulLog_add_le hy0 (by linarith : (0:ℝ) ≤ x - y)
      rw [show y + (x - y) = x by ring] at hsub
      linarith
  · have hd : |x - y| = y - x := by
      rw [abs_of_nonpos (by linarith : x - y ≤ 0)]; ring
    rw [hd, abs_le]
    constructor
    · have hsub := negMulLog_add_le hx0 (by linarith : (0:ℝ) ≤ y - x)
      rw [show x + (y - x) = y by ring] at hsub
      linarith
    · have := negMulLog_sub_le_sub hx0 hxy hy1
      have := negMulLog_nonneg (by linarith : (0:ℝ) ≤ y - x) (by linarith)
      linarith

/-- Values of `negMulLog` below a radius are dominated by its value at the
radius plus the radius: for `0 ≤ s ≤ r ≤ 1`, `negMulLog s ≤ negMulLog r + r`. -/
theorem negMulLog_le_of_le {s r : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) (hr : r ≤ 1) :
    negMulLog s ≤ negMulLog r + r := by
  have := negMulLog_sub_le_sub hs hsr hr
  linarith

/-! ## Entropy on a finite alphabet -/

variable {Y : Type*} [Fintype Y]

/-- The explicit modulus: `k · negMulLog (2 r / k) + 4 r`. -/
def entropyModulus (k : ℕ) (r : ℝ) : ℝ :=
  k * negMulLog (2 * r / k) + 4 * r

theorem entropyModulus_zero (k : ℕ) : entropyModulus k 0 = 0 := by
  simp [entropyModulus]

theorem continuous_entropyModulus (k : ℕ) : Continuous (entropyModulus k) := by
  unfold entropyModulus
  fun_prop

/-- The modulus is a vanishing modulus in the sense of process-order
monotonicity. -/
theorem entropyModulus_vanishing (k : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ r, 0 ≤ r → r < η → entropyModulus k r ≤ ε := by
  intro ε hε
  have hcont := (continuous_entropyModulus k).continuousAt (x := 0)
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨η, hη, h⟩ := hcont ε hε
  refine ⟨η, hη, fun r hr0 hr => ?_⟩
  have := h (by rw [Real.dist_eq, sub_zero, abs_of_nonneg hr0]; exact hr)
  rw [Real.dist_eq, entropyModulus_zero, sub_zero] at this
  exact (le_abs_self _).trans this.le

/-- Coordinatewise sum of `negMulLog` of gaps is at most `k · negMulLog` of
the mean gap (Jensen with uniform weights). -/
theorem sum_negMulLog_le_card_mul (d : Y → ℝ) (hd : ∀ y, 0 ≤ d y) :
    ∑ y, negMulLog (d y) ≤ (Fintype.card Y : ℝ) * negMulLog ((∑ y, d y) / Fintype.card Y) := by
  classical
  rcases Nat.eq_zero_or_pos (Fintype.card Y) with h0 | hpos
  · have : IsEmpty Y := Fintype.card_eq_zero_iff.mp h0
    simp
  have hk : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hpos
  have hk' : (Fintype.card Y : ℝ) ≠ 0 := hk.ne'
  have hj := concaveOn_negMulLog.le_map_sum (t := Finset.univ)
    (w := fun _ : Y => 1 / (Fintype.card Y : ℝ)) (p := d)
    (fun _ _ => by positivity)
    (by simp [Finset.sum_const, Finset.card_univ]; field_simp)
    (fun y _ => Set.mem_Ici.mpr (hd y))
  simp only [smul_eq_mul] at hj
  have hl : ∑ y, 1 / (Fintype.card Y : ℝ) * negMulLog (d y) =
      (∑ y, negMulLog (d y)) / Fintype.card Y := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro y _
    ring
  have hr : ∑ y, 1 / (Fintype.card Y : ℝ) * d y = (∑ y, d y) / Fintype.card Y := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [hl, hr] at hj
  rwa [div_le_iff₀ hk, mul_comm] at hj

/-- **Entropy is TV-continuous with the explicit modulus.**  For probability
vectors `p, q` on a `k`-letter alphabet with `TV(p, q) ≤ r` and `2 r ≤ k`,
`|ent p - ent q| ≤ entropyModulus k r`. -/
theorem abs_ent_sub_le_entropyModulus (p q : Y → ℝ) (hp : IsDist p) (hq : IsDist q)
    (r : ℝ) (hr0 : 0 ≤ r) (hrk : 2 * r ≤ Fintype.card Y) (htv : finiteTV p q ≤ r) :
    |ent p - ent q| ≤ entropyModulus (Fintype.card Y) r := by
  classical
  set k : ℝ := (Fintype.card Y : ℝ) with hk
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos (Fintype.card Y) with h0 | hpos
    · exfalso
      have : IsEmpty Y := Fintype.card_eq_zero_iff.mp h0
      have := hp.2
      simp at this
    · rw [hk]; exact_mod_cast hpos
  have hp1 : ∀ y, p y ≤ 1 := fun y =>
    (Finset.single_le_sum (fun z _ => hp.1 z) (Finset.mem_univ y)).trans hp.2.le
  have hq1 : ∀ y, q y ≤ 1 := fun y =>
    (Finset.single_le_sum (fun z _ => hq.1 z) (Finset.mem_univ y)).trans hq.2.le
  -- coordinatewise bound
  have hcoord : ∀ y, |negMulLog (p y) - negMulLog (q y)| ≤ negMulLog |p y - q y| + |p y - q y| :=
    fun y => abs_negMulLog_sub_le (hp.1 y) (hp1 y) (hq.1 y) (hq1 y)
  have hsum_abs : ∑ y, |p y - q y| = 2 * finiteTV p q := by
    unfold finiteTV; ring
  have hgap_le : ∑ y, |p y - q y| ≤ 2 * r := by linarith
  -- entropy difference
  have h1 : |ent p - ent q| ≤ ∑ y, (negMulLog |p y - q y| + |p y - q y|) := by
    unfold ent
    rw [← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => hcoord y)
  rw [Finset.sum_add_distrib] at h1
  -- Jensen over the alphabet
  have h2 := sum_negMulLog_le_card_mul (fun y => |p y - q y|) (fun y => abs_nonneg _)
  -- the mean gap is at most 2r/k ≤ 1, so the value at the mean is dominated by the modulus
  have hmean0 : 0 ≤ (∑ y, |p y - q y|) / k := by positivity
  have hmean_le : (∑ y, |p y - q y|) / k ≤ 2 * r / k := by
    exact div_le_div_of_nonneg_right hgap_le hkpos.le
  have h2rk : 2 * r / k ≤ 1 := by rw [div_le_one hkpos]; exact hrk
  have h3 := negMulLog_le_of_le hmean0 hmean_le h2rk
  have h4 : (∑ y, |p y - q y|) ≤ 2 * r := hgap_le
  have hkne : k ≠ 0 := hkpos.ne'
  unfold entropyModulus
  rw [← hk]
  calc |ent p - ent q|
      ≤ ∑ y, negMulLog |p y - q y| + ∑ y, |p y - q y| := h1
    _ ≤ k * negMulLog ((∑ y, |p y - q y|) / k) + 2 * r := by linarith
    _ ≤ k * (negMulLog (2 * r / k) + 2 * r / k) + 2 * r := by
        have := mul_le_mul_of_nonneg_left h3 hkpos.le
        linarith
    _ = k * negMulLog (2 * r / k) + 4 * r := by
        field_simp
        ring


/-- Total variation between distributions on a `k`-letter alphabet is at most
`k / 2`: it is at most one, and zero on a single letter. -/
theorem finiteTV_le_half_card (p q : Y → ℝ) (hp : IsDist p) (hq : IsDist q) :
    finiteTV p q ≤ (Fintype.card Y : ℝ) / 2 := by
  classical
  rcases Nat.lt_or_ge (Fintype.card Y) 2 with hlt | hge
  · -- at most one letter: the two distributions coincide
    have hle1 : Fintype.card Y ≤ 1 := by omega
    have hsub : Subsingleton Y := Fintype.card_le_one_iff_subsingleton.mp hle1
    have hpq : p = q := by
      funext y
      have h1 : ∑ z, p z = p y := by
        rw [Finset.sum_eq_single y] <;> simp [Subsingleton.elim _ y]
      have h2 : ∑ z, q z = q y := by
        rw [Finset.sum_eq_single y] <;> simp [Subsingleton.elim _ y]
      rw [← h1, ← h2, hp.2, hq.2]
    rw [hpq, (finiteTV_eq_zero_iff q q).mpr rfl]
    positivity
  · have h1 := finiteTV_le_one_of_isDist p q hp hq
    have : (2 : ℝ) ≤ Fintype.card Y := by exact_mod_cast hge
    linarith

/-- The capped modulus `entropyModulus k (min r (k/2))`: valid without any
side condition relating the radius to the alphabet size. -/
def cappedEntropyModulus (k : ℕ) (r : ℝ) : ℝ :=
  entropyModulus k (min r ((k : ℝ) / 2))

theorem cappedEntropyModulus_vanishing (k : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ r, 0 ≤ r → r < η → cappedEntropyModulus k r ≤ ε := by
  intro ε hε
  obtain ⟨η, hη, h⟩ := entropyModulus_vanishing k ε hε
  refine ⟨η, hη, fun r hr0 hr => ?_⟩
  unfold cappedEntropyModulus
  apply h
  · exact le_min hr0 (by positivity)
  · exact (min_le_left _ _).trans_lt hr

theorem continuous_cappedEntropyModulus (k : ℕ) : Continuous (cappedEntropyModulus k) := by
  unfold cappedEntropyModulus
  exact (continuous_entropyModulus k).comp (continuous_id.min continuous_const)

/-- **Entropy is TV-continuous with the capped modulus**, with no side
condition on the radius. -/
theorem abs_ent_sub_le_cappedEntropyModulus (p q : Y → ℝ) (hp : IsDist p) (hq : IsDist q)
    (r : ℝ) (hr0 : 0 ≤ r) (htv : finiteTV p q ≤ r) :
    |ent p - ent q| ≤ cappedEntropyModulus (Fintype.card Y) r := by
  unfold cappedEntropyModulus
  apply abs_ent_sub_le_entropyModulus p q hp hq
  · exact le_min hr0 (by positivity)
  · have := min_le_right r ((Fintype.card Y : ℝ) / 2)
    linarith
  · exact le_min htv (finiteTV_le_half_card p q hp hq)

end

end IdExp
