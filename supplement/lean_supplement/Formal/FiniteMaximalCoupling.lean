import Formal.MeasurableInformationForms

/-! A measurable maximal coupling for finite probability rows. -/

namespace IdExp
open Finset MeasureTheory
noncomputable section
variable {X : Type*} [Fintype X] [DecidableEq X]

def finiteMaximalCoupling (p q : X → ℝ) (z : X × X) : ℝ :=
  (if z.1 = z.2 then min (p z.1) (q z.1) else 0) +
    (p z.1 - min (p z.1) (q z.1)) * (q z.2 - min (p z.2) (q z.2)) / finiteTV p q

def finiteMismatch (j : X × X → ℝ) : ℝ :=
  ∑ x, ∑ y, if x = y then 0 else j (x, y)

omit [DecidableEq X] in
theorem sum_min_eq_one_sub_finiteTV (p q : X → ℝ) (hp : IsDist p) (hq : IsDist q) :
    (∑ x, min (p x) (q x)) = 1 - finiteTV p q := by
  have h (x : X) : min (p x) (q x) = (p x + q x - |p x - q x|) / 2 := by
    rcases le_total (p x) (q x) with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
  simp_rw [h]
  rw [← sum_div, sum_sub_distrib, sum_add_distrib, hp.2, hq.2]
  unfold finiteTV
  ring

theorem sum_residual_left (p q : X → ℝ) (hp : IsDist p) (hq : IsDist q) :
    (∑ x, (p x - min (p x) (q x))) = finiteTV p q := by
  rw [sum_sub_distrib, hp.2, sum_min_eq_one_sub_finiteTV p q hp hq]
  ring

theorem sum_residual_right (p q : X → ℝ) (hp : IsDist p) (hq : IsDist q) :
    (∑ x, (q x - min (p x) (q x))) = finiteTV p q := by
  rw [sum_sub_distrib, hq.2, sum_min_eq_one_sub_finiteTV p q hp hq]
  ring

theorem finiteMaximalCoupling_nonneg (p q : X → ℝ) (hp : IsDist p) (hq : IsDist q) (z : X × X) :
    0 ≤ finiteMaximalCoupling p q z := by
  unfold finiteMaximalCoupling
  apply add_nonneg
  · split_ifs
    · exact le_min (hp.1 _) (hq.1 _)
    · exact le_rfl
  · exact div_nonneg (mul_nonneg (sub_nonneg.mpr (min_le_left _ _))
      (sub_nonneg.mpr (min_le_right _ _))) (finiteTV_nonneg _ _)

theorem finiteMaximalCoupling_fst (p q : X → ℝ) (hp : IsDist p) (hq : IsDist q) (x : X) :
    (∑ y, finiteMaximalCoupling p q (x, y)) = p x := by
  simp only [finiteMaximalCoupling]
  rw [sum_add_distrib, ← sum_div, ← mul_sum, sum_residual_right p q hp hq]
  simp only [sum_ite_eq, mem_univ, if_true]
  by_cases hd : finiteTV p q = 0
  · have hz := (sum_eq_zero_iff_of_nonneg (fun y _ => sub_nonneg.mpr (min_le_left (p y) (q y)))).mp
      ((sum_residual_left p q hp hq).trans hd) x (mem_univ x)
    simp only [hd, mul_zero, zero_mul, zero_div, add_zero]
    linarith
  · rw [mul_div_cancel_right₀ _ hd]
    ring

theorem finiteMaximalCoupling_snd (p q : X → ℝ) (hp : IsDist p) (hq : IsDist q) (y : X) :
    (∑ x, finiteMaximalCoupling p q (x, y)) = q y := by
  simp only [finiteMaximalCoupling]
  rw [sum_add_distrib, ← sum_div, ← sum_mul, sum_residual_left p q hp hq]
  simp only [sum_ite_eq', mem_univ, if_true]
  by_cases hd : finiteTV p q = 0
  · have hz := (sum_eq_zero_iff_of_nonneg (fun x _ => sub_nonneg.mpr (min_le_right (p x) (q x)))).mp
      ((sum_residual_right p q hp hq).trans hd) y (mem_univ y)
    simp only [hd, mul_zero, zero_mul, zero_div, add_zero]
    linarith
  · rw [mul_div_cancel_left₀ _ hd]
    ring

theorem finiteMaximalCoupling_isDist (p q : X → ℝ) (hp : IsDist p) (hq : IsDist q) :
    IsDist (finiteMaximalCoupling p q) := by
  refine ⟨finiteMaximalCoupling_nonneg p q hp hq, ?_⟩
  rw [Fintype.sum_prod_type]
  simp_rw [finiteMaximalCoupling_fst p q hp hq]
  exact hp.2

theorem finiteMismatch_eq_sum_sub_diag (j : X × X → ℝ) :
    finiteMismatch j = (∑ z, j z) - ∑ x, j (x, x) := by
  unfold finiteMismatch
  have h (x : X) : (∑ y, if x = y then 0 else j (x, y)) = (∑ y, j (x, y)) - j (x, x) := by
    calc _ = ∑ y, (j (x, y) - if x = y then j (x, y) else 0) := by
          apply sum_congr rfl; intro y _; split_ifs <;> ring
      _ = _ := by rw [sum_sub_distrib]; simp
  simp_rw [h]
  rw [sum_sub_distrib, Fintype.sum_prod_type]

theorem finiteMaximalCoupling_diag (p q : X → ℝ) (x : X) :
    finiteMaximalCoupling p q (x, x) = min (p x) (q x) := by
  unfold finiteMaximalCoupling
  rcases le_total (p x) (q x) with h | h
  · simp [min_eq_left h]
  · simp [min_eq_right h]

theorem finiteMaximalCoupling_mismatch (p q : X → ℝ) (hp : IsDist p) (hq : IsDist q) :
    finiteMismatch (finiteMaximalCoupling p q) = finiteTV p q := by
  rw [finiteMismatch_eq_sum_sub_diag, (finiteMaximalCoupling_isDist p q hp hq).2]
  simp_rw [finiteMaximalCoupling_diag]
  rw [sum_min_eq_one_sub_finiteTV p q hp hq]
  ring

variable {Θ : Type*} [MeasurableSpace Θ]

omit [DecidableEq X] in
theorem measurable_finiteTV_rows (E F : FiniteExperiment Θ X)
    (hE : ∀ x, Measurable (fun θ => E θ x)) (hF : ∀ x, Measurable (fun θ => F θ x)) :
    Measurable (fun θ => finiteTV (E θ) (F θ)) := by
  unfold finiteTV
  exact measurable_const.mul (Finset.measurable_sum _ fun x _ => ((hE x).sub (hF x)).abs)

theorem measurable_finiteMaximalCoupling (E F : FiniteExperiment Θ X)
    (hE : ∀ x, Measurable (fun θ => E θ x)) (hF : ∀ x, Measurable (fun θ => F θ x)) (z : X × X) :
    Measurable (fun θ => finiteMaximalCoupling (E θ) (F θ) z) := by
  have hm x := (hE x).min (hF x)
  have hr := (((hE z.1).sub (hm z.1)).mul ((hF z.2).sub (hm z.2))).div (measurable_finiteTV_rows E F hE hF)
  unfold finiteMaximalCoupling
  by_cases hz : z.1 = z.2
  · simp only [if_pos hz]; exact (hm z.1).add hr
  · simp only [if_neg hz]; exact measurable_const.add hr

end
end IdExp
