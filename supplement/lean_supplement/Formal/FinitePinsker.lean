import Formal.FiniteTV
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.InformationTheory.KullbackLeibler.KLFun

/-!
# Finite Pinsker inequality, including null coordinates

Natural logarithms are used. The real-valued KL sum is used only under
absolute continuity (`q x = 0 -> p x = 0`); without that hypothesis the usual
KL divergence can be infinite and Lean's totalized `log 0` would not represent it.
-/
namespace IdExp
open Finset Set
noncomputable section

private def pinskerRemainder (x : ℝ) : ℝ :=
  InformationTheory.klFun x - (3 / 2) * (x - 1)^2 / (x + 2)

private def pinskerRemainderDeriv (x : ℝ) : ℝ :=
  Real.log x - 3/2 + (27/2) / (x+2)^2

private theorem pinskerRemainder_hasDeriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt pinskerRemainder (pinskerRemainderDeriv x) x := by
  have hx2 : x+2 ≠ 0 := by linarith
  convert! (InformationTheory.hasDerivAt_klFun (ne_of_gt hx)).sub
    (((((hasDerivAt_id x).sub_const 1).pow 2).const_mul (3/2)).div
      ((hasDerivAt_id x).add_const 2) hx2) using 1
  dsimp [pinskerRemainderDeriv]
  field_simp
  ring

private theorem pinskerRemainderDeriv_hasDeriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt pinskerRemainderDeriv
      ((x-1)^2 * (x+8) / (x * (x+2)^3)) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hx2 : x+2 ≠ 0 := by linarith
  convert! ((Real.hasDerivAt_log hx0).sub_const (3/2)).add
    ((hasDerivAt_const x (27/2)).div
      (((hasDerivAt_id x).add_const 2).pow 2) (pow_ne_zero 2 hx2)) using 1
  dsimp
  field_simp
  ring

/-- A scalar KL lower bound whose weighted Cauchy--Schwarz consequence is sharp Pinsker. -/
theorem klFun_rational_lower {x : ℝ} (hx : 0 ≤ x) :
    (3/2 : ℝ) * (x-1)^2 / (x+2) ≤ InformationTheory.klFun x := by
  have hc : ContinuousOn pinskerRemainder (Ici 0) := by
    apply InformationTheory.continuous_klFun.continuousOn.sub
    exact (continuous_const.mul ((continuous_id.sub continuous_const).pow 2)).continuousOn.div
      (continuous_id.add continuous_const).continuousOn (fun x hx => by have : 0 ≤ x := hx; dsimp; linarith)
  have hconv : ConvexOn ℝ (Ici 0) pinskerRemainder := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici 0) hc
      (f' := pinskerRemainderDeriv)
      (f'' := fun x => (x-1)^2 * (x+8) / (x * (x+2)^3))
    · intro x hx
      exact (pinskerRemainder_hasDeriv (by simpa using hx)).hasDerivWithinAt
    · intro x hx
      exact (pinskerRemainderDeriv_hasDeriv (by simpa using hx)).hasDerivWithinAt
    · intro x hx
      have hx0 : 0 < x := by simpa using hx
      positivity
  have hd : derivWithin pinskerRemainder (Ioi 1) 1 = 0 := by
    rw [(pinskerRemainder_hasDeriv (by norm_num : (0:ℝ)<1)).hasDerivWithinAt.derivWithin
      (uniqueDiffWithinAt_Ioi 1)]
    norm_num [pinskerRemainderDeriv]
  have hm := hconv.isMinOn_of_rightDeriv_eq_zero (by norm_num : (1:ℝ) ∈ interior (Ici 0)) hd hx
  simp only [pinskerRemainder, InformationTheory.klFun_one] at hm
  norm_num at hm
  linarith

/-- Finite natural-log KL under a separately stated absolute-continuity condition. -/
def finiteKL {X : Type*} [Fintype X] (p q : X → ℝ) : ℝ :=
  ∑ x, p x * Real.log (p x / q x)

/-- The scalar perspective bound, with zeros in the numerator allowed. -/
theorem kl_row_quadratic_bound {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    3 / 2 * (p-q)^2 / (p+2*q) ≤ p * Real.log (p/q) + q-p := by
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hd : p+2*q ≠ 0 := by positivity
  calc
    _ = q * ((3/2) * (p/q-1)^2 / (p/q+2)) := by field_simp
    _ ≤ q * InformationTheory.klFun (p/q) :=
      mul_le_mul_of_nonneg_left (klFun_rational_lower (div_nonneg hp hq.le)) hq.le
    _ = _ := by unfold InformationTheory.klFun; field_simp

/-- Sharp finite Pinsker inequality in natural-log units. No positive-mass assumption
is imposed on either row; absolute continuity handles null coordinates correctly. -/
theorem finiteTV_sq_le_finiteKL_half {X : Type*} [Fintype X]
    (p q : X → ℝ) (hp : IsDist p) (hq : IsDist q)
    (hac : ∀ x, q x = 0 → p x = 0) :
    (finiteTV p q)^2 ≤ finiteKL p q / 2 := by
  have hrow : ∀ x, |p x-q x|^2 ≤
      ((p x+2*q x)/3) * (2*(p x * Real.log (p x/q x)+q x-p x)) := by
    intro x
    by_cases hqx : q x = 0
    · simp [hqx, hac x hqx]
    · have hpos : 0 < q x := lt_of_le_of_ne (hq.1 x) (Ne.symm hqx)
      have hd : 0 < p x+2*q x := by linarith [hp.1 x]
      have h := (div_le_iff₀ hd).mp (kl_row_quadratic_bound (hp.1 x) hpos)
      rw [sq_abs]
      nlinarith
  have hnonneg : ∀ x, 0 ≤ 2*(p x * Real.log (p x/q x)+q x-p x) := by
    intro x
    by_cases hqx : q x = 0
    · simp [hqx, hac x hqx]
    · have hpos : 0 < q x := lt_of_le_of_ne (hq.1 x) (Ne.symm hqx)
      have h := kl_row_quadratic_bound (hp.1 x) hpos
      have : 0 ≤ 3/2 * (p x-q x)^2 / (p x+2*q x) := by
        have := hp.1 x
        positivity
      linarith
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s := (univ : Finset X)) (r := fun x => |p x-q x|)
    (f := fun x => (p x+2*q x)/3)
    (g := fun x => 2*(p x * Real.log (p x/q x)+q x-p x))
    (fun x _ => by have := hp.1 x; have := hq.1 x; positivity)
    (fun x _ => hnonneg x) (fun x _ => hrow x)
  have hf : (∑ x, (p x+2*q x)/3) = 1 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, hp.2, hq.2]
    norm_num
  have hg : (∑ x, 2*(p x * Real.log (p x/q x)+q x-p x)) = 2*finiteKL p q := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib, hp.2, hq.2]
    simp [finiteKL]
  rw [hf, hg, one_mul] at hcs
  unfold finiteTV
  nlinarith

/-- Conventional finite KL, with infinity for a positive numerator over a zero denominator. -/
def finiteKLExtended {X : Type*} [Fintype X] (p q : X → ℝ) : EReal :=
  if ∀ x, q x = 0 → p x = 0 then (finiteKL p q : EReal) else ⊤

/-- A finite KL confidence bound discharges both absolute continuity and Pinsker. -/
theorem finiteTV_sq_le_half_of_KL_bound {X : Type*} [Fintype X]
    (p q : X → ℝ) (hp : IsDist p) (hq : IsDist q) {b : ℝ}
    (hKL : finiteKLExtended p q ≤ (b : EReal)) :
    (finiteTV p q)^2 ≤ b/2 := by
  classical
  unfold finiteKLExtended at hKL
  split_ifs at hKL with hac
  · exact (finiteTV_sq_le_finiteKL_half p q hp hq hac).trans
      (div_le_div_of_nonneg_right (EReal.coe_le_coe_iff.mp hKL) (by norm_num))
  · exact False.elim (by simpa using hKL)

end
end IdExp
