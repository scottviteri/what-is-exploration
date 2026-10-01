import Formal.FiniteMaximalCoupling
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-! The finite Fano conditional-entropy bound, in natural logarithms. -/
namespace IdExp
open Finset
noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y]

def finiteMarginalSnd (j : X × Y → ℝ) (y : Y) : ℝ := ∑ x, j (x, y)

theorem finiteMarginalSnd_isDist (j : X × Y → ℝ) (hj : IsDist j) :
    IsDist (finiteMarginalSnd j) := by
  refine ⟨fun y => sum_nonneg fun x _ => hj.1 (x, y), ?_⟩
  unfold finiteMarginalSnd
  rw [sum_comm, ← Fintype.sum_prod_type]
  exact hj.2

omit [Fintype X] in
theorem negMulLog_sum_le (s : Finset X) (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) :
    Real.negMulLog (∑ x ∈ s, f x) ≤ ∑ x ∈ s, Real.negMulLog (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (negMulLog_add_le (hf a) (sum_nonneg fun x _ => hf x)).trans (add_le_add le_rfl ih)

theorem ent_marginal_snd_le (j : X × Y → ℝ) (hj : ∀ z, 0 ≤ j z) :
    ent (finiteMarginalSnd j) ≤ ent j := by
  unfold ent finiteMarginalSnd
  rw [Fintype.sum_prod_type, sum_comm]
  exact sum_le_sum fun y _ => negMulLog_sum_le univ _ (fun x => hj (x, y))

theorem ent_le_crossEntropy (p q : X → ℝ) (hp : IsDist p) (hq : IsDist q)
    (hac : ∀ x, q x = 0 → p x = 0) : ent p ≤ -(∑ x, p x * Real.log (q x)) := by
  have h := finiteTV_sq_le_finiteKL_half p q hp hq hac
  have hkl : finiteKL p q = -ent p - ∑ x, p x * Real.log (q x) := by
    have ht (x : X) : p x * Real.log (p x / q x) =
        p x * Real.log (p x) - p x * Real.log (q x) := by
      by_cases hx : q x = 0
      · simp [hx, hac x hx]
      · exact mul_log_div_eq _ _ hx
    simp_rw [finiteKL, ht, sum_sub_distrib, ent, Real.negMulLog, neg_mul, sum_neg_distrib]
    ring
  rw [hkl] at h
  nlinarith [sq_nonneg (finiteTV p q)]

variable [Nonempty X] [DecidableEq X]

def fanoNoise (r : ℝ) (y x : X) : ℝ :=
  (if y = x then 1 - r else 0) + r * uniformPrior X x

theorem fanoNoise_stochastic (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    fanoNoise (X := X) r ∈ stochasticRules X X := by
  intro y _
  constructor
  · intro x
    exact add_nonneg (by split_ifs <;> linarith)
      (mul_nonneg hr0 ((isDist_uniformPrior (Θ := X)).1 x))
  · simp only [fanoNoise, sum_add_distrib, ← mul_sum, (isDist_uniformPrior (Θ := X)).2,
      sum_ite_eq, mem_univ, if_true, mul_one]
    ring

/-- Any coupling with mismatch at most r has conditional entropy at most
h(r) + r log |X|, for 0 < r <= 1/2. The boundary r=0 is handled separately. -/
theorem ent_sub_marginal_le_fano_pos (j : X × X → ℝ) (hj : IsDist j)
    (r : ℝ) (hr : 0 < r) (hrhalf : r ≤ 1 / 2) (hmis : finiteMismatch j ≤ r) :
    ent j - ent (finiteMarginalSnd j) ≤ Real.binEntropy r + r * Real.log (Fintype.card X) := by
  let m := finiteMarginalSnd j
  let Q : X × X → ℝ := fun z => m z.2 * fanoNoise r z.2 z.1
  have hm := finiteMarginalSnd_isDist j hj
  have hN := fanoNoise_stochastic (X := X) r hr.le (by linarith)
  have hk : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hsmall : 0 < r / Fintype.card X := div_pos hr hk
  have hlarge : 0 < 1 - r := by linarith
  have hQ : IsDist Q := by
    refine ⟨fun z => mul_nonneg (hm.1 _) ((hN _ (Set.mem_univ _)).1 _), ?_⟩
    change (∑ z : X × X, m z.2 * fanoNoise r z.2 z.1) = 1
    rw [Fintype.sum_prod_type, sum_comm]
    simp_rw [← mul_sum, (hN _ (Set.mem_univ _)).2, mul_one]
    exact hm.2
  have hNpos (y x : X) : 0 < fanoNoise (X := X) r y x := by
    have hbase : 0 ≤ if y = x then 1 - r else 0 := by split_ifs <;> linarith
    change 0 < (if y = x then 1 - r else 0) + r * (1 / Fintype.card X)
    have hpos : 0 < r * (1 / Fintype.card X) := mul_pos hr (by positivity)
    linarith
  have hac : ∀ z, Q z = 0 → j z = 0 := by
    rintro ⟨x, y⟩ hz
    have hz' : m y = 0 := (mul_eq_zero.mp hz).resolve_right (hNpos y x).ne'
    have hx := single_le_sum (fun x' _ => hj.1 (x', y)) (mem_univ x)
    change j (x, y) ≤ m y at hx
    exact le_antisymm (hz' ▸ hx) (hj.1 _)
  have hcross := ent_le_crossEntropy j Q hj hQ hac
  have hlog (x y : X) :
      j (x,y) * Real.log (m y) +
        (if x = y then j (x,y) * Real.log (1-r) else j (x,y) * Real.log (r / Fintype.card X)) ≤
      j (x,y) * Real.log (Q (x,y)) := by
    by_cases hj0 : j (x,y) = 0
    · simp [hj0]
    · have hjp : 0 < j (x,y) := lt_of_le_of_ne (hj.1 _) (Ne.symm hj0)
      have hmp : 0 < m y := hjp.trans_le (single_le_sum (fun x' _ => hj.1 (x',y)) (mem_univ x))
      change _ ≤ j (x,y) * Real.log (m y * fanoNoise r y x)
      rw [Real.log_mul hmp.ne' (hNpos y x).ne', mul_add]
      apply add_le_add le_rfl
      split_ifs with hxy
      · subst y
        apply mul_le_mul_of_nonneg_left _ hjp.le
        apply Real.log_le_log hlarge
        change 1-r ≤ (if x=x then 1-r else 0) + r * (1 / Fintype.card X)
        simp only [if_pos rfl]
        exact le_add_of_nonneg_right (mul_nonneg hr.le (by positivity))
      · have he : fanoNoise (X := X) r y x = r / Fintype.card X := by
          simp [fanoNoise, Ne.symm hxy, uniformPrior, div_eq_mul_inv]
        rw [he]
  have hbase : (∑ x, ∑ y, j (x,y) * Real.log (m y)) = -ent m := by
    rw [sum_comm]
    simp_rw [← sum_mul]
    simp only [ent, Real.negMulLog, neg_mul, sum_neg_distrib, neg_neg]
    rfl
  have hdiag : (∑ x, j (x,x)) = 1 - finiteMismatch j := by
    rw [finiteMismatch_eq_sum_sub_diag, hj.2]; ring
  have hsplit : (∑ x, ∑ y, (if x=y then j (x,y) * Real.log (1-r)
      else j (x,y) * Real.log (r / Fintype.card X))) =
      (1-finiteMismatch j) * Real.log (1-r) + finiteMismatch j * Real.log (r / Fintype.card X) := by
    have ht (x y : X) : (if x=y then j (x,y)*Real.log (1-r) else j (x,y)*Real.log (r/Fintype.card X)) =
        (if x=y then j (x,y) else 0)*Real.log (1-r) +
        (if x=y then 0 else j (x,y))*Real.log (r/Fintype.card X) := by split_ifs <;> ring
    simp_rw [ht, sum_add_distrib, ← sum_mul]
    simp only [sum_ite_eq, mem_univ, if_true]
    rw [hdiag]
    rfl
  have hsum := sum_le_sum fun x (_ : x ∈ univ) => sum_le_sum fun y (_ : y ∈ univ) => hlog x y
  simp only [sum_add_distrib] at hsum
  rw [hbase, hsplit] at hsum
  rw [Fintype.sum_prod_type] at hcross
  have hmono : Real.log (r / Fintype.card X) ≤ Real.log (1-r) := by
    apply Real.log_le_log hsmall
    have hk1 : (1 : ℝ) ≤ Fintype.card X := by exact_mod_cast Nat.succ_le_of_lt (Fintype.card_pos (α := X))
    have : r / Fintype.card X ≤ r := div_le_self hr.le hk1
    linarith
  have hmul := mul_nonneg (sub_nonneg.mpr hmis) (sub_nonneg.mpr hmono)
  have he : -(1-r)*Real.log (1-r) - r*Real.log (r / Fintype.card X) =
      Real.binEntropy r + r * Real.log (Fintype.card X) := by
    rw [Real.log_div hr.ne' hk.ne', Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    unfold Real.negMulLog
    ring
  change ent j - ent m ≤ _
  rw [← he]
  dsimp [Q] at hsum hcross
  linarith

end
end IdExp
