import Formal.FiniteFanoBound

/-!
# Entropy and discounted control rewards

The entropy maximum and its equality case are shared by the physical-control
counterexamples. The tilted binary root reward is ordinary entropy after
splitting one branch into two equiprobable labels.
-/

namespace IdExp
open Finset
noncomputable section
set_option linter.unusedSectionVars false

variable {X : Type*} [Fintype X]

theorem ent_nonneg_of_isDist (p : X → ℝ) (hp : IsDist p) : 0 ≤ ent p := by
  apply sum_nonneg
  intro x _
  exact Real.negMulLog_nonneg (hp.1 x)
    ((single_le_sum (fun y _ => hp.1 y) (mem_univ x)).trans_eq hp.2)

variable [Nonempty X] [DecidableEq X]

theorem finiteKL_uniform (p : X → ℝ) (hp : IsDist p) :
    finiteKL p (uniformPrior X) = Real.log (Fintype.card X) - ent p := by
  have hn : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold finiteKL uniformPrior
  simp_rw [mul_log_div_eq _ _ (one_div_ne_zero hn), one_div, Real.log_inv]
  simp only [mul_neg, sub_neg_eq_add, sum_add_distrib, ← sum_mul, hp.2, one_mul,
    ent, Real.negMulLog, neg_mul, sum_neg_distrib]
  ring

theorem ent_le_log_card (p : X → ℝ) (hp : IsDist p) :
    ent p ≤ Real.log (Fintype.card X) := by
  have hn : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h := finiteTV_sq_le_finiteKL_half p (uniformPrior X) hp isDist_uniformPrior
    (fun x hx => False.elim ((one_div_ne_zero hn) hx))
  rw [finiteKL_uniform p hp] at h
  nlinarith [sq_nonneg (finiteTV p (uniformPrior X))]

@[simp] theorem ent_uniformPrior :
    ent (uniformPrior X) = Real.log (Fintype.card X) := by
  have hn : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [ent, uniformPrior, Real.negMulLog, one_div, Real.log_inv, hn]

theorem ent_eq_log_card_iff (p : X → ℝ) (hp : IsDist p) :
    ent p = Real.log (Fintype.card X) ↔ p = uniformPrior X := by
  constructor
  · intro heq
    have hn : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have h := finiteTV_sq_le_finiteKL_half p (uniformPrior X) hp isDist_uniformPrior
      (fun x hx => False.elim ((one_div_ne_zero hn) hx))
    rw [finiteKL_uniform p hp, heq] at h
    apply (finiteTV_eq_zero_iff p (uniformPrior X)).1
    nlinarith [finiteTV_nonneg p (uniformPrior X)]
  · rintro rfl
    exact ent_uniformPrior

/-- Binary action entropy plus the physical entropy of the second branch. -/
def splitBinaryEntropy (s : ℝ) : ℝ :=
  Real.negMulLog s + Real.negMulLog (1-s) + (1-s) * Real.log 2

/-- One revealing label and two known-noise labels. -/
def splitBinaryDist (s : ℝ) : Fin 3 → ℝ := ![s, (1-s)/2, (1-s)/2]

theorem splitBinaryDist_valid {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    IsDist (splitBinaryDist s) := by
  constructor
  · intro i; fin_cases i <;> simp [splitBinaryDist] <;> linarith
  · simp [splitBinaryDist, Fin.sum_univ_three]; ring

theorem ent_splitBinaryDist (s : ℝ) : ent (splitBinaryDist s) = splitBinaryEntropy s := by
  have hhalf : Real.negMulLog (1/2 : ℝ) = Real.log 2 / 2 := by
    simp [Real.negMulLog, one_div, Real.log_inv]; ring
  simp only [ent, Fin.sum_univ_three, splitBinaryDist, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  rw [show (1-s)/2 = (1-s)*(1/2) by ring, Real.negMulLog_mul, hhalf]
  unfold splitBinaryEntropy
  ring

theorem splitBinaryEntropy_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    splitBinaryEntropy s ≤ Real.log 3 := by
  simpa only [← ent_splitBinaryDist, Fintype.card_fin, Nat.cast_ofNat] using
    ent_le_log_card (splitBinaryDist s) (splitBinaryDist_valid hs0 hs1)

theorem splitBinaryEntropy_eq_iff {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    splitBinaryEntropy s = Real.log 3 ↔ s = 1/3 := by
  rw [← ent_splitBinaryDist]
  have h := ent_eq_log_card_iff (splitBinaryDist s) (splitBinaryDist_valid hs0 hs1)
  simp only [Fintype.card_fin, Nat.cast_ofNat] at h
  rw [h]
  constructor
  · intro heq
    exact congrFun heq 0
  · rintro rfl
    funext i
    fin_cases i <;> norm_num [splitBinaryDist, uniformPrior]

/-- A discounted nonnegative reward with a bounded tail is summable. -/
theorem summable_discounted_of_bounded {r : ℕ → ℝ} {γ B : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hr0 : ∀ t, 0 ≤ r t)
    (hrB : ∀ t, r t ≤ B) : Summable (fun t => γ^t * r t) := by
  apply Summable.of_nonneg_of_le (fun t => mul_nonneg (pow_nonneg hγ0 t) (hr0 t))
    (fun t => mul_le_mul_of_nonneg_left (hrB t) (pow_nonneg hγ0 t))
  exact (summable_geometric_of_lt_one hγ0 hγ1).mul_right B

/-- Only the first reward depends on the root choice. Every later reward is
bounded by the same physical-control ceiling. -/
theorem discounted_le_root_add_tail {r : ℕ → ℝ} {γ B : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hr0 : ∀ t, 0 ≤ r t)
    (hrB : ∀ t, r (t+1) ≤ B) :
    (∑' t, γ^t * r t) ≤ r 0 + γ * B / (1-γ) := by
  have hB0 : 0 ≤ B := (hr0 1).trans (hrB 0)
  have hsum := summable_discounted_of_bounded hγ0 hγ1 hr0
    (B := max (r 0) B) (fun t => by
      cases t with
      | zero => exact le_max_left _ _
      | succ t => exact (hrB t).trans (le_max_right _ _))
  rw [hsum.tsum_eq_zero_add]
  simp only [pow_zero, one_mul]
  apply add_le_add le_rfl
  calc
    (∑' t, γ^(t+1) * r (t+1)) ≤ ∑' t, γ^(t+1) * B := by
      apply Summable.tsum_le_tsum
        (fun t => mul_le_mul_of_nonneg_left (hrB t) (pow_nonneg hγ0 _))
        (hsum.comp_injective (fun a b h => Nat.add_right_cancel h))
      simpa only [pow_succ, mul_assoc] using
        (summable_geometric_of_lt_one hγ0 hγ1).mul_right (γ*B)
    _ = γ * B / (1-γ) := by
      simp only [pow_succ, mul_assoc, tsum_mul_right,
        tsum_geometric_of_lt_one hγ0 hγ1]
      ring

end
end IdExp
