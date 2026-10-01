import Formal.ControlEntropy

/-! Ordinary finite conditional entropy, including zero-mass conditioning events. -/
namespace IdExp
open Finset
noncomputable section
variable {A S : Type*} [Fintype A] [Nonempty A] [Fintype S]

def finiteConditionalLaw (j : A × S → ℝ) (s : S) (a : A) : ℝ :=
  if finiteMarginalSnd j s = 0 then uniformPrior A a
  else j (a,s) / finiteMarginalSnd j s

theorem finiteConditionalLaw_valid (j : A × S → ℝ) (hj : IsDist j) (s : S) :
    IsDist (finiteConditionalLaw j s) := by
  classical
  by_cases h : finiteMarginalSnd j s = 0
  · have he : finiteConditionalLaw j s = uniformPrior A := by
      funext a; simp [finiteConditionalLaw, h]
    rw [he]
    exact isDist_uniformPrior
  · constructor
    · intro a
      simp only [finiteConditionalLaw, h, if_false]
      exact div_nonneg (hj.1 _) ((finiteMarginalSnd_isDist j hj).1 s)
    · simp only [finiteConditionalLaw, h, if_false, ← sum_div]
      exact div_self h

/-- H(A | S), using the actual joint law of action and physical state. -/
def finiteConditionalEntropy (j : A × S → ℝ) : ℝ :=
  ∑ s, finiteMarginalSnd j s * ent (finiteConditionalLaw j s)

theorem finiteConditionalEntropy_nonneg (j : A × S → ℝ) (hj : IsDist j) :
    0 ≤ finiteConditionalEntropy j :=
  sum_nonneg fun s _ => mul_nonneg ((finiteMarginalSnd_isDist j hj).1 s)
    (ent_nonneg_of_isDist _ (finiteConditionalLaw_valid j hj s))

theorem finiteConditionalEntropy_le (j : A × S → ℝ) (hj : IsDist j) :
    finiteConditionalEntropy j ≤ Real.log (Fintype.card A) := by
  classical
  calc
    _ ≤ ∑ s, finiteMarginalSnd j s * Real.log (Fintype.card A) :=
      sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
        (ent_le_log_card _ (finiteConditionalLaw_valid j hj s))
        ((finiteMarginalSnd_isDist j hj).1 s)
    _ = _ := by rw [← sum_mul, (finiteMarginalSnd_isDist j hj).2, one_mul]

theorem finiteConditionalEntropy_uniform (m : S → ℝ) (hm : IsDist m) :
    finiteConditionalEntropy (fun p : A × S => uniformPrior A p.1 * m p.2) =
      Real.log (Fintype.card A) := by
  classical
  have hmass (s : S) :
      finiteMarginalSnd (fun p : A × S => uniformPrior A p.1 * m p.2) s = m s := by
    simp only [finiteMarginalSnd, ← sum_mul, isDist_uniformPrior.2, one_mul]
  have hcond (s : S) :
      finiteConditionalLaw (fun p : A × S => uniformPrior A p.1 * m p.2) s =
        uniformPrior A := by
    funext a
    simp only [finiteConditionalLaw, hmass]
    split_ifs with h
    · rfl
    · exact mul_div_cancel_right₀ _ h
  simp only [finiteConditionalEntropy, hmass, hcond, ent_uniformPrior, ← sum_mul,
    hm.2, one_mul]
end
end IdExp
