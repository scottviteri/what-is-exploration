import Formal.ControlChannelCapacity
import Formal.FiniteConditionalEntropy

/-! Equality in binary skill information: the maximum is attained exactly when
no signal is shared by both skills. These are ordinary finite Shannon quantities. -/
namespace IdExp
open Finset
noncomputable section
variable {X : Type*} [Fintype X]

/-- For a fair binary skill, maximal information means disjoint signal supports. -/
theorem binary_information_max_iff_disjoint
    (E : FiniteExperiment (Fin 2) X) (hE : IsFiniteExperiment E) :
    finiteBayesInformation (uniformPrior (Fin 2)) E = Real.log 2 ↔
      ∀ x, E 0 x = 0 ∨ E 1 x = 0 := by
  classical
  have hent : ent (uniformPrior (Fin 2)) = Real.log 2 := by
    simp
  have hn (x : X) : 0 ≤ finiteBayesMass (uniformPrior (Fin 2)) E x *
      ent (finiteBayesPosterior (uniformPrior (Fin 2)) E x) := by
    apply mul_nonneg
    · exact finiteBayesMass_nonneg _ _ isDist_uniformPrior.1 (fun z x => (hE z).1 x) x
    · exact sum_nonneg fun z _ => Real.negMulLog_nonneg
        (finiteBayesPosterior_nonneg _ _ isDist_uniformPrior.1 (fun z x => (hE z).1 x) x z)
        (finiteBayesPosterior_le_one _ _ isDist_uniformPrior.1 (fun z x => (hE z).1 x) x z)
  constructor
  · intro hi x
    have hz : finiteBayesPotential ent (uniformPrior (Fin 2)) E = 0 := by
      unfold finiteBayesInformation at hi
      rw [hent] at hi
      linarith
    have hx := (sum_eq_zero_iff_of_nonneg (fun x _ => hn x)).1 hz x (mem_univ x)
    by_contra hno
    push Not at hno
    have h0 : 0 < E 0 x := lt_of_le_of_ne ((hE 0).1 x) (Ne.symm hno.1)
    have h1 : 0 < E 1 x := lt_of_le_of_ne ((hE 1).1 x) (Ne.symm hno.2)
    have hm : 0 < finiteBayesMass (uniformPrior (Fin 2)) E x := by
      simp only [finiteBayesMass, Fin.sum_univ_two, uniformPrior, Fintype.card_fin,
        Nat.cast_ofNat]
      positivity
    have he : ent (finiteBayesPosterior (uniformPrior (Fin 2)) E x) = 0 :=
      (mul_eq_zero.mp hx).resolve_left hm.ne'
    have hp0 : 0 < finiteBayesPosterior (uniformPrior (Fin 2)) E x 0 := by
      simp only [finiteBayesPosterior, Fin.sum_univ_two, uniformPrior,
        Fintype.card_fin, Nat.cast_ofNat]
      positivity
    have hp1 : finiteBayesPosterior (uniformPrior (Fin 2)) E x 0 < 1 := by
      simp only [finiteBayesPosterior, Fin.sum_univ_two, uniformPrior,
        Fintype.card_fin, Nat.cast_ofNat]
      apply (div_lt_one (by positivity)).2
      linarith
    have hp : 0 < Real.negMulLog (finiteBayesPosterior (uniformPrior (Fin 2)) E x 0) := by
      rw [Real.negMulLog_eq_neg]
      exact neg_pos.mpr (Real.mul_log_neg hp0 hp1)
    have hb := finiteBayesPosterior_nonneg (uniformPrior (Fin 2)) E
      isDist_uniformPrior.1 (fun z x => (hE z).1 x) x 1
    have hc := finiteBayesPosterior_le_one (uniformPrior (Fin 2)) E
      isDist_uniformPrior.1 (fun z x => (hE z).1 x) x 1
    have hp' := Real.negMulLog_nonneg hb hc
    rw [ent, Fin.sum_univ_two] at he
    linarith
  · intro hd
    unfold finiteBayesInformation
    rw [hent]
    have hz : finiteBayesPotential ent (uniformPrior (Fin 2)) E = 0 := by
      apply sum_eq_zero
      intro x _
      rcases hd x with h0 | h1
      · by_cases h1 : E 1 x = 0
        · simp [finiteBayesMass, finiteBayesPosterior, uniformPrior,
            Fin.sum_univ_two, h0, h1, ent]
        · have hne : (2⁻¹ : ℝ) * E 1 x ≠ 0 := mul_ne_zero (by norm_num) h1
          simp [finiteBayesPosterior, uniformPrior, Fin.sum_univ_two, h0, ent, hne]
      · by_cases h0 : E 0 x = 0
        · simp [finiteBayesMass, finiteBayesPosterior, uniformPrior,
            Fin.sum_univ_two, h0, h1, ent]
        · have hne : (2⁻¹ : ℝ) * E 0 x ≠ 0 := mul_ne_zero (by norm_num) h0
          simp [finiteBayesPosterior, uniformPrior, Fin.sum_univ_two, h1, ent, hne]
    rw [hz, sub_zero]
/-- The usual kernel form of conditional action entropy, including null states. -/
theorem finiteConditionalEntropy_kernel
    {A S : Type*} [Fintype A] [Nonempty A] [Fintype S]
    (m : S → ℝ) (k : S → A → ℝ) (hk : ∀ s, IsDist (k s)) :
    finiteConditionalEntropy (fun p : A × S => m p.2 * k p.2 p.1) =
      ∑ s, m s * ent (k s) := by
  classical
  have hm (s : S) :
      finiteMarginalSnd (fun p : A × S => m p.2 * k p.2 p.1) s = m s := by
    simp only [finiteMarginalSnd, ← mul_sum, (hk s).2, mul_one]
  unfold finiteConditionalEntropy
  apply sum_congr rfl
  intro s _
  rw [hm]
  by_cases hs : m s = 0
  · simp [hs]
  · have hc : finiteConditionalLaw (fun p : A × S => m p.2 * k p.2 p.1) s = k s := by
      funext a
      simp only [finiteConditionalLaw, hm, hs, if_false]
      exact mul_div_cancel_left₀ _ hs
    rw [hc]

end
end IdExp
