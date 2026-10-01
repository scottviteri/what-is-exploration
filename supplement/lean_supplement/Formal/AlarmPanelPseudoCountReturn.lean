import Formal.AlarmPanelPseudoCountDensity
import Formal.AlarmPanelPseudoCountSupport
import Formal.AlarmPanelPseudoCountBounds

/-! The literal continuing bonus is the sum of inverse-square-root harmonic
counts, with pathwise bounds on every supported causal trace. -/
namespace IdExp.AlarmPanel.PseudoCount
noncomputable section
open Finset PseudoCountBounds

/-- The count representation of the cumulative reward. -/
def countReturn (D : List Observation) : ℝ := ∑ o : Observation, countSum (D.count o)

@[simp] theorem countReturn_nil : countReturn [] = 0 := by
  simp [countReturn, countSum_zero]

theorem countReturn_append (D : List Observation) (o : Observation) :
    countReturn (D ++ [o]) = countReturn D + densityBonus D o := by
  have he (p : Observation) : countSum ((D ++ [o]).count p) =
      countSum (D.count p) + if p = o then densityBonus D o else 0 := by
    by_cases hp : p = o
    · subst p
      simp [List.count_append, countSum_succ, densityBonus_eq]
    · have hp' : o ≠ p := Ne.symm hp
      simp [List.count_append, hp, hp']
  simp_rw [countReturn, he]
  rw [sum_add_distrib]
  simp

/-- Equality with the actual sequential density-derived bonuses at all lengths. -/
theorem densityReturn_eq_countReturn (D : List Observation) : densityReturn D = countReturn D := by
  induction D using List.reverseRecOn with
  | nil => simp
  | append_singleton D o ih => rw [densityReturn_append, countReturn_append, ih]

theorem countReturn_nonneg (D : List Observation) : 0 ≤ countReturn D := by
  exact sum_nonneg (fun _ _ => countSum_nonneg _)

theorem nonzero_count_eq (D : List Observation) :
    D.countP (fun o => decide (o ≠ 0)) = D.count 1 + D.count 2 + D.count 3 := by
  induction D with
  | nil => simp
  | cons a D ih => fin_cases a <;> simp_all [List.count_cons, List.countP_cons] <;> omega

theorem high_count_eq (D : List Observation) :
    D.countP (fun o => decide (o = 2 ∨ o = 3)) = D.count 2 + D.count 3 := by
  induction D with
  | nil => simp
  | cons a D ih => fin_cases a <;> simp_all [List.count_cons, List.countP_cons] <;> omega

theorem countReturn_four (D : List Observation) :
    countReturn D = countSum (D.count 0) + countSum (D.count 1) +
      countSum (D.count 2) + countSum (D.count 3) := by
  simp [countReturn, Fin.sum_univ_succ]
  ring

theorem count_four (D : List Observation) :
    D.count 0 + D.count 1 + D.count 2 + D.count 3 = D.length := by
  have h := FirstVisitCount.count_sum D
  norm_num [Fin.sum_univ_succ] at h
  rw [show (Fin.succ (2 : Fin 3) : Observation) = 3 from rfl] at h
  have he : (D.count 0 : ℝ) + D.count 1 + D.count 2 + D.count 3 = D.length := by
    linarith
  exact_mod_cast he

theorem countReturn_inspection_bound (D : List Observation)
    (hD : D.countP (fun o => decide (o ≠ 0)) ≤ 2) :
    countReturn D ≤ 2 * Real.sqrt D.length + 2 := by
  rw [countReturn_four]
  have h0 := (countSum_mono (List.count_le_length (a := (0 : Observation)) (l := D))).trans
    (countSum_le_two_sqrt D.length)
  have h1 := countSum_le_nat (D.count 1)
  have h2 := countSum_le_nat (D.count 2)
  have h3 := countSum_le_nat (D.count 3)
  rw [nonzero_count_eq] at hD
  have hc : (D.count 1 : ℝ) + D.count 2 + D.count 3 ≤ 2 := by exact_mod_cast hD
  linarith

theorem inspecting_densityReturn_le (π : CausalPolicy Action Observation)
    (θ : World) (t : ℕ) (w : CausalFiniteTrace Action Observation t)
    (hw : experiment (inspectBranch π) t θ w ≠ 0) :
    densityReturn (archive w) ≤ 2 * Real.sqrt t + 2 := by
  rw [densityReturn_eq_countReturn]
  simpa using countReturn_inspection_bound (archive w)
    (inspectBranch_nonzero_count_le_two π θ t w hw)

theorem high_densityReturn_ge (θ : World) (t : ℕ)
    (w : CausalFiniteTrace Action Observation t) (hw : experiment highPolicy t θ w ≠ 0) :
    countSum (t / 2) + countSum ((t - 1) / 2 - 1) ≤ densityReturn (archive w) := by
  rw [densityReturn_eq_countReturn, countReturn_four]
  have hhigh := high_count_ge θ t w hw
  rw [high_count_eq] at hhigh
  have hp := (countSum_mono hhigh).trans (countSum_add_le _ _)
  have hz := countSum_mono (zero_count_ge highPolicy θ t w hw)
  have hn := countSum_nonneg ((archive w).count 1)
  linarith

/-- Four-label count bonus is bounded by the square-root growth rate. -/
theorem countReturn_le_four_sqrt (D : List Observation) :
    countReturn D ≤ 4 * Real.sqrt D.length := by
  have hc := count_four D
  have hcr : (D.count 0 : ℝ) + D.count 1 + D.count 2 + D.count 3 = D.length := by
    exact_mod_cast hc
  have h0 := countSum_le_two_sqrt (D.count 0)
  have h1 := countSum_le_two_sqrt (D.count 1)
  have h2 := countSum_le_two_sqrt (D.count 2)
  have h3 := countSum_le_two_sqrt (D.count 3)
  have q0 := Real.sq_sqrt (show (0 : ℝ) ≤ D.count 0 by positivity)
  have q1 := Real.sq_sqrt (show (0 : ℝ) ≤ D.count 1 by positivity)
  have q2 := Real.sq_sqrt (show (0 : ℝ) ≤ D.count 2 by positivity)
  have q3 := Real.sq_sqrt (show (0 : ℝ) ≤ D.count 3 by positivity)
  have qt := Real.sq_sqrt (show (0 : ℝ) ≤ D.length by positivity)
  have hs : Real.sqrt (D.count 0) + Real.sqrt (D.count 1) +
      Real.sqrt (D.count 2) + Real.sqrt (D.count 3) ≤ 2 * Real.sqrt D.length := by
    nlinarith [sq_nonneg (Real.sqrt (D.count 0) - Real.sqrt (D.count 1)),
      sq_nonneg (Real.sqrt (D.count 0) - Real.sqrt (D.count 2)),
      sq_nonneg (Real.sqrt (D.count 0) - Real.sqrt (D.count 3)),
      sq_nonneg (Real.sqrt (D.count 1) - Real.sqrt (D.count 2)),
      sq_nonneg (Real.sqrt (D.count 1) - Real.sqrt (D.count 3)),
      sq_nonneg (Real.sqrt (D.count 2) - Real.sqrt (D.count 3)),
      Real.sqrt_nonneg (D.count 0), Real.sqrt_nonneg (D.count 1),
      Real.sqrt_nonneg (D.count 2), Real.sqrt_nonneg (D.count 3), Real.sqrt_nonneg D.length]
  rw [countReturn_four]
  linarith

/-- Every record earns at least the square root of its length. -/
theorem sqrt_le_countReturn (D : List Observation) :
    Real.sqrt D.length ≤ countReturn D := by
  have h0 := countSum_add_le (D.count 0) (D.count 1)
  have h1 := countSum_add_le (D.count 0 + D.count 1) (D.count 2)
  have h2 := countSum_add_le (D.count 0 + D.count 1 + D.count 2) (D.count 3)
  rw [count_four] at h2
  rw [countReturn_four]
  have hl := sqrt_le_countSum D.length
  linarith

/-- Distribution-free deterministic bounds for the literal density bonus. -/
theorem densityReturn_sqrt_bounds (D : List Observation) :
    Real.sqrt D.length ≤ densityReturn D ∧
      densityReturn D ≤ 2 * Real.sqrt (4 * D.length) := by
  rw [densityReturn_eq_countReturn]
  refine ⟨sqrt_le_countReturn D, ?_⟩
  have hu := countReturn_le_four_sqrt D
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num
  linarith

end
end IdExp.AlarmPanel.PseudoCount
