import Formal.PairedAlarmPseudoCountDensity
import Formal.PairedAlarmPseudoCountSupport
import Formal.PairedAlarmPseudoCountBounds

/-!
# The continuing eight-label count bonus as a sum of square-root harmonic counts

The literal cumulative density bonus on a length-`H` archive equals
`R_H = Σ_o S(N_H(o))`, the sum running over all eight raw labels of
`Fin 4 × Fin 2`. Pathwise consequences on supported records:

* inspection branch: `R_H ≤ S(H) + 2 ≤ 2√H + 2`;
* alternating-play witness: `R_H ≥ S(⌊H/2⌋-1) + S(⌊(H-1)/2⌋-1)`;
* every record: `√H ≤ R_H ≤ 2√(8H)`.
-/

namespace IdExp.PairedAlarm.PseudoCount
noncomputable section
open Finset IdExp.AlarmPanel.PseudoCountBounds

/-- The count representation of the cumulative reward, over all eight labels. -/
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
theorem densityReturn_eq_countReturn (D : List Observation) :
    densityReturn D = countReturn D := by
  induction D using List.reverseRecOn with
  | nil => simp
  | append_singleton D o ih => rw [densityReturn_append, countReturn_append, ih]

theorem countReturn_nonneg (D : List Observation) : 0 ≤ countReturn D :=
  sum_nonneg (fun _ _ => countSum_nonneg _)

/-- Counts restricted to a set of labels form a `countP`. -/
theorem sum_count_eq_countP (s : Finset Observation) (D : List Observation) :
    (∑ o ∈ s, D.count o) = D.countP (fun x => decide (x ∈ s)) := by
  induction D with
  | nil => simp
  | cons a D ih =>
    simp only [List.count_cons, List.countP_cons, Finset.sum_add_distrib, ih, beq_iff_eq]
    congr 1
    rw [Finset.sum_ite_eq]
    simp

/-- The occurrence counts of the eight labels sum to the archive length. -/
theorem sum_count_eq_length (D : List Observation) :
    (∑ o : Observation, D.count o) = D.length := by
  have h := count_sum D
  exact_mod_cast h

/-- The eight summands, grouped by monitor bit. -/
theorem countReturn_eight (D : List Observation) :
    countReturn D =
      (countSum (D.count (0, 0)) + countSum (D.count (1, 0)) +
        countSum (D.count (2, 0)) + countSum (D.count (3, 0))) +
      (countSum (D.count (0, 1)) + countSum (D.count (1, 1)) +
        countSum (D.count (2, 1)) + countSum (D.count (3, 1))) := by
  simp only [countReturn, Fintype.sum_prod_type, Fin.sum_univ_four, Fin.sum_univ_two]
  ring

/-! ## The inspection-branch ceiling -/

theorem countReturn_inspection_bound (D : List Observation)
    (hD : D.countP (fun o => decide (o ≠ (0, 0))) ≤ 2) :
    countReturn D ≤ 2 * Real.sqrt D.length + 2 := by
  unfold countReturn
  rw [← Finset.add_sum_erase univ _ (mem_univ ((0, 0) : Observation))]
  have h0 := (countSum_mono (List.count_le_length (a := ((0, 0) : Observation)) (l := D))).trans
    (countSum_le_two_sqrt D.length)
  have hrest : ∑ o ∈ univ.erase ((0, 0) : Observation), countSum (D.count o) ≤
      ∑ o ∈ univ.erase ((0, 0) : Observation), (D.count o : ℝ) :=
    sum_le_sum (fun o _ => countSum_le_nat _)
  have hcount : (∑ o ∈ univ.erase ((0, 0) : Observation), D.count o) =
      D.countP (fun o => decide (o ≠ (0, 0))) := by
    rw [sum_count_eq_countP]
    apply List.countP_congr
    intro x _
    simp
  have hc : (∑ o ∈ univ.erase ((0, 0) : Observation), (D.count o : ℝ)) ≤ 2 := by
    have hn : (∑ o ∈ univ.erase ((0, 0) : Observation), D.count o) ≤ 2 := hcount ▸ hD
    exact_mod_cast hn
  linarith

theorem inspecting_densityReturn_le (π : CausalPolicy Action Observation)
    (θ : World) (t : ℕ) (w : CausalFiniteTrace Action Observation t)
    (hw : experiment (inspectBranch π) t θ w ≠ 0) :
    densityReturn (archive w) ≤ 2 * Real.sqrt t + 2 := by
  rw [densityReturn_eq_countReturn]
  simpa using countReturn_inspection_bound (archive w)
    (inspectBranch_offCount_le_two π θ t w hw)

/-! ## The alternating-play floor -/

theorem low_count_eq (D : List Observation) :
    D.countP (fun o => decide (o = (0, 0) ∨ o = (1, 0))) = D.count (0, 0) + D.count (1, 0) := by
  have h := sum_count_eq_countP {(0, 0), (1, 0)} D
  rw [Finset.sum_pair (by decide)] at h
  rw [h]
  apply List.countP_congr
  intro x _
  simp

theorem high_count_eq (D : List Observation) :
    D.countP (fun o => decide (o = (2, 0) ∨ o = (3, 0))) = D.count (2, 0) + D.count (3, 0) := by
  have h := sum_count_eq_countP {(2, 0), (3, 0)} D
  rw [Finset.sum_pair (by decide)] at h
  rw [h]
  apply List.countP_congr
  intro x _
  simp

/-- Guaranteed low and high monitor-zero counts give the witness floor. -/
theorem countReturn_witness_lower (D : List Observation) (a b : ℕ)
    (ha : a ≤ D.countP (fun o => decide (o = (0, 0) ∨ o = (1, 0))))
    (hb : b ≤ D.countP (fun o => decide (o = (2, 0) ∨ o = (3, 0)))) :
    countSum a + countSum b ≤ countReturn D := by
  rw [low_count_eq] at ha
  rw [high_count_eq] at hb
  have hla := (countSum_mono ha).trans (countSum_add_le _ _)
  have hlb := (countSum_mono hb).trans (countSum_add_le _ _)
  rw [countReturn_eight]
  have n1 := countSum_nonneg (D.count (0, 1))
  have n2 := countSum_nonneg (D.count (1, 1))
  have n3 := countSum_nonneg (D.count (2, 1))
  have n4 := countSum_nonneg (D.count (3, 1))
  linarith

theorem alt_densityReturn_ge (θ : World) (t : ℕ)
    (w : CausalFiniteTrace Action Observation t) (hw : experiment altPolicy t θ w ≠ 0) :
    countSum (t / 2 - 1) + countSum ((t - 1) / 2 - 1) ≤ densityReturn (archive w) := by
  rw [densityReturn_eq_countReturn]
  exact countReturn_witness_lower (archive w) _ _
    (alt_low_count_ge θ t w hw) (alt_high_count_ge θ t w hw)

/-! ## Distribution-free square-root envelope -/

theorem countSum_sum_le {ι : Type*} (s : Finset ι) (n : ι → ℕ) :
    countSum (∑ i ∈ s, n i) ≤ ∑ i ∈ s, countSum (n i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (countSum_add_le _ _).trans (add_le_add le_rfl ih)

/-- Every record earns at least the square root of its length. -/
theorem sqrt_le_countReturn (D : List Observation) :
    Real.sqrt D.length ≤ countReturn D := by
  have h := countSum_sum_le (univ : Finset Observation) (fun o => D.count o)
  rw [sum_count_eq_length] at h
  exact (sqrt_le_countSum D.length).trans h

/-- Eight-label square-root ceiling, by Cauchy--Schwarz. -/
theorem countReturn_le_two_sqrt_eight (D : List Observation) :
    countReturn D ≤ 2 * Real.sqrt (8 * D.length) := by
  have hterm : countReturn D ≤ ∑ o : Observation, 2 * Real.sqrt (D.count o) :=
    sum_le_sum (fun o _ => countSum_le_two_sqrt _)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset Observation)
    (fun _ => (1 : ℝ)) (fun o => Real.sqrt (D.count o))
  have hsq : (∑ o : Observation, Real.sqrt (D.count o) ^ 2) = D.length := by
    rw [← count_sum D]
    apply sum_congr rfl
    intro o _
    exact Real.sq_sqrt (Nat.cast_nonneg _)
  have hone : (∑ _o : Observation, (1 : ℝ) ^ 2) = 8 := by
    simp
  simp only [one_mul] at hcs
  rw [hsq, hone] at hcs
  have hs : (∑ o : Observation, Real.sqrt (D.count o)) ≤ Real.sqrt (8 * D.length) :=
    (le_abs_self _).trans (Real.abs_le_sqrt hcs)
  rw [← mul_sum] at hterm
  linarith

/-- Distribution-free deterministic bounds for the literal density bonus. -/
theorem densityReturn_sqrt_bounds (D : List Observation) :
    Real.sqrt D.length ≤ densityReturn D ∧
      densityReturn D ≤ 2 * Real.sqrt (8 * D.length) := by
  rw [densityReturn_eq_countReturn]
  exact ⟨sqrt_le_countReturn D, countReturn_le_two_sqrt_eight D⟩

end
end IdExp.PairedAlarm.PseudoCount
