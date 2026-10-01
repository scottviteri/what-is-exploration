import Formal.AlarmPanelFinitePseudoCount

/-! The continuing add-one categorical pseudo-count reward, evaluated on the
actual before/after density model at every observation, not just two steps. -/
namespace IdExp.AlarmPanel.PseudoCount
noncomputable section
open Finset

/-- The density-derived pseudo-count equals the previous occurrence count plus one. -/
theorem categoricalPseudoCount_eq (D : List Observation) (o : Observation) :
    categoricalPseudoCount D o = (D.count o : ℝ) + 1 := by
  have hcount : (D.count o : ℝ) ≤ D.length := by
    exact_mod_cast (List.count_le_length (a := o) (l := D))
  have hd : (D.length : ℝ) + 4 ≠ 0 := by positivity
  have he : (D.length : ℝ) + 5 ≠ 0 := by positivity
  have hn : (D.length : ℝ) + 3 - D.count o ≠ 0 := by linarith
  change FirstVisitCount.modelPseudoCount D o = _
  unfold FirstVisitCount.modelPseudoCount FirstVisitCount.updatedCountDensity
    FirstVisitCount.countDensity
  simp only [List.count_append, List.count_singleton, beq_self_eq_true, if_true,
    List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
  have hdiff : ((D.count o : ℝ) + 1 + 1) / ((D.length : ℝ) + 1 + 4) -
      ((D.count o : ℝ) + 1) / ((D.length : ℝ) + 4) =
      ((D.length : ℝ) + 3 - D.count o) / (((D.length : ℝ) + 5) * ((D.length : ℝ) + 4)) := by
    field_simp
    <;> ring
  rw [hdiff]
  field_simp
  <;> ring

/-- The literal bonus from the before/after categorical density. -/
def densityBonus (D : List Observation) (o : Observation) : ℝ :=
  1 / Real.sqrt (categoricalPseudoCount D o)

theorem densityBonus_eq (D : List Observation) (o : Observation) :
    densityBonus D o = 1 / Real.sqrt ((D.count o : ℝ) + 1) := by
  rw [densityBonus, categoricalPseudoCount_eq]

/-- Actual cumulative bonuses, using the archive strictly preceding each observation.
The default label is unreachable because all summation indices are below length. -/
def densityReturn (D : List Observation) : ℝ :=
  ∑ i ∈ range D.length, densityBonus (D.take i) (D[i]?.getD 0)

@[simp] theorem densityReturn_nil : densityReturn [] = 0 := by simp [densityReturn]

theorem densityReturn_append (D : List Observation) (o : Observation) :
    densityReturn (D ++ [o]) = densityReturn D + densityBonus D o := by
  unfold densityReturn
  simp only [List.length_append, List.length_singleton]
  rw [sum_range_succ]
  have hs : (∑ i ∈ range D.length,
      densityBonus ((D ++ [o]).take i) ((D ++ [o])[i]?.getD 0)) =
      ∑ i ∈ range D.length, densityBonus (D.take i) (D[i]?.getD 0) := by
    apply sum_congr rfl
    intro i hi
    have hi' := mem_range.mp hi
    rw [List.take_append_of_le_length (by omega), List.getElem?_append_left hi']
  rw [hs]
  congr 1
  simp

end
end IdExp.AlarmPanel.PseudoCount
