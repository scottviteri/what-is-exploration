import Formal.PairedAlarm

/-!
# The categorical density model behind the simultaneous-interface pseudo-count

The raw observation labels of the simultaneous alarm interface are the eight
pairs in `Fin 4 × Fin 2` (display label, monitor bit). The categorical model
assigns one adjustable count to each of the eight labels, with initial count
one. Before and after one further occurrence of `o` in a length-`t` archive it
assigns
`ρ_D(o) = (N_D(o)+1)/(t+8)` and `ρ'_D(o) = (N_D(o)+2)/(t+9)`.
The density-update recoding of Bellemare et al. (2016, Equations (1)--(2)),
`ρ(1-ρ')/(ρ'-ρ)`, is evaluated on that actual before/after model; it equals
`N_D(o)+1`. The bonus `1/√(pseudo-count)` is paid before updating, at every
observation including startup. No count bonus is assumed separately.
-/

namespace IdExp.PairedAlarm.PseudoCount
noncomputable section
open Finset

/-- The scored alphabet has exactly eight raw labels. -/
theorem card_observation : Fintype.card Observation = 8 := by decide

/-- `ρ_D(o) = (number of previous `o` + 1) / (archive length + 8)`. -/
def categoricalDensity (D : List Observation) (o : Observation) : ℝ :=
  ((D.count o : ℝ) + 1) / (D.length + 8)

/-- The occurrence counts of the eight labels sum to the archive length. -/
theorem count_sum (D : List Observation) :
    (∑ o : Observation, (D.count o : ℝ)) = D.length := by
  induction D with
  | nil => simp
  | cons a D ih =>
    simp only [List.count_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    simp only [Finset.sum_add_distrib, ih]
    simp

/-- The add-one categorical model is a probability vector over the eight labels. -/
theorem categoricalDensity_valid (D : List Observation) : IsDist (categoricalDensity D) := by
  constructor
  · intro o
    unfold categoricalDensity
    positivity
  · have hd : (D.length : ℝ) + 8 ≠ 0 := by positivity
    simp only [categoricalDensity, ← Finset.sum_div, Finset.sum_add_distrib, count_sum]
    simp only [Finset.sum_const, Finset.card_univ, card_observation, nsmul_eq_mul]
    rw [div_eq_one_iff_eq hd]
    push_cast
    ring

/-- `ρ'_D(o)`: the same model after one further occurrence of `o`. -/
def updatedCategoricalDensity (D : List Observation) (o : Observation) : ℝ :=
  categoricalDensity (D ++ [o]) o

/-- Bellemare et al.'s recoding `ρ(1-ρ')/(ρ'-ρ)`, not an assumed count bonus. -/
def categoricalPseudoCount (D : List Observation) (o : Observation) : ℝ :=
  categoricalDensity D o * (1 - updatedCategoricalDensity D o) /
    (updatedCategoricalDensity D o - categoricalDensity D o)

/-- The density-derived pseudo-count of the eight-label model is the previous
occurrence count plus one. -/
theorem categoricalPseudoCount_eq (D : List Observation) (o : Observation) :
    categoricalPseudoCount D o = (D.count o : ℝ) + 1 := by
  have hcount : (D.count o : ℝ) ≤ D.length := by
    exact_mod_cast (List.count_le_length (a := o) (l := D))
  have hd : (D.length : ℝ) + 8 ≠ 0 := by positivity
  have he : (D.length : ℝ) + 9 ≠ 0 := by positivity
  have hn : (D.length : ℝ) + 7 - D.count o ≠ 0 := by linarith
  unfold categoricalPseudoCount updatedCategoricalDensity categoricalDensity
  simp only [List.count_append, List.count_singleton, beq_self_eq_true, if_true,
    List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
  have hdiff : ((D.count o : ℝ) + 1 + 1) / ((D.length : ℝ) + 1 + 8) -
      ((D.count o : ℝ) + 1) / ((D.length : ℝ) + 8) =
      ((D.length : ℝ) + 7 - D.count o) / (((D.length : ℝ) + 9) * ((D.length : ℝ) + 8)) := by
    field_simp
    ring
  rw [hdiff]
  field_simp
  ring

theorem categoricalPseudoCount_empty (o : Observation) : categoricalPseudoCount [] o = 1 := by
  rw [categoricalPseudoCount_eq]; simp

/-- The literal bonus `1/√(pseudo-count)` from the before/after categorical density. -/
def densityBonus (D : List Observation) (o : Observation) : ℝ :=
  1 / Real.sqrt (categoricalPseudoCount D o)

theorem densityBonus_eq (D : List Observation) (o : Observation) :
    densityBonus D o = 1 / Real.sqrt ((D.count o : ℝ) + 1) := by
  rw [densityBonus, categoricalPseudoCount_eq]

/-- Actual cumulative bonuses: each observation, including startup, is scored
against the archive strictly preceding it, before the model is updated. The
default label is unreachable because every summation index is below the length. -/
def densityReturn (D : List Observation) : ℝ :=
  ∑ i ∈ range D.length, densityBonus (D.take i) (D[i]?.getD (0, 0))

@[simp] theorem densityReturn_nil : densityReturn [] = 0 := by simp [densityReturn]

theorem densityReturn_append (D : List Observation) (o : Observation) :
    densityReturn (D ++ [o]) = densityReturn D + densityBonus D o := by
  unfold densityReturn
  simp only [List.length_append, List.length_singleton]
  rw [sum_range_succ]
  have hs : (∑ i ∈ range D.length,
      densityBonus ((D ++ [o]).take i) ((D ++ [o])[i]?.getD (0, 0))) =
      ∑ i ∈ range D.length, densityBonus (D.take i) (D[i]?.getD (0, 0)) := by
    apply sum_congr rfl
    intro i hi
    have hi' := mem_range.mp hi
    rw [List.take_append_of_le_length (by omega), List.getElem?_append_left hi']
  rw [hs]
  congr 1
  simp

end
end IdExp.PairedAlarm.PseudoCount
