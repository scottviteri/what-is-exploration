import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic

/-!
# Weighted objectives from bounded losses

The series argument is independent of the index type, the process semantics,
and the construction of the losses. A representing family supplies strictness;
nonnegative weights alone suffice for ordinary monotonicity.
-/

namespace IdExp

variable {ι P : Type*}

/-- One minus the weighted sum of a family of losses. -/
noncomputable def weightedScore (w : ι → ℝ) (ℓ : ι → P → ℝ) (π : P) : ℝ :=
  1 - ∑' j, w j * ℓ j π

theorem summable_weightedScore_loss {w : ι → ℝ} (hw : ∀ j, 0 ≤ w j) (hsum : Summable w)
    {ℓ : ι → P → ℝ} (hℓ : ∀ j π, 0 ≤ ℓ j π ∧ ℓ j π ≤ 1) (π : P) :
    Summable fun j => w j * ℓ j π :=
  Summable.of_nonneg_of_le (fun j => mul_nonneg (hw j) (hℓ j π).1)
    (fun j => mul_le_of_le_one_right (hw j) (hℓ j π).2) hsum

theorem weightedScore_mem_Icc {w : ι → ℝ} (hw : ∀ j, 0 ≤ w j) (hsum : Summable w)
    (hone : ∑' j, w j = 1) {ℓ : ι → P → ℝ}
    (hℓ : ∀ j π, 0 ≤ ℓ j π ∧ ℓ j π ≤ 1) (π : P) :
    weightedScore w ℓ π ∈ Set.Icc (0 : ℝ) 1 := by
  unfold weightedScore
  have hs := summable_weightedScore_loss hw hsum hℓ π
  constructor
  · have : ∑' j, w j * ℓ j π ≤ ∑' j, w j :=
      hs.tsum_le_tsum (fun j => mul_le_of_le_one_right (hw j) (hℓ j π).2) hsum
    linarith
  · have : 0 ≤ ∑' j, w j * ℓ j π := tsum_nonneg fun j => mul_nonneg (hw j) (hℓ j π).1
    linarith

theorem weightedScore_le_of_loss_le {w : ι → ℝ} (hw : ∀ j, 0 ≤ w j)
    (hsum : Summable w) {ℓ : ι → P → ℝ}
    (hℓ : ∀ j π, 0 ≤ ℓ j π ∧ ℓ j π ≤ 1) {π σ : P}
    (hle : ∀ j, ℓ j π ≤ ℓ j σ) : weightedScore w ℓ σ ≤ weightedScore w ℓ π := by
  unfold weightedScore
  have := (summable_weightedScore_loss hw hsum hℓ π).tsum_le_tsum
    (fun j => mul_le_mul_of_nonneg_left (hle j) (hw j))
    (summable_weightedScore_loss hw hsum hℓ σ)
  linarith

theorem weightedScore_lt_of_loss_lt {w : ι → ℝ} (hw : ∀ j, 0 < w j)
    (hsum : Summable w) {ℓ : ι → P → ℝ}
    (hℓ : ∀ j π, 0 ≤ ℓ j π ∧ ℓ j π ≤ 1) {π σ : P}
    (hle : ∀ j, ℓ j π ≤ ℓ j σ) (hlt : ∃ j, ℓ j π < ℓ j σ) :
    weightedScore w ℓ σ < weightedScore w ℓ π := by
  obtain ⟨j, hj⟩ := hlt
  have hw' : ∀ j, 0 ≤ w j := fun j => (hw j).le
  unfold weightedScore
  have := (summable_weightedScore_loss hw' hsum hℓ π).tsum_lt_tsum
    (fun j => mul_le_mul_of_nonneg_left (hle j) (hw' j))
    (mul_lt_mul_of_pos_left hj (hw j))
    (summable_weightedScore_loss hw' hsum hℓ σ)
  linarith

/-- A family representing any relation strictly rewards its strict comparisons. -/
theorem weightedScore_lt_of_representation {R : P → P → Prop}
    {w : ι → ℝ} (hw : ∀ j, 0 < w j) (hsum : Summable w) {ℓ : ι → P → ℝ}
    (hℓ : ∀ j π, 0 ≤ ℓ j π ∧ ℓ j π ≤ 1)
    (hrep : ∀ π σ, R π σ ↔ ∀ j, ℓ j π ≤ ℓ j σ)
    {π σ : P} (hdom : R π σ) (hnot : ¬ R σ π) :
    weightedScore w ℓ σ < weightedScore w ℓ π := by
  apply weightedScore_lt_of_loss_lt hw hsum hℓ ((hrep π σ).1 hdom)
  have hne : ¬ ∀ j, ℓ j σ ≤ ℓ j π := fun hall => hnot ((hrep σ π).2 hall)
  push Not at hne
  exact hne

end IdExp
