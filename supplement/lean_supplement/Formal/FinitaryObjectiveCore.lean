import Formal.NativeProcess
import Formal.WeightedObjectives

/-!
# Strictly finitary objectives from a representing family of losses

Two order-theoretic pieces of the paper's Section 4.3, independent of how the
representing family is constructed.

* If a countable family of `[0,1]`-valued losses `ℓ_j` represents the finitary
  order, in the sense that `π` finitarily dominates `σ` iff `ℓ_j π ≤ ℓ_j σ` for
  every `j`, then for positive summable weights the objective
  `1 − Σ_j w_j ℓ_j` is bounded and **strictly finitarily monotone**.
* For any strictly finitarily monotone objective, when some process is
  finitarily greatest, the maximizers are exactly the finitarily greatest
  processes.

The analytic part of the paper's theorem, that such a representing family of
randomized native prefixes exists for every class, is not proved here.
-/

namespace IdExp

section Abstract

variable {P X : Type*} (K : P → ℕ → X) (δ : X → X → ℝ)

/-- A countable family of losses represents the finitary order. -/
def RepresentsFinitaryOrder (ℓ : ℕ → P → ℝ) : Prop :=
  ∀ π σ, FinitaryDominates K δ π σ ↔ ∀ j, ℓ j π ≤ ℓ j σ

/-- A strictly finitarily monotone objective. -/
structure IsStrictlyFinitaryMonotone (J : P → ℝ) : Prop where
  mono : ∀ π σ, FinitaryDominates K δ π σ → J σ ≤ J π
  strict : ∀ π σ, FinitaryDominates K δ π σ → ¬ FinitaryDominates K δ σ π → J σ < J π

/-- The weighted eventual-loss objective. -/
noncomputable def weightedLossObjective (w : ℕ → ℝ) (ℓ : ℕ → P → ℝ) (π : P) : ℝ :=
  1 - ∑' j, w j * ℓ j π

variable {K δ}

theorem summable_weighted_loss {w : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j) (hsum : Summable w)
    {ℓ : ℕ → P → ℝ} (hℓ : ∀ j π, 0 ≤ ℓ j π ∧ ℓ j π ≤ 1) (π : P) :
    Summable fun j => w j * ℓ j π := summable_weightedScore_loss hw hsum hℓ π

/-- The objective takes values in `[0, 1]` when the weights sum to one. -/
theorem weightedLossObjective_mem_Icc {w : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j) (hsum : Summable w)
    (hone : ∑' j, w j = 1) {ℓ : ℕ → P → ℝ} (hℓ : ∀ j π, 0 ≤ ℓ j π ∧ ℓ j π ≤ 1) (π : P) :
    weightedLossObjective w ℓ π ∈ Set.Icc (0 : ℝ) 1 := weightedScore_mem_Icc hw hsum hone hℓ π

/-- **A representing family gives a strictly finitarily monotone objective.** -/
theorem weightedLossObjective_strictlyFinitaryMonotone {w : ℕ → ℝ} (hw : ∀ j, 0 < w j)
    (hsum : Summable w) {ℓ : ℕ → P → ℝ} (hℓ : ∀ j π, 0 ≤ ℓ j π ∧ ℓ j π ≤ 1)
    (hrep : RepresentsFinitaryOrder K δ ℓ) :
    IsStrictlyFinitaryMonotone K δ (weightedLossObjective w ℓ) := by
  refine ⟨fun π σ hdom => ?_, fun π σ hdom hnot => ?_⟩
  · exact weightedScore_le_of_loss_le (fun j => (hw j).le) hsum hℓ ((hrep π σ).1 hdom)
  · exact weightedScore_lt_of_representation hw hsum hℓ hrep hdom hnot

/-- **Maximizers of a strictly finitary objective are the greatest processes.**
When some process is finitarily greatest, a process maximizes any strictly
finitarily monotone objective iff it is itself finitarily greatest. -/
theorem strictlyFinitary_maximizer_iff_greatest
    (htri : ∀ x y z, δ x z ≤ δ x y + δ y z) {J : P → ℝ}
    (hJ : IsStrictlyFinitaryMonotone K δ J) {π : P} (hgreat : FinitarilyGreatest K δ π) (σ : P) :
    (∀ ρ, J ρ ≤ J σ) ↔ FinitarilyGreatest K δ σ := by
  constructor
  · intro hmax
    have hσπ : FinitaryDominates K δ σ π := by
      by_contra hnot
      exact absurd (hmax π) (not_le.2 (hJ.strict π σ (hgreat σ) hnot))
    intro ρ
    exact finitaryDominates_trans K δ htri hσπ (hgreat ρ)
  · intro hσ ρ
    exact hJ.mono σ ρ (hσ ρ)

end Abstract

end IdExp
