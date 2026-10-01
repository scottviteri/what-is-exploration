import Formal.WeightedObjectives
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Regularity of weighted objectives from bounded losses

Summable nonnegative weights give continuous finite-stage scores, passage of
pointwise stage limits through the series, and lower semicontinuity when the
losses decrease with the stage. No density or order representation is needed
for these analytic facts, and the weights need not sum to one.
-/

namespace IdExp

open Filter Topology

variable {ι P : Type*}

theorem norm_weighted_unit_loss_le {w l : ℝ} (hw : 0 ≤ w)
    (hl : 0 ≤ l ∧ l ≤ 1) : ‖w * l‖ ≤ w := by
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw hl.1)]
  exact mul_le_of_le_one_right hw hl.2

theorem continuous_weightedScore [TopologicalSpace P] {w : ι → ℝ}
    (hw : ∀ j, 0 ≤ w j) (hsum : Summable w) {ℓ : ι → P → ℝ}
    (hℓ : ∀ j π, 0 ≤ ℓ j π ∧ ℓ j π ≤ 1)
    (hcont : ∀ j, Continuous (ℓ j)) : Continuous (weightedScore w ℓ) := by
  exact continuous_const.sub (continuous_tsum
    (fun j => continuous_const.mul (hcont j)) hsum
    (fun j π => norm_weighted_unit_loss_le (hw j) (hℓ j π)))

theorem tendsto_weightedScore {w : ι → ℝ} (hw : ∀ j, 0 ≤ w j)
    (hsum : Summable w) {ℓ : ℕ → ι → P → ℝ} {ℓlim : ι → P → ℝ}
    (hℓ : ∀ t j π, 0 ≤ ℓ t j π ∧ ℓ t j π ≤ 1)
    (hlim : ∀ j π, Tendsto (fun t => ℓ t j π) atTop (𝓝 (ℓlim j π))) (π : P) :
    Tendsto (fun t => weightedScore w (ℓ t) π) atTop (𝓝 (weightedScore w ℓlim π)) := by
  exact tendsto_const_nhds.sub (tendsto_tsum_of_dominated_convergence hsum
    (fun j => tendsto_const_nhds.mul (hlim j π))
    (Eventually.of_forall fun t j => norm_weighted_unit_loss_le (hw j) (hℓ t j π)))

theorem monotone_weightedScore_of_antitone {w : ι → ℝ} (hw : ∀ j, 0 ≤ w j)
    (hsum : Summable w) {ℓ : ℕ → ι → P → ℝ}
    (hℓ : ∀ t j π, 0 ≤ ℓ t j π ∧ ℓ t j π ≤ 1)
    (hanti : ∀ j π, Antitone (fun t => ℓ t j π)) (π : P) :
    Monotone (fun t => weightedScore w (ℓ t) π) := by
  intro s t hst
  exact weightedScore_le_of_loss_le hw hsum (ℓ := fun j n => ℓ n j π)
    (fun j n => hℓ n j π) (fun j => hanti j π hst)

theorem weightedScore_eq_iSup {w : ι → ℝ} (hw : ∀ j, 0 ≤ w j)
    (hsum : Summable w) {ℓ : ℕ → ι → P → ℝ} {ℓlim : ι → P → ℝ}
    (hℓ : ∀ t j π, 0 ≤ ℓ t j π ∧ ℓ t j π ≤ 1)
    (hanti : ∀ j π, Antitone (fun t => ℓ t j π))
    (hlim : ∀ j π, Tendsto (fun t => ℓ t j π) atTop (𝓝 (ℓlim j π))) (π : P) :
    weightedScore w ℓlim π = ⨆ t, weightedScore w (ℓ t) π :=
  (isLUB_of_tendsto_atTop (monotone_weightedScore_of_antitone hw hsum hℓ hanti π)
    (tendsto_weightedScore hw hsum hℓ hlim π)).ciSup_eq.symm

theorem lowerSemicontinuous_weightedScore [TopologicalSpace P] {w : ι → ℝ}
    (hw : ∀ j, 0 ≤ w j) (hsum : Summable w)
    {ℓ : ℕ → ι → P → ℝ} {ℓlim : ι → P → ℝ}
    (hℓ : ∀ t j π, 0 ≤ ℓ t j π ∧ ℓ t j π ≤ 1)
    (hcont : ∀ t j, Continuous (ℓ t j))
    (hanti : ∀ j π, Antitone (fun t => ℓ t j π))
    (hlim : ∀ j π, Tendsto (fun t => ℓ t j π) atTop (𝓝 (ℓlim j π))) :
    LowerSemicontinuous (weightedScore w ℓlim) := by
  have heq : weightedScore w ℓlim = fun π => ⨆ t, weightedScore w (ℓ t) π :=
    funext (weightedScore_eq_iSup hw hsum hℓ hanti hlim)
  rw [heq]
  apply lowerSemicontinuous_ciSup
  · intro π
    refine ⟨1, ?_⟩
    rintro _ ⟨t, rfl⟩
    unfold weightedScore
    have hn : 0 ≤ ∑' j, w j * ℓ t j π :=
      tsum_nonneg fun j => mul_nonneg (hw j) (hℓ t j π).1
    linarith
  · intro t
    exact (continuous_weightedScore hw hsum (hℓ t) (hcont t)).lowerSemicontinuous

end IdExp
