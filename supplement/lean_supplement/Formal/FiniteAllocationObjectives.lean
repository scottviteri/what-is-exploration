import Formal.FiniteDecoderAllocation
import Formal.FiniteBayesBregman
import Formal.DecisionDeficiencyDuality

/-!
# Posterior and decision objectives in realization coordinates

The source has entries `w x * p θ x`, with fixed controlled likelihoods `p`
and variable world-independent weights `w`. Bayes' rule cancels `w` at
nonnull signals. Every posterior potential therefore has fixed linear
coefficients, even if controlled likelihoods or acquired weights vanish.
The same factorization yields an exact linear epigraph for the *optimized*
Bayes decision value, retaining its inner optimization over randomized rules.
These algebraic facts do not require convexity of the posterior potential.
-/
namespace IdExp
open Finset
noncomputable section
set_option linter.unusedSectionVars false

section Posterior
variable {Θ X : Type*} [Fintype Θ] [Fintype X]

theorem finiteBayesMass_allocationSource (α : Θ → ℝ) (p : Θ → X → ℝ)
    (w : X → ℝ) (x : X) :
    finiteBayesMass α (allocationSource p w) x = w x * finiteBayesMass α p x := by
  unfold finiteBayesMass allocationSource
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun θ _ => by ring

/-- Cancellation needs only a nonzero realization weight, not a full-support
prior or a nonnull controlled likelihood. Null mixture masses give zero on
both sides under the library's Bayes convention. -/
theorem finiteBayesPosterior_allocationSource (α : Θ → ℝ) (p : Θ → X → ℝ)
    (w : X → ℝ) (x : X) (hw : w x ≠ 0) :
    finiteBayesPosterior α (allocationSource p w) x = finiteBayesPosterior α p x := by
  funext θ
  change (α θ * (w x * p θ x)) / finiteBayesMass α (allocationSource p w) x = _
  rw [finiteBayesMass_allocationSource]
  change (α θ * (w x * p θ x)) / (w x * finiteBayesMass α p x) =
    (α θ * p θ x) / finiteBayesMass α p x
  rw [show α θ * (w x * p θ x) = w x * (α θ * p θ x) by ring]
  exact mul_div_mul_left _ _ hw

/-- The posterior potential is linear in world-independent realization
weights. Zero-weight signals contribute zero regardless of their posterior. -/
theorem finiteBayesPotential_allocationSource (Φ : (Θ → ℝ) → ℝ)
    (α : Θ → ℝ) (p : Θ → X → ℝ) (w : X → ℝ) :
    finiteBayesPotential Φ α (allocationSource p w) =
      ∑ x, w x * finiteBayesMass α p x * Φ (finiteBayesPosterior α p x) := by
  unfold finiteBayesPotential
  apply Finset.sum_congr rfl
  intro x _
  rw [finiteBayesMass_allocationSource]
  by_cases hw : w x = 0
  · simp [hw]
  · rw [finiteBayesPosterior_allocationSource α p w x hw]

/-- Fixed coefficient of terminal posterior gain, including its baseline. -/
def allocationPosteriorCoefficient (Φ : (Θ → ℝ) → ℝ) (α : Θ → ℝ)
    (p : Θ → X → ℝ) (x : X) : ℝ :=
  finiteBayesMass α p x * (Φ (finiteBayesPosterior α p x) - Φ α)

/-- For a valid acquired experiment and prior, the terminal gain is the
linear objective used by the collector LP. The likelihood matrix `p` itself
need not be a stochastic experiment: normalization belongs to `w * p`. -/
theorem finiteBayesGain_allocationSource (Φ : (Θ → ℝ) → ℝ)
    (α : Θ → ℝ) (hα : IsDist α) (p : Θ → X → ℝ) (w : X → ℝ)
    (hE : IsFiniteExperiment (allocationSource p w)) :
    finiteBayesPotential Φ α (allocationSource p w) - Φ α =
      ∑ x, w x * allocationPosteriorCoefficient Φ α p x := by
  have hm : (∑ x, w x * finiteBayesMass α p x) = 1 := by
    simp_rw [← finiteBayesMass_allocationSource α p w]
    unfold finiteBayesMass
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, fun θ => (hE θ).2, mul_one]
    exact hα.2
  rw [finiteBayesPotential_allocationSource]
  simp only [allocationPosteriorCoefficient, mul_sub, ← mul_assoc, Finset.sum_sub_distrib,
    ← Finset.sum_mul, hm, one_mul]

end Posterior

section Decision
variable {Θ X D : Type*} [Fintype Θ] [Fintype X] [Fintype D] [Nonempty D]

/-- Fixed likelihood/payoff coefficients factor out the realization weight. -/
theorem finiteDecisionScore_allocationSource (p : Θ → X → ℝ) (w : X → ℝ)
    (α : Θ → ℝ) (u : Θ → D → ℝ) (x : X) (d : D) :
    finiteDecisionScore (allocationSource p w) α u x d =
      w x * finiteDecisionScore p α u x d := by
  unfold finiteDecisionScore allocationSource
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun θ _ => by ring

/-- Literal epigraph for optimized post-acquisition decision value. No
nonnegative slack constraint is needed; arbitrary real payoffs are allowed. -/
structure AllocationDecisionEpigraph (p : Θ → X → ℝ) (w : X → ℝ)
    (α : Θ → ℝ) (u : Θ → D → ℝ) (v : X → ℝ) : Prop where
  upper : ∀ x d, w x * finiteDecisionScore p α u x d ≤ v x

/-- Exact closed value sublevels. Minimizing the sum of epigraph variables
therefore minimizes the best available decision value, not a fixed rule's
payoff. The inner randomized-rule optimum is `finiteBayesValue_isGreatest`. -/
theorem finiteBayesValue_allocationSource_le_iff_epigraph
    (p : Θ → X → ℝ) (w : X → ℝ) (α : Θ → ℝ)
    (u : Θ → D → ℝ) (c : ℝ) :
    finiteBayesValue (allocationSource p w) α u ≤ c ↔
      ∃ v : X → ℝ, AllocationDecisionEpigraph p w α u v ∧ (∑ x, v x) ≤ c := by
  classical
  constructor
  · intro hc
    refine ⟨fun x => Finset.univ.sup' Finset.univ_nonempty
      (finiteDecisionScore (allocationSource p w) α u x), ⟨?_⟩, hc⟩
    intro x d
    rw [← finiteDecisionScore_allocationSource]
    exact Finset.le_sup' _ (Finset.mem_univ d)
  · rintro ⟨v, hv, hc⟩
    apply le_trans _ hc
    apply Finset.sum_le_sum
    intro x _
    apply Finset.sup'_le
    intro d _
    rw [finiteDecisionScore_allocationSource]
    exact hv.upper x d

end Decision
end
end IdExp
