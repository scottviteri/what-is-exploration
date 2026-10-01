import Mathlib

namespace IdExp.IntrinsicRewardComparison

/-- With a common maximizer and strictly positive finite world weights,
maximizing their weighted sum is equivalent to maximizing every component.
The policy domain is arbitrary; all objective values are finite reals.
Weights need not sum to one because positive normalization does not affect argmax. -/
theorem weighted_maximizer_iff_common
    {World Policy : Type*} [Fintype World]
    (weight : World → ℝ) (hweight : ∀ w, 0 < weight w)
    (value : World → Policy → ℝ) (common : Policy)
    (hcommon : ∀ w p, value w p ≤ value w common)
    (candidate : Policy) :
    (∀ p, (∑ w, weight w * value w p) ≤
      ∑ w, weight w * value w candidate) ↔
    ∀ w p, value w p ≤ value w candidate := by
  classical
  constructor
  · intro hmax w p
    have heq : value w candidate = value w common := by
      by_contra hne
      have hstrict : value w candidate < value w common :=
        lt_of_le_of_ne (hcommon w candidate) hne
      have hsum : (∑ v, weight v * value v candidate) <
          ∑ v, weight v * value v common := by
        exact Finset.sum_lt_sum
          (fun v _ => mul_le_mul_of_nonneg_left (hcommon v candidate) (hweight v).le)
          ⟨w, Finset.mem_univ w, mul_lt_mul_of_pos_left hstrict (hweight w)⟩
      exact (not_lt_of_ge (hmax common)) hsum
    rw [heq]
    exact hcommon w p
  · intro hcommonCandidate p
    exact Finset.sum_le_sum fun w _ =>
      mul_le_mul_of_nonneg_left (hcommonCandidate w p) (hweight w).le

/-- The literal infimum over worlds, applied after computing each world score.
The finite-world results below impose nonemptiness explicitly. -/
noncomputable def worstCaseObjective {World Policy : Type*}
    (value : World → Policy → ℝ) (p : Policy) : ℝ := ⨅ w, value w p

theorem worstCaseObjective_le {World Policy : Type*} [Fintype World]
    (value : World → Policy → ℝ) (p : Policy) (w : World) :
    worstCaseObjective value p ≤ value w p :=
  ciInf_le (Set.finite_range (fun w => value w p)).bddBelow w

/-- A shared finite upper bound attained in every world makes worst-case
maximization equivalent to attaining that bound in every world. Neither a prior
nor finiteness/compactness of the policy family is required. -/
theorem worstCase_maximizer_iff_attains
    {World Policy : Type*} [Fintype World] [Nonempty World]
    (value : World → Policy → ℝ) (bound : ℝ)
    (hbound : ∀ w p, value w p ≤ bound)
    (witness : Policy) (hattain : ∀ w, value w witness = bound)
    (candidate : Policy) :
    (∀ p, worstCaseObjective value p ≤ worstCaseObjective value candidate) ↔
      ∀ w, value w candidate = bound := by
  have hwitness : worstCaseObjective value witness = bound := by
    simp [worstCaseObjective, hattain]
  constructor
  · intro hmax w
    apply le_antisymm (hbound w candidate)
    exact (hwitness ▸ hmax witness).trans (worstCaseObjective_le value candidate w)
  · intro hc p
    have hcandidate : worstCaseObjective value candidate = bound := by
      simp [worstCaseObjective, hc]
    rw [hcandidate]
    obtain ⟨w⟩ := ‹Nonempty World›
    exact (worstCaseObjective_le value p w).trans (hbound w p)

/-- The equal attained bound is essential: existence of simultaneous component
maxima alone does not make every worst-case optimum a component optimum. -/
theorem worstCase_maximizer_iff_common
    {World Policy : Type*} [Fintype World] [Nonempty World]
    (value : World → Policy → ℝ) (bound : ℝ)
    (hbound : ∀ w p, value w p ≤ bound)
    (witness : Policy) (hattain : ∀ w, value w witness = bound)
    (candidate : Policy) :
    (∀ p, worstCaseObjective value p ≤ worstCaseObjective value candidate) ↔
      ∀ w p, value w p ≤ value w candidate := by
  rw [worstCase_maximizer_iff_attains value bound hbound witness hattain candidate]
  constructor
  · intro hc w p
    rw [hc w]
    exact hbound w p
  · intro hc w
    exact le_antisymm (hbound w candidate) (hattain w ▸ hc w witness)

/-- Under the equal-bound hypothesis, the worst-case and every strictly positive
finite weighted objective have exactly the same maximizers. -/
theorem worstCase_maximizer_iff_weighted
    {World Policy : Type*} [Fintype World] [Nonempty World]
    (value : World → Policy → ℝ) (bound : ℝ)
    (hbound : ∀ w p, value w p ≤ bound)
    (witness : Policy) (hattain : ∀ w, value w witness = bound)
    (weight : World → ℝ) (hweight : ∀ w, 0 < weight w)
    (candidate : Policy) :
    (∀ p, worstCaseObjective value p ≤ worstCaseObjective value candidate) ↔
      ∀ p, (∑ w, weight w * value w p) ≤ ∑ w, weight w * value w candidate := by
  exact (worstCase_maximizer_iff_common value bound hbound witness hattain candidate).trans
    (weighted_maximizer_iff_common weight hweight value witness
      (fun w p => (hbound w p).trans_eq (hattain w).symm) candidate).symm

#print axioms weighted_maximizer_iff_common
end IdExp.IntrinsicRewardComparison
