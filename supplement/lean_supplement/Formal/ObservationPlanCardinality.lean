import Formal.CausalCoverageMaximin
import Mathlib.Algebra.Ring.GeomSum

/-!
# Reader-form cardinality of the actual native observation-plan type

`CausalCoverageMaximin` already proves the cardinality of the actual recursive
`CausalObservationPlan` and identifies its node count with the sum over all
observation-history depths. These corollaries give the exact printed forms,
including the geometric quotient only when the observation alphabet has more
than one symbol. They do not count the redundant full-history plan type.
-/

namespace IdExp

open Finset

variable {A O : Type*} [Fintype A] [Fintype O]
  [Nonempty A] [Nonempty O]

/-- The sum-exponent form used for the paper's finite native test family. -/
theorem card_causalObservationPlan_eq_power_sum (n : ℕ) :
    Nat.card (CausalObservationPlan A O n) =
      Nat.card A ^ (∑ k : Fin n, Nat.card O ^ k.1) := by
  classical
  rw [card_causalObservationPlan, observationTreeNodeCount_eq_sum]

/-- Geometric-series node count, with the paper's nondegenerate alphabet
condition stated explicitly. Nat division is exact by the geometric identity. -/
theorem observationTreeNodeCount_eq_quotient
    (hO : 1 < Nat.card O) (n : ℕ) :
    observationTreeNodeCount O n = (Nat.card O ^ n - 1) / (Nat.card O - 1) := by
  classical
  rw [observationTreeNodeCount_eq_sum]
  rw [Fin.sum_univ_eq_sum_range]
  exact Nat.geomSum_eq hO n

/-- The geometric-exponent form of the cardinality for the actual native
observation-plan type. -/
theorem card_causalObservationPlan_eq_power_quotient
    (hO : 1 < Nat.card O) (n : ℕ) :
    Nat.card (CausalObservationPlan A O n) =
      Nat.card A ^ ((Nat.card O ^ n - 1) / (Nat.card O - 1)) := by
  classical
  rw [card_causalObservationPlan, observationTreeNodeCount_eq_quotient hO]

/-- The one-observation-symbol case is finite and has exactly one decision
node per depth; the quotient expression is deliberately not used here. -/
theorem card_causalObservationPlan_of_one_observation
    (hO : Nat.card O = 1) (n : ℕ) :
    Nat.card (CausalObservationPlan A O n) = Nat.card A ^ n := by
  classical
  rw [card_causalObservationPlan_eq_power_sum]
  simp only [Nat.card_eq_fintype_card] at hO ⊢
  simp [hO]

end IdExp
