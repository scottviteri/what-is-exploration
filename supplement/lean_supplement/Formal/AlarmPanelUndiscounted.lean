import Formal.AlarmPanelControl
import Formal.AlarmPanelNativeAudit

/-!
# Undiscounted empowerment optima on the alarm/panel interface

The channel horizon is one step. The reward objective sums the capacities at
exactly the first two visited decision states, with no discount, then averages
under the study's actual geometric world prior. All policies are arbitrary
randomized history policies, including their continuation after the reward
horizon. Every maximizer skips startup inspection and has inspection deficiency
one half at every positive finite collection time and in the eventual infimum.

This is a finite reward horizon, not an undiscounted infinite total. The latter
can diverge and is not defined or asserted here.
-/

namespace IdExp.AlarmPanel.Control

noncomputable section

/-- The actual prior average of the two-stage visited one-step capacity sum. -/
def priorEmpowermentTwo (π : ValidCausalPolicy Action Observation) : ℝ :=
  ∫ θ, empowermentTwo π θ ∂AlarmPanelPrior.prior

/-- The prior-integrated objective has a policy-independent startup term and
one bit of panel capacity precisely on the non-inspecting branch (in nats). -/
theorem priorEmpowermentTwo_eq (π : ValidCausalPolicy Action Observation) :
    priorEmpowermentTwo π =
      (localCapacity none [] + localCapacity (some 0) []) / 2 +
        (1 - inspectionProbability π.1) * Real.log 2 := by
  unfold priorEmpowermentTwo
  rw [AlarmPanelPrior.integral_none_some _ (by
    intro k
    rw [empowermentTwo_eq, empowermentTwo_eq]
    rfl)]
  rw [empowermentTwo_eq, empowermentTwo_eq]
  simp only [inspectionProbability, inspect]
  ring

/-- All and only the policies that skip startup inspection maximize the
undiscounted two-stage objective. Their later actions are unrestricted. -/
theorem priorEmpowermentTwo_maximizer_iff
    (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, priorEmpowermentTwo ρ ≤ priorEmpowermentTwo π) ↔
      inspectionProbability π.1 = 0 := by
  have hworld := empowermentTwo_maximizer_iff π none
  change (∀ ρ, empowermentTwo ρ none ≤ empowermentTwo π none) ↔
    inspectionProbability π.1 = 0 at hworld
  rw [← hworld]
  simp only [priorEmpowermentTwo_eq, empowermentTwo_eq,
    inspectionProbability, inspect]
  constructor <;> intro h ρ <;> have hh := h ρ <;> linarith

/-- The maximizing set is nonempty: the already defined deterministic play
policy used by the novelty comparison attains the empowerment maximum too. -/
theorem priorEmpowermentTwo_attained :
    ∀ ρ, priorEmpowermentTwo ρ ≤ priorEmpowermentTwo noveltyPolicy := by
  apply (priorEmpowermentTwo_maximizer_iff noveltyPolicy).2
  exact noveltyPolicy_root

/-- Collection time is unrestricted by the two-stage reward horizon. -/
theorem priorEmpowermentTwo_maximizer_inspection_deficiency
    (π : ValidCausalPolicy Action Observation)
    (hopt : ∀ ρ, priorEmpowermentTwo ρ ≤ priorEmpowermentTwo π)
    (t : ℕ) (ht : 1 ≤ t) :
    finiteDeficiency (experiment π.1 t) (experiment inspectPolicy 1) = 1 / 2 := by
  cases t with
  | zero => omega
  | succ n =>
    rw [inspection_deficiency_exact π.1 π.2 n,
      (priorEmpowermentTwo_maximizer_iff π).1 hopt]
    norm_num

/-- Eventual inspection error uses arbitrarily large finite records, represented
by all positive horizons `n + 1`; no completed infinite record is supplied. -/
def eventualInspectionDeficiency (π : ValidCausalPolicy Action Observation) : ℝ :=
  ⨅ n : ℕ, finiteDeficiency (experiment π.1 (n + 1)) (experiment inspectPolicy 1)

theorem eventualInspectionDeficiency_eq (π : ValidCausalPolicy Action Observation) :
    eventualInspectionDeficiency π = (1 - inspectionProbability π.1) / 2 := by
  simp only [eventualInspectionDeficiency, inspection_deficiency_exact π.1 π.2]
  simp

/-- Every global maximizer has permanent error one half even after allowing
all of its arbitrary post-horizon continuation. -/
theorem priorEmpowermentTwo_maximizer_eventual_deficiency
    (π : ValidCausalPolicy Action Observation)
    (hopt : ∀ ρ, priorEmpowermentTwo ρ ≤ priorEmpowermentTwo π) :
    eventualInspectionDeficiency π = 1 / 2 := by
  rw [eventualInspectionDeficiency_eq, (priorEmpowermentTwo_maximizer_iff π).1 hopt]
  norm_num

/-- Every global maximizer is strictly dominated in the finitary process order
by the feasible inspection policy; this is not merely one bad maximizing tie. -/
theorem priorEmpowermentTwo_maximizer_strictly_dominated
    (π : ValidCausalPolicy Action Observation)
    (hopt : ∀ ρ, priorEmpowermentTwo ρ ≤ priorEmpowermentTwo π) :
    CausalFinitaryDominates response ⟨inspectPolicy, inspectPolicy_valid⟩ π ∧
      ¬ CausalFinitaryDominates response π ⟨inspectPolicy, inspectPolicy_valid⟩ := by
  apply inspection_strictly_dominates π.1 π.2
  rw [(priorEmpowermentTwo_maximizer_iff π).1 hopt]
  norm_num

/-- Attainment and all-maximizer failure for the literal undiscounted objective. -/
theorem priorEmpowermentTwo_all_optima_failure :
    (∃ π, ∀ ρ, priorEmpowermentTwo ρ ≤ priorEmpowermentTwo π) ∧
      ∀ π : ValidCausalPolicy Action Observation,
        (∀ ρ, priorEmpowermentTwo ρ ≤ priorEmpowermentTwo π) →
          (∀ t : ℕ, 1 ≤ t →
            finiteDeficiency (experiment π.1 t) (experiment inspectPolicy 1) = 1 / 2) ∧
          eventualInspectionDeficiency π = 1 / 2 ∧
          CausalFinitaryDominates response ⟨inspectPolicy, inspectPolicy_valid⟩ π ∧
          ¬ CausalFinitaryDominates response π ⟨inspectPolicy, inspectPolicy_valid⟩ := by
  refine ⟨⟨noveltyPolicy, priorEmpowermentTwo_attained⟩, ?_⟩
  intro π hopt
  exact ⟨priorEmpowermentTwo_maximizer_inspection_deficiency π hopt,
    priorEmpowermentTwo_maximizer_eventual_deficiency π hopt,
    priorEmpowermentTwo_maximizer_strictly_dominated π hopt⟩

end
end IdExp.AlarmPanel.Control
