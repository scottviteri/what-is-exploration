import Formal.AlarmPanelFinite
import Formal.PseudoCountProcess

/-!
# Two-observation categorical pseudo-count calculation

The reward is the actual add-one categorical before/after density expression
on the four raw labels, summed over exactly two observations. This retained
calculation is not the continuing T >= 64 optimizer theorem; use
`AlarmPanelPseudoCountObjective.lean` for that selected result.
-/
namespace IdExp.AlarmPanel
open Finset
noncomputable section

/-- rho_D(x) = (number of previous x + 1) / (archive length + 4). -/
abbrev categoricalDensity := FirstVisitCount.countDensity
/-- rho'_D(x) is obtained by incrementing that observed coordinate. -/
abbrev updatedCategoricalDensity := FirstVisitCount.updatedCountDensity
/-- rho*(1-rho')/(rho'-rho), rather than an assumed count bonus. -/
abbrev categoricalPseudoCount := FirstVisitCount.modelPseudoCount

theorem categoricalDensity_valid (D : List Observation) : IsDist (categoricalDensity D) :=
  FirstVisitCount.countDensity_valid D

theorem categoricalPseudoCount_empty (o : Observation) : categoricalPseudoCount [] o = 1 :=
  FirstVisitCount.modelPseudoCount_empty o

theorem categoricalPseudoCount_single (o p : Observation) :
    categoricalPseudoCount [o] p = if o=p then 2 else 1 :=
  FirstVisitCount.modelPseudoCount_single o p

def densityPseudoCountObjective (π : ValidCausalPolicy Action Observation) : ℝ :=
  twoExpectation π (fun x y =>
    1 / Real.sqrt (categoricalPseudoCount [] x.2) +
    1 / Real.sqrt (categoricalPseudoCount [x.2] y.2))

/-- The density learner's literal two bonuses equal the previously evaluated
payoff for every stochastic history policy under the exact countable prior. -/
theorem densityPseudoCountObjective_eq (π : ValidCausalPolicy Action Observation) :
    densityPseudoCountObjective π = pseudoCountObjective π := by
  unfold densityPseudoCountObjective pseudoCountObjective twoExpectation
  apply sum_congr rfl; intro x _
  apply sum_congr rfl; intro y _
  dsimp
  rw [categoricalPseudoCount_empty,categoricalPseudoCount_single]
  by_cases h : x.2 = y.2 <;> norm_num [h]

theorem densityPseudoCountObjective_maximizer_iff (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, densityPseudoCountObjective ρ ≤ densityPseudoCountObjective π) ↔ repetition π = 0 := by
  simp only [densityPseudoCountObjective_eq]
  exact pseudoCountObjective_maximizer_iff π

theorem densityPseudoCountObjective_maximizer_skips_inspection
    (π : ValidCausalPolicy Action Observation)
    (hmax : ∀ ρ, densityPseudoCountObjective ρ ≤ densityPseudoCountObjective π) : π.1 [] 0 = 0 := by
  have hr := (densityPseudoCountObjective_maximizer_iff π).mp hmax
  have hb := repetition_ge_inspect π
  linarith [(π.2 []).1 0]

end
end IdExp.AlarmPanel
