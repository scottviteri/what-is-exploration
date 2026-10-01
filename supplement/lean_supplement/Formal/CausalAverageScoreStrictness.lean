import Formal.AverageFiniteExperimentScore
import Formal.CausalInformationStrictness

/-! Objective-independent average-error strictness for actual randomized
controlled-prefix policy records. This bridge discharges measurability and
prefix projection; the remaining score-cost hypothesis is explicit. -/
namespace IdExp
open MeasureTheory
open scoped ENNReal
noncomputable section
variable {Θ P A O : Type*} [MeasurableSpace Θ]
  [Fintype A] [Fintype O] [Nonempty A] [Nonempty O]
  (μ : Measure Θ) [IsProbabilityMeasure μ]
  (ps : Θ → CausalBehavior A O)
  (hm : ∀ h, Measurable (fun θ => (ps θ).mass h))
  (policies : P → ValidCausalPolicy A O)
  (SCORE : AverageFiniteExperimentScore Θ (CausalFiniteTrace A O) μ)

/-- Genuine action-observation records, with their measurability certificates. -/
def causalAverageScoreRecords : P → ℕ → IndexedMeasurableFiniteExperiment Θ (CausalFiniteTrace A O) :=
  AverageFiniteExperimentScore.records (causalFamilyFiniteProcess ps hm policies)

/-- The supremum of the finite score on actual policy histories. -/
def causalAverageTotalScore (π : P) : ℝ≥0∞ :=
  SCORE.toScoreExperimentSystem.totalScore (causalAverageScoreRecords ps hm policies) π

/-- Finite-score equality is exactly reverse average finitary simulation.
Cost uniformity is required only below a fixed score ceiling. -/
theorem causalAverageTotalScore_eq_iff_reverse
    (hc : SCORE.toScoreExperimentSystem.HasBoundedFixedTargetCost
      (causalAverageScoreRecords ps hm policies))
    {π ρ : P} (hb : causalAverageTotalScore μ ps hm policies SCORE π ≠ ⊤)
    (h : CausalBehaviorAverageFinitaryDominates μ ps (policies π) (policies ρ)) :
    causalAverageTotalScore μ ps hm policies SCORE π =
      causalAverageTotalScore μ ps hm policies SCORE ρ ↔
        CausalBehaviorAverageFinitaryDominates μ ps (policies ρ) (policies π) :=
  SCORE.toScoreExperimentSystem.totalScore_eq_iff_reverse_of_bounded_cost
    (causalAverageScoreRecords ps hm policies)
    (SCORE.records_refines (causalFamilyFiniteProcess ps hm policies)) hc hb h

/-- Exact uniform strictness criterion for any qualifying average-error score,
on any declared feasible family of valid causal policies. -/
theorem causalAverageTotalScore_uniform_strictness_iff [Nonempty Θ]
    (hc : SCORE.toScoreExperimentSystem.HasBoundedFixedTargetCost
      (causalAverageScoreRecords ps hm policies)) :
    StrictlyMonotoneFor
      (fun π ρ => CausalBehaviorFinitaryDominates ps (policies π) (policies ρ))
      (causalAverageTotalScore μ ps hm policies SCORE) ↔
    ReverseDominanceLifts
      (fun π ρ => CausalBehaviorFinitaryDominates ps (policies π) (policies ρ))
      (fun π ρ => CausalBehaviorAverageFinitaryDominates μ ps (policies π) (policies ρ)) ∧
    NoInfiniteStrictPairFor
      (fun π ρ => CausalBehaviorFinitaryDominates ps (policies π) (policies ρ))
      (causalAverageTotalScore μ ps hm policies SCORE) :=
  SCORE.toScoreExperimentSystem.totalScore_strictness_iff_of_bounded_cost
    (causalAverageScoreRecords ps hm policies)
    (SCORE.records_refines (causalFamilyFiniteProcess ps hm policies)) hc _
    (fun _ _ h => (causalFamilyFiniteProcess ps hm policies).averageDominates_of_uniform μ h)

end
end IdExp
