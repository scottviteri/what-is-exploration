import Formal.PairedAlarmInformationCore
import Formal.PairedAlarmNativeExtraction

/-!
# Complete information and Brier returns tie on the paired alarm

Every valid randomized history policy on the paired interface attains
the complete information value `sup_t I(Θ; H_t) = H(α) = 2 log 2` nats
(two bits) and the complete ordinary Brier return
`Σ_{t≥0} E‖β_{t+1}-β_t‖² = 1 - ‖α‖² = 2/3`.

The lower bounds use the literal deterministic extraction
`PairedAlarm.extractWait` of the pulse WAIT record of the same length
from every collected paired record (`extractWait_law`); no terminal
identification bridge is assumed. The upper bounds are the prior entropy and
the unit quadratic-potential bound.
-/

noncomputable section
namespace IdExp.PairedAlarm.Information
open MeasureTheory Finset Set Filter Topology
open PulseBrierScore (prior Report ruleValue rulePayoff)

/-- Data processing: the extracted WAIT prefix carries no more information than
the paired record of the same length. -/
theorem prefixInformation_ge_wait (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    PulseInformation.prefixInformation (pulsePolicy false) n ≤ prefixInformation π n := by
  have h := infinitePriorInformation_mono_garbling prior (record π n)
    (record_valid π n) (fun _ => measurable_of_countable _)
    (extractWaitRule n) (extractWaitRule_valid n)
  change infinitePriorInformation prior
    (finiteDecisionLaw (experiment π.1 n) (extractWaitRule n)) ≤ _ at h
  rw [extractWait_law π.1 π.2 n] at h
  exact h

/-- All randomized history policies attain the same finite complete information
value, the prior entropy `2 log 2` nats. -/
theorem completeInformation_eq (π : ValidCausalPolicy Action Observation) :
    completeInformation π = 2 * Real.log 2 := by
  apply le_antisymm (completeInformation_le π)
  apply le_of_tendsto PulseInformation.wait_information_tendsto
  apply Eventually.of_forall
  intro n
  apply (prefixInformation_ge_wait π n).trans
  exact le_csSup ⟨2 * Real.log 2, by
    rintro _ ⟨t, rfl⟩
    exact prefixInformation_le π t⟩ (Set.mem_range_self n)

/-- The same complete information value in bits: two bits for every policy. -/
theorem completeInformation_bits (π : ValidCausalPolicy Action Observation) :
    completeInformation π / Real.log 2 = 2 := by
  rw [completeInformation_eq]
  have hl : Real.log (2:ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  exact mul_div_cancel_right₀ 2 hl

/-- Replaying the exact monitor statistic preserves the actual reporting payoff. -/
theorem extracted_report_value (π : ValidCausalPolicy Action Observation) (n : ℕ)
    (r : CausalFiniteTrace Bool Bool n → Report) :
    ruleValue (record π n) (fun h => r (extractWait n h)) =
      ruleValue (pulseExperiment false n) r := by
  unfold ruleValue
  apply integral_congr_ae
  apply Eventually.of_forall
  intro θ
  rw [← extractWait_law π.1 π.2 n]
  unfold rulePayoff finiteDecisionLaw
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  simp [extractWaitRule, mul_ite]

/-- The complete posterior quadratic potential reaches one for every policy. -/
theorem completeScore_eq (π : ValidCausalPolicy Action Observation) :
    completeScore π = 1 := by
  apply le_antisymm (completeScore_le_one π)
  have hlimit : Tendsto (fun n => 1 - 2 * waitingQueryTail prior n) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub ((waitingQueryTail_tendsto_zero prior).const_mul 2)
  apply le_of_tendsto hlimit
  apply Eventually.of_forall
  intro n
  rw [← PulseBrierScore.wait_point_value n, ← extracted_report_value π n]
  have h := PulseBrierScore.ruleValue_le_experimentScore (record π n)
    (record_valid π n)
    (fun h => PulseBrierScore.waitReport n (extractWait n h))
  rw [PulseBrierScore.experimentScore_eq_posteriorPotential _ (record_valid π n)] at h
  apply h.trans
  exact le_csSup ⟨1, by
    rintro _ ⟨t, rfl⟩
    exact prefixPotential_le_one π t⟩ (Set.mem_range_self n)

/-- The literal infinite sum of expected squared movements of the posterior
world probabilities is `1 - ‖α‖² = 2/3` for every policy. -/
theorem totalMovement_eq_two_thirds (π : ValidCausalPolicy Action Observation) :
    totalMovement π = 2/3 := by
  rw [totalMovement_eq, completeScore_eq, PulseBrierScore.priorPotential_eq_third]
  norm_num

/-- Both complete posterior objectives tie all valid policies. -/
theorem posterior_objectives_tie (π ρ : ValidCausalPolicy Action Observation) :
    completeInformation π = completeInformation ρ ∧ totalMovement π = totalMovement ρ := by
  simp [completeInformation_eq, totalMovement_eq_two_thirds]

end IdExp.PairedAlarm.Information
