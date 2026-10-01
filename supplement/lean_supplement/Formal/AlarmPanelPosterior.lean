import Formal.AlarmPanelPosteriorCore
import Formal.AlarmPanelNativeExtraction

/-! Every actual policy on the alarm/panel interface maximizes complete full-world
information and ordinary Brier movement. The proof uses a literal deterministic
extraction of the pulse prefix, not an assumed terminal identification bridge. -/
namespace IdExp.AlarmPanelPosterior
open MeasureTheory Finset Set Filter Topology
open AlarmPanel (World Action Observation)
open PulseBrierScore (prior Report ruleValue rulePayoff)
noncomputable section

theorem prefixInformation_ge_wait (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    PulseInformation.prefixInformation (pulsePolicy false) n ≤ prefixInformation π (2*n+1) := by
  have h := infinitePriorInformation_mono_garbling prior (record π (2*n+1))
    (record_valid π (2*n+1)) (fun _ => measurable_of_countable _)
    (AlarmPanel.extractWaitRule n) (AlarmPanel.extractWaitRule_valid n)
  change infinitePriorInformation prior
    (finiteDecisionLaw (AlarmPanel.experiment π.1 (2*n+1)) (AlarmPanel.extractWaitRule n)) ≤ _ at h
  rw [AlarmPanel.extractWait_law π.1 π.2 n] at h
  exact h

/-- All randomized history policies attain the same finite complete information value. -/
theorem completeInformation_eq (π : ValidCausalPolicy Action Observation) :
    completeInformation π = 2 * Real.log 2 := by
  apply le_antisymm (completeInformation_le π)
  apply le_of_tendsto PulseInformation.wait_information_tendsto
  apply Eventually.of_forall
  intro n
  apply (prefixInformation_ge_wait π n).trans
  exact le_csSup ⟨2 * Real.log 2, by
    rintro _ ⟨t, rfl⟩
    exact prefixInformation_le π t⟩ (Set.mem_range_self (2*n+1))

/-- Replaying the exact monitor statistic preserves the actual reporting payoff. -/
theorem extracted_report_value (π : ValidCausalPolicy Action Observation) (n : ℕ)
    (r : CausalFiniteTrace Bool Bool n → Report) :
    ruleValue (record π (2*n+1)) (fun h => r (AlarmPanel.extractWait n h)) =
      ruleValue (pulseExperiment false n) r := by
  unfold ruleValue
  apply integral_congr_ae
  apply Eventually.of_forall
  intro θ
  rw [← AlarmPanel.extractWait_law π.1 π.2 n]
  unfold rulePayoff finiteDecisionLaw
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  simp [AlarmPanel.extractWaitRule, mul_ite]

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
  have h := PulseBrierScore.ruleValue_le_experimentScore (record π (2*n+1))
    (record_valid π (2*n+1))
    (fun h => PulseBrierScore.waitReport n (AlarmPanel.extractWait n h))
  rw [PulseBrierScore.experimentScore_eq_posteriorPotential _ (record_valid π (2*n+1))] at h
  apply h.trans
  exact le_csSup ⟨1, by
    rintro _ ⟨t, rfl⟩
    exact prefixPotential_le_one π t⟩ (Set.mem_range_self (2*n+1))

/-- The literal infinite sum of expected full-label squared posterior movements. -/
theorem totalMovement_eq_two_thirds (π : ValidCausalPolicy Action Observation) :
    totalMovement π = 2/3 := by
  rw [totalMovement_eq, completeScore_eq, PulseBrierScore.priorPotential_eq_third]
  norm_num

theorem posterior_objectives_tie (π ρ : ValidCausalPolicy Action Observation) :
    completeInformation π = completeInformation ρ ∧ totalMovement π = totalMovement ρ := by
  simp [completeInformation_eq, totalMovement_eq_two_thirds]

end
end IdExp.AlarmPanelPosterior
