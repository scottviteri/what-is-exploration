import Formal.AlarmPanel
import Formal.PulseBrierMovement
import Formal.PulseInformationDomination
import Formal.MeasurableInformationContinuity

/-! Actual posterior objectives and squared-movement telescope on the alarm/panel
interface. Countable full-world posteriors use the same positive geometric prior.
No asymptotic attainment or native-completion conclusion is assumed here. -/
namespace IdExp.AlarmPanelPosterior
open MeasureTheory Finset Set Filter Topology
open AlarmPanel (World Action Observation response response_valid)
open PulseBrierScore (Report prior posteriorReport posteriorReport_value
  posteriorReport_apply posteriorPotential ruleValue rulePayoff
  ruleValue_posterior_identity experimentScore_eq_posteriorPotential
  experimentScore_le_one priorPotential likelihood_integrable)
noncomputable section

abbrev record (π : ValidCausalPolicy Action Observation) (t : ℕ) :=
  AlarmPanel.experiment π.1 t

theorem record_valid (π : ValidCausalPolicy Action Observation) (t : ℕ) :
    IsFiniteExperiment (record π t) :=
  AlarmPanel.experiment_valid π.1 π.2 t

def prefixPotential (π : ValidCausalPolicy Action Observation) (t : ℕ) : ℝ :=
  posteriorPotential (record π t) (record_valid π t)

/-- Every countable squared posterior distance is a summable series. -/
theorem posterior_square_distance_summable (p q : Report) :
    Summable (fun θ => (p θ - q θ)^2) := by
  apply Summable.of_nonneg_of_le (fun θ => sq_nonneg _)
    (f := fun θ => 2 * (p θ + q θ)) _ ((p.summable.add q.summable).mul_left 2)
  intro θ
  have hp0 := p.nonneg θ
  have hp1 := p.le_one θ
  have hq0 := q.nonneg θ
  have hq1 := q.le_one θ
  nlinarith [mul_nonneg hp0 hq0]

/-- The actual expected squared change of all posterior label probabilities.
The prior-predictive weight is that of the entire new action-observation prefix. -/
def expectedMovement (π : ValidCausalPolicy Action Observation) (n : ℕ) : ℝ :=
  ∑ w, priorSignalMass prior (record π (n+1)) w *
    ∑' θ, (posteriorReport (record π (n+1)) (record_valid π (n+1)) w θ -
      posteriorReport (record π n) (record_valid π n) (Fin.init w) θ)^2

theorem expectedMovement_nonneg (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    0 ≤ expectedMovement π n := by
  exact Finset.sum_nonneg fun w _ =>
    mul_nonneg ((priorSignalMass_isDist prior (record π (n+1)) (record_valid π (n+1))
      (likelihood_integrable _ (record_valid π (n+1)))).1 w)
      (tsum_nonneg fun θ => sq_nonneg _)

/-- Reporting from the shortened retained record has exactly its shorter-record value. -/
theorem ruleValue_prefix (π : ValidCausalPolicy Action Observation) (n : ℕ)
    (r : CausalFiniteTrace Action Observation n → Report) :
    ruleValue (record π (n+1)) (fun w => r (Fin.init w)) = ruleValue (record π n) r := by
  unfold ruleValue
  apply integral_congr_ae
  apply Eventually.of_forall
  intro θ
  have hp := causalFiniteExperiment_prefix π.1 π.2 response response_valid n
  change rulePayoff (record π (n+1)) (fun w => r (Fin.init w)) θ = _
  change finiteDecisionLaw (record π (n+1)) (causalPrefixRule n) = record π n at hp
  rw [← hp]
  unfold rulePayoff finiteDecisionLaw
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  simp [causalPrefixRule]

/-- Pythagoras for the actual successive countable Bayes posterior vectors. -/
theorem expectedMovement_eq (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    expectedMovement π n = prefixPotential π (n+1) - prefixPotential π n := by
  have h := ruleValue_posterior_identity (record π (n+1)) (record_valid π (n+1))
    (fun w => posteriorReport (record π n) (record_valid π n) (Fin.init w))
  rw [ruleValue_prefix, posteriorReport_value] at h
  change prefixPotential π n = prefixPotential π (n+1) - expectedMovement π n at h
  linarith

theorem prefixPotential_le_one (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    prefixPotential π n ≤ 1 := by
  rw [prefixPotential, ← experimentScore_eq_posteriorPotential]
  exact experimentScore_le_one _ (record_valid π n)

def completeScore (π : ValidCausalPolicy Action Observation) : ℝ :=
  sSup (Set.range (prefixPotential π))

theorem completeScore_le_one (π : ValidCausalPolicy Action Observation) :
    completeScore π ≤ 1 :=
  csSup_le (Set.range_nonempty _) (by
    rintro _ ⟨t, rfl⟩
    exact prefixPotential_le_one π t)

theorem prefixPotential_monotone (π : ValidCausalPolicy Action Observation) :
    Monotone (prefixPotential π) := by
  apply monotone_nat_of_le_succ
  intro n
  have h := expectedMovement_nonneg π n
  rw [expectedMovement_eq] at h
  linarith

theorem record_zero (π : ValidCausalPolicy Action Observation) (θ : World)
    (w : CausalFiniteTrace Action Observation 0) : record π 0 θ w = 1 := by
  simp [record, AlarmPanel.experiment, causalFiniteExperiment, causalTraceProb,
    causalTraceProbFrom, List.ofFn_zero]

theorem posterior_zero (π : ValidCausalPolicy Action Observation)
    (w : CausalFiniteTrace Action Observation 0) (θ : World) :
    posteriorReport (record π 0) (record_valid π 0) w θ = prior.real {θ} := by
  rw [posteriorReport_apply]
  have hm : priorSignalMass prior (record π 0) w = 1 := by
    simp [priorSignalMass, record_zero]
  simp [priorSignalDensity, hm, record_zero]

theorem prefixPotential_zero (π : ValidCausalPolicy Action Observation) :
    prefixPotential π 0 = priorPotential := by
  unfold prefixPotential posteriorPotential
  have hm (w : CausalFiniteTrace Action Observation 0) : priorSignalMass prior (record π 0) w = 1 := by
    simp [priorSignalMass, record_zero]
  have hp (w : CausalFiniteTrace Action Observation 0) :
      (posteriorReport (record π 0) (record_valid π 0) w).potential = priorPotential := by
    unfold FullLabelBrierReport.potential priorPotential
    apply tsum_congr
    intro θ
    rw [posterior_zero]
    rfl
  simp [hm, hp]

/-- Finite sums of genuine squared posterior movements telescope from the prior. -/
theorem finite_movement_telescope (π : ValidCausalPolicy Action Observation) (N : ℕ) :
    (∑ n ∈ Finset.range N, expectedMovement π n) = prefixPotential π N - priorPotential := by
  induction N with
  | zero => simp [prefixPotential_zero]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, expectedMovement_eq]
    ring

theorem prefixPotential_tendsto (π : ValidCausalPolicy Action Observation) :
    Tendsto (prefixPotential π) atTop (𝓝 (completeScore π)) := by
  have hb : BddAbove (Set.range (prefixPotential π)) :=
    ⟨1, by rintro _ ⟨n, rfl⟩; exact prefixPotential_le_one π n⟩
  have h := tendsto_atTop_ciSup (prefixPotential_monotone π) hb
  simpa only [completeScore, iSup] using h

/-- The full nonnegative squared-movement series genuinely converges. -/
theorem movement_hasSum (π : ValidCausalPolicy Action Observation) :
    HasSum (expectedMovement π) (completeScore π - priorPotential) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (expectedMovement_nonneg π) _).2
  simpa only [finite_movement_telescope] using (prefixPotential_tendsto π).sub_const priorPotential

def totalMovement (π : ValidCausalPolicy Action Observation) : ℝ := ∑' n, expectedMovement π n

theorem totalMovement_eq (π : ValidCausalPolicy Action Observation) :
    totalMovement π = completeScore π - priorPotential := (movement_hasSum π).tsum_eq


def prefixInformation (π : ValidCausalPolicy Action Observation) (t : ℕ) : ℝ :=
  infinitePriorInformation prior (record π t)

def completeInformation (π : ValidCausalPolicy Action Observation) : ℝ :=
  sSup (Set.range (prefixInformation π))

theorem prefixInformation_le (π : ValidCausalPolicy Action Observation) (t : ℕ) :
    prefixInformation π t ≤ 2 * Real.log 2 := by
  rw [← PulseInformation.prior_entropy]
  exact information_le_atomic_entropy prior PulseInformation.mass_pos
    PulseInformation.surprisal_integrable _ (record_valid π t)
    (fun _ => measurable_of_countable _)

theorem completeInformation_le (π : ValidCausalPolicy Action Observation) :
    completeInformation π ≤ 2 * Real.log 2 :=
  csSup_le (Set.range_nonempty _) (by
    rintro _ ⟨t,rfl⟩
    exact prefixInformation_le π t)

end
end IdExp.AlarmPanelPosterior
