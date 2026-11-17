import Formal.PairedAlarm
import Formal.PulseBrierMovement
import Formal.PulseInformationDomination
import Formal.MeasurableInformationContinuity
import Formal.WorstPriorInformation

/-!
# Posterior objectives on the paired alarm interface

The actual Bayes posterior `β_t` over the countable world labels `Option ℕ`,
given the complete length-`t` action-observation record of
`PairedAlarm.experiment`, under the positive geometric prior
`α(none) = 1/2`, `α(some k) = 2^{-(k+2)}` (`PulseBrierScore.prior`).

* `prefixInformation π t` is `I(Θ; H_t)`, in nats; `completeInformation π` is
  `sup_t I(Θ; H_t)`.
* `prefixPotential π t` is the expected squared posterior norm `E‖β_t‖²`, over
  the probabilities of individual worlds (no tail is merged into one label).
* `expectedMovement π n` is the ordinary Brier movement `E‖β_{n+1} - β_n‖²`,
  weighted by the prior-predictive mass of the entire new record.

This module proves the squared-movement telescope
`Σ_{n<N} E‖β_{n+1}-β_n‖² = E‖β_N‖² - ‖α‖²`, its convergent infinite form,
the prior-entropy ceiling for information, and `I(Θ; H_0) = 0`. No
asymptotic attainment or native conclusion is assumed here. All declarations
are in `IdExp.PairedAlarm.Information`.
-/

noncomputable section
namespace IdExp.PairedAlarm.Information
open MeasureTheory Finset Set Filter Topology
open PulseBrierScore (Report prior posteriorReport posteriorReport_value
  posteriorReport_apply posteriorPotential ruleValue rulePayoff
  ruleValue_posterior_identity experimentScore_eq_posteriorPotential
  experimentScore_le_one priorPotential likelihood_integrable)

/-- The complete paired record of a valid policy at horizon `t`. -/
abbrev record (π : ValidCausalPolicy Action Observation) (t : ℕ) :=
  experiment π.1 t

theorem record_valid (π : ValidCausalPolicy Action Observation) (t : ℕ) :
    IsFiniteExperiment (record π t) :=
  experiment_valid π.1 π.2 t

/-- Expected squared norm of the actual posterior over individual worlds. -/
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

/-- The actual expected squared change of all posterior world probabilities.
The prior-predictive weight is that of the entire new action-observation record. -/
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

/-- The complete posterior quadratic potential, `sup_t E‖β_t‖²`. -/
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
  simp [record, experiment, causalFiniteExperiment, causalTraceProb,
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
  have hm (w : CausalFiniteTrace Action Observation 0) :
      priorSignalMass prior (record π 0) w = 1 := by
    simp [priorSignalMass, record_zero]
  have hp (w : CausalFiniteTrace Action Observation 0) :
      (posteriorReport (record π 0) (record_valid π 0) w).potential = priorPotential := by
    unfold FullLabelBrierReport.potential priorPotential
    apply tsum_congr
    intro θ
    rw [posterior_zero]
    rfl
  simp [hm, hp]

/-- Finite sums of genuine squared posterior movements telescope from the prior:
`Σ_{n<N} E‖β_{n+1}-β_n‖² = E‖β_N‖² - ‖α‖²`. -/
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
  simpa only [finite_movement_telescope] using
    (prefixPotential_tendsto π).sub_const priorPotential

/-- The complete (undiscounted) Brier return `Σ_{t≥0} E‖β_{t+1}-β_t‖²`. -/
def totalMovement (π : ValidCausalPolicy Action Observation) : ℝ := ∑' n, expectedMovement π n

theorem totalMovement_eq (π : ValidCausalPolicy Action Observation) :
    totalMovement π = completeScore π - priorPotential := (movement_hasSum π).tsum_eq

/-- Mutual information `I(Θ; H_t)` between the world and the complete record, in nats. -/
def prefixInformation (π : ValidCausalPolicy Action Observation) (t : ℕ) : ℝ :=
  infinitePriorInformation prior (record π t)

/-- The complete information objective `sup_t I(Θ; H_t)`, in nats. -/
def completeInformation (π : ValidCausalPolicy Action Observation) : ℝ :=
  sSup (Set.range (prefixInformation π))

/-- The prior entropy `H(α) = 2 log 2` nats (two bits) bounds every prefix. -/
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

/-- The empty record carries no information. -/
theorem information_zero (π : ValidCausalPolicy Action Observation) :
    prefixInformation π 0 = 0 := by
  rw [prefixInformation, infinitePriorInformation_eq_ent_mass_sub
    prior (record π 0) (record_valid π 0) (fun _ => measurable_of_countable _)]
  have hm (u : CausalFiniteTrace Action Observation 0) :
      priorSignalMass prior (record π 0) u = 1 := by
    simp [priorSignalMass, record_zero]
  simp [ent, hm, record_zero]

section Discrete
local instance : TopologicalSpace World := ⊥
local instance : DiscreteTopology World := ⟨rfl⟩
local instance : OpensMeasurableSpace World :=
  ⟨fun s _ => Set.Countable.measurableSet (Set.to_countable s)⟩

theorem information_bounds (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    0 ≤ prefixInformation π n ∧ prefixInformation π n ≤ 2 * Real.log 2 := by
  refine ⟨?_, prefixInformation_le π n⟩
  exact infinitePriorInformation_nonneg prior _ (record_valid π n)
    (fun _ => continuous_of_discreteTopology)

end Discrete

theorem potential_bounds (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    0 ≤ prefixPotential π n ∧ prefixPotential π n ≤ 1 := by
  refine ⟨?_, prefixPotential_le_one π n⟩
  have h := prefixPotential_monotone π (Nat.zero_le n)
  rw [prefixPotential_zero, PulseBrierScore.priorPotential_eq_third] at h
  linarith

end IdExp.PairedAlarm.Information
