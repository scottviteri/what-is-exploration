import Formal.PulseBrierPosterior

/-!
# Literal countable-posterior Brier movement on the pulse class

Actual countable Bayes posteriors on successive retained prefixes have expected
squared movement equal to the increase of their unweighted quadratic potential.
The nonnegative series telescopes and converges to the complete posterior gain.
Thus the dominated WAIT optimum is an optimum of the literal complete expected
squared-posterior-movement objective, over all randomized history policies.
-/

namespace IdExp.PulseBrierScore

open MeasureTheory Finset Set Filter Topology
noncomputable section

abbrev record (π : ValidCausalPolicy Bool Bool) (t : ℕ) :=
  causalBehaviorFiniteExperiment π.1 pulseBehavior t

theorem record_valid (π : ValidCausalPolicy Bool Bool) (t : ℕ) :
    IsFiniteExperiment (record π t) :=
  causalBehaviorFiniteExperiment_valid π.1 π.2 pulseBehavior t

def prefixPotential (π : ValidCausalPolicy Bool Bool) (t : ℕ) : ℝ :=
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
def expectedMovement (π : ValidCausalPolicy Bool Bool) (n : ℕ) : ℝ :=
  ∑ w, priorSignalMass prior (record π (n+1)) w *
    ∑' θ, (posteriorReport (record π (n+1)) (record_valid π (n+1)) w θ -
      posteriorReport (record π n) (record_valid π n) (Fin.init w) θ)^2

theorem expectedMovement_nonneg (π : ValidCausalPolicy Bool Bool) (n : ℕ) :
    0 ≤ expectedMovement π n := by
  exact Finset.sum_nonneg fun w _ =>
    mul_nonneg ((priorSignalMass_isDist prior (record π (n+1)) (record_valid π (n+1))
      (likelihood_integrable _ (record_valid π (n+1)))).1 w)
      (tsum_nonneg fun θ => sq_nonneg _)

/-- Reporting from the shortened retained record has exactly its shorter-record value. -/
theorem ruleValue_prefix (π : ValidCausalPolicy Bool Bool) (n : ℕ)
    (r : CausalFiniteTrace Bool Bool n → Report) :
    ruleValue (record π (n+1)) (fun w => r (Fin.init w)) = ruleValue (record π n) r := by
  unfold ruleValue
  apply integral_congr_ae
  apply Eventually.of_forall
  intro θ
  have hp := causalBehaviorFiniteExperiment_prefix π.1 π.2 pulseBehavior n
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
theorem expectedMovement_eq (π : ValidCausalPolicy Bool Bool) (n : ℕ) :
    expectedMovement π n = prefixPotential π (n+1) - prefixPotential π n := by
  have h := ruleValue_posterior_identity (record π (n+1)) (record_valid π (n+1))
    (fun w => posteriorReport (record π n) (record_valid π n) (Fin.init w))
  rw [ruleValue_prefix, posteriorReport_value] at h
  change prefixPotential π n = prefixPotential π (n+1) - expectedMovement π n at h
  linarith

theorem prefixPotential_eq_prefixScore (π : ValidCausalPolicy Bool Bool) (n : ℕ) :
    prefixPotential π n = prefixScore π n :=
  (experimentScore_eq_posteriorPotential (record π n) (record_valid π n)).symm

theorem prefixPotential_monotone (π : ValidCausalPolicy Bool Bool) :
    Monotone (prefixPotential π) := by
  apply monotone_nat_of_le_succ
  intro n
  have h := expectedMovement_nonneg π n
  rw [expectedMovement_eq] at h
  linarith

theorem record_zero (π : ValidCausalPolicy Bool Bool) (θ : World)
    (w : CausalFiniteTrace Bool Bool 0) : record π 0 θ w = 1 := by
  simp [record, causalBehaviorFiniteExperiment, causalBehaviorTraceProb,
    causalPolicyProb, causalResponseProb, causalPolicyProbFrom, causalResponseProbFrom,
    pulseBehavior]

theorem posterior_zero (π : ValidCausalPolicy Bool Bool)
    (w : CausalFiniteTrace Bool Bool 0) (θ : World) :
    posteriorReport (record π 0) (record_valid π 0) w θ = prior.real {θ} := by
  rw [posteriorReport_apply]
  have hm : priorSignalMass prior (record π 0) w = 1 := by
    simp [priorSignalMass, record_zero]
  simp [priorSignalDensity, hm, record_zero]

theorem prefixPotential_zero (π : ValidCausalPolicy Bool Bool) :
    prefixPotential π 0 = priorPotential := by
  unfold prefixPotential posteriorPotential
  have hm (w : CausalFiniteTrace Bool Bool 0) : priorSignalMass prior (record π 0) w = 1 := by
    simp [priorSignalMass, record_zero]
  have hp (w : CausalFiniteTrace Bool Bool 0) :
      (posteriorReport (record π 0) (record_valid π 0) w).potential = priorPotential := by
    unfold FullLabelBrierReport.potential priorPotential
    apply tsum_congr
    intro θ
    rw [posterior_zero]
    rfl
  simp [hm, hp]

/-- Finite sums of genuine squared posterior movements telescope from the prior. -/
theorem finite_movement_telescope (π : ValidCausalPolicy Bool Bool) (N : ℕ) :
    (∑ n ∈ Finset.range N, expectedMovement π n) = prefixPotential π N - priorPotential := by
  induction N with
  | zero => simp [prefixPotential_zero]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, expectedMovement_eq]
    ring

theorem prefixPotential_tendsto (π : ValidCausalPolicy Bool Bool) :
    Tendsto (prefixPotential π) atTop (𝓝 (completeScore π)) := by
  have hb : BddAbove (Set.range (prefixPotential π)) :=
    ⟨1, by rintro _ ⟨n, rfl⟩; rw [prefixPotential_eq_prefixScore]; exact prefixScore_le_one π n⟩
  have h := tendsto_atTop_ciSup (prefixPotential_monotone π) hb
  have he : (fun n => prefixPotential π n) = prefixScore π :=
    funext (prefixPotential_eq_prefixScore π)
  simpa only [he, completeScore, iSup] using h

/-- The full nonnegative squared-movement series genuinely converges. -/
theorem movement_hasSum (π : ValidCausalPolicy Bool Bool) :
    HasSum (expectedMovement π) (completePosteriorGain π) := by
  rw [completePosteriorGain_eq]
  apply (hasSum_iff_tendsto_nat_of_nonneg (expectedMovement_nonneg π) _).2
  simpa only [finite_movement_telescope] using (prefixPotential_tendsto π).sub_const priorPotential

def totalMovement (π : ValidCausalPolicy Bool Bool) : ℝ := ∑' n, expectedMovement π n

theorem totalMovement_eq (π : ValidCausalPolicy Bool Bool) :
    totalMovement π = completePosteriorGain π := (movement_hasSum π).tsum_eq

/-- The complete ordinary full-label Brier movement objective has a globally
maximizing policy strictly dominated by a feasible policy in the finitary order. -/
theorem movement_dominated_maximizer :
    (∀ π : ValidCausalPolicy Bool Bool, totalMovement π ≤ totalMovement (pulsePolicy false)) ∧
    CausalBehaviorFinitaryDominates pulseBehavior (pulsePolicy true) (pulsePolicy false) ∧
      ¬ CausalBehaviorFinitaryDominates pulseBehavior (pulsePolicy false) (pulsePolicy true) := by
  simp only [totalMovement_eq]
  exact posterior_gain_dominated_maximizer

/-- Enumerate infinity first, then the finite pulse times. -/
def geometricWorldEquiv : ℕ ≃ World :=
  Equiv.ofBijective waitingQueryGeometricWorld (by
    constructor
    · intro n m h
      cases n <;> cases m <;> simp_all [waitingQueryGeometricWorld]
    · intro θ
      cases θ with
      | none => exact ⟨0, rfl⟩
      | some k => exact ⟨k+1, rfl⟩)

theorem geometric_index_mass (n : ℕ) :
    prior.real {geometricWorldEquiv n} = (1/2 : ℝ)^(n+1) := by
  cases n with
  | zero =>
      change prior.real {none} = (1/2 : ℝ)^1
      simpa only [pow_one] using waitingQueryGeometricPrior_none
  | succ n => exact waitingQueryGeometricPrior_some n

/-- The ordinary full-label prior quadratic potential is exactly one third. -/
theorem priorPotential_eq_third : priorPotential = 1/3 := by
  change (∑' θ : World, prior.real {θ} ^ 2) = _
  rw [← geometricWorldEquiv.tsum_eq (fun θ => prior.real {θ} ^ 2)]
  simp only [geometric_index_mass]
  have hp (n : ℕ) : ((1/2 : ℝ)^(n+1))^2 = (1/4 : ℝ)^n * (1/4) := by
    rw [← pow_mul, Nat.mul_comm (n+1) 2, pow_mul]
    norm_num [pow_succ]
  simp_rw [hp]
  rw [tsum_mul_right, tsum_geometric_of_abs_lt_one (by norm_num : |(1/4 : ℝ)| < 1)]
  norm_num

/-- WAIT earns the maximum complete full-label Brier movement, two thirds. -/
theorem wait_totalMovement : totalMovement (pulsePolicy false) = 2/3 := by
  rw [totalMovement_eq, completePosteriorGain_eq, wait_completeScore, priorPotential_eq_third]
  norm_num

end
end IdExp.PulseBrierScore
