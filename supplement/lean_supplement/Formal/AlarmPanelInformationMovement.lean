import Formal.CountablePosteriorKL
import Formal.AlarmPanelPosteriorDiscount

/-!
# Literal successive-posterior information on the countable alarm

The published reward compares the actual full-world posteriors at two successive
retained histories. This module connects that countable coordinate sum with the
prefix-information increments used by the existing optimizer proof. Natural-log
and bit units, null records, convergence, and chronological discounts are explicit.
-/
noncomputable section
namespace IdExp.AlarmPanelPosterior
open AlarmPanel MeasureTheory Finset Set Filter Topology

/-- Expected KL of the new full-world posterior relative to the preceding one,
in nats. These are the actual posteriors of the full action-observation records. -/
def expectedInformationMovement (π : ValidCausalPolicy Action Observation) (n : ℕ) : ℝ :=
  ∑ h : CausalFiniteTrace Action Observation (n+1),
    priorSignalMass PulseBrierScore.prior (record π (n+1)) h *
      ∑' θ, CountableBrier.posterior PulseBrierScore.prior
        (record π (n+1)) (record_valid π (n+1)) h θ *
        Real.log (CountableBrier.posterior PulseBrierScore.prior
          (record π (n+1)) (record_valid π (n+1)) h θ /
          CountableBrier.posterior PulseBrierScore.prior
            (record π n) (record_valid π n) (Fin.init h) θ)

/-- Every positive-probability history has a summable literal posterior-KL
coordinate series. Null records have zero weight in the expected reward. -/
theorem informationMovement_history_summable (π : ValidCausalPolicy Action Observation)
    (n : ℕ) (h : CausalFiniteTrace Action Observation (n+1))
    (hh : 0 < priorSignalMass PulseBrierScore.prior (record π (n+1)) h) :
    Summable (fun θ => CountableBrier.posterior PulseBrierScore.prior
      (record π (n+1)) (record_valid π (n+1)) h θ *
      Real.log (CountableBrier.posterior PulseBrierScore.prior
        (record π (n+1)) (record_valid π (n+1)) h θ /
        CountableBrier.posterior PulseBrierScore.prior
          (record π n) (record_valid π n) (Fin.init h) θ)) := by
  have hj : 0 < priorSignalMass PulseBrierScore.prior (record π (n+1)) h *
      causalPrefixRule n h (Fin.init h) := by simpa [causalPrefixRule] using hh
  have he := CountablePosteriorKL.posteriorKL_summable
    PulseBrierScore.prior PulseInformation.mass_pos
    (record π (n+1)) (record_valid π (n+1))
    (causalPrefixRule n) (causalPrefixRule_mem_stochasticRules n) h (Fin.init h) hj
  have hp : finiteDecisionLaw (record π (n+1)) (causalPrefixRule n) = record π n :=
    causalFiniteExperiment_prefix π.1 π.2 response response_valid n
  simpa only [CountableBrier.posterior_apply, hp] using he

/-- A positive-probability posterior update cannot give positive mass to a
world assigned zero mass by its preceding posterior. -/
theorem informationMovement_history_support (π : ValidCausalPolicy Action Observation)
    (n : ℕ) (h : CausalFiniteTrace Action Observation (n+1))
    (hh : 0 < priorSignalMass PulseBrierScore.prior (record π (n+1)) h) (θ : World)
    (hz : CountableBrier.posterior PulseBrierScore.prior
      (record π n) (record_valid π n) (Fin.init h) θ = 0) :
    CountableBrier.posterior PulseBrierScore.prior
      (record π (n+1)) (record_valid π (n+1)) h θ = 0 := by
  have hj : 0 < priorSignalMass PulseBrierScore.prior (record π (n+1)) h *
      causalPrefixRule n h (Fin.init h) := by simpa [causalPrefixRule] using hh
  have hp : finiteDecisionLaw (record π (n+1)) (causalPrefixRule n) = record π n :=
    causalFiniteExperiment_prefix π.1 π.2 response response_valid n
  have he := CountablePosteriorKL.posteriorKL_support
    PulseBrierScore.prior PulseInformation.mass_pos
    (record π (n+1)) (record_valid π (n+1))
    (causalPrefixRule n) (causalPrefixRule_mem_stochasticRules n) h (Fin.init h) hj θ
  simp only [CountableBrier.posterior_apply, hp] at he
  simpa only [CountableBrier.posterior_apply] using
    he (by simpa only [CountableBrier.posterior_apply] using hz)

/-- The exact countable chain identity needed by the paper's information reward. -/
theorem expectedInformationMovement_eq (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    expectedInformationMovement π n = prefixInformation π (n+1) - prefixInformation π n := by
  have he := CountablePosteriorKL.information_gap_eq_expected_posteriorKL
    PulseBrierScore.prior PulseInformation.mass_pos
    (record π (n+1)) (record_valid π (n+1)) (causalPrefixRule n) (causalPrefixRule_mem_stochasticRules n)
  have hp : finiteDecisionLaw (record π (n+1)) (causalPrefixRule n) = record π n :=
    causalFiniteExperiment_prefix π.1 π.2 response response_valid n
  simp only [CountableBrier.posterior_apply, hp] at he
  simp only [causalPrefixRule, mul_ite, mul_one, mul_zero, ite_mul,
    zero_mul, sum_ite_eq', Finset.mem_univ, if_true] at he
  simpa only [expectedInformationMovement, CountableBrier.posterior_apply, prefixInformation] using he.symm

/-- Every literal expected information increment is nonnegative. -/
theorem expectedInformationMovement_nonneg (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    0 ≤ expectedInformationMovement π n := by
  rw [expectedInformationMovement_eq]
  apply sub_nonneg.mpr
  have he := infinitePriorInformation_mono_garbling PulseBrierScore.prior
    (record π (n+1)) (record_valid π (n+1)) (fun _ => measurable_of_countable _)
    (causalPrefixRule n) (causalPrefixRule_mem_stochasticRules n)
  have hp : finiteDecisionLaw (record π (n+1)) (causalPrefixRule n) = record π n :=
    causalFiniteExperiment_prefix π.1 π.2 response response_valid n
  rw [hp] at he
  exact he

/-- Actual successive posterior KL telescopes at every finite horizon. -/
theorem finite_information_movement_telescope (π : ValidCausalPolicy Action Observation) (N : ℕ) :
    (∑ n ∈ range N, expectedInformationMovement π n) = prefixInformation π N := by
  induction N with
  | zero => simp [AlarmPanelBayes.information_zero]
  | succ N ih =>
    rw [sum_range_succ, ih, expectedInformationMovement_eq]
    ring

/-- The complete nonnegative reward sum converges to the same two-bit value;
this is a sum of successive KL rewards, not KL to the original prior at each step. -/
theorem informationMovement_hasSum (π : ValidCausalPolicy Action Observation) :
    HasSum (expectedInformationMovement π) (2*Real.log 2) := by
  have hm : Monotone (prefixInformation π) := by
    apply monotone_nat_of_le_succ
    intro n
    have h := expectedInformationMovement_nonneg π n
    rw [expectedInformationMovement_eq] at h
    linarith
  have hb : BddAbove (Set.range (prefixInformation π)) :=
    ⟨2*Real.log 2, by rintro _ ⟨n,rfl⟩; exact prefixInformation_le π n⟩
  have ht : Tendsto (prefixInformation π) atTop (𝓝 (2*Real.log 2)) := by
    have h := tendsto_atTop_ciSup hm hb
    change Tendsto (prefixInformation π) atTop (𝓝 (completeInformation π)) at h
    simpa only [completeInformation_eq] using h
  apply (hasSum_iff_tendsto_nat_of_nonneg (expectedInformationMovement_nonneg π) _).2
  simpa only [finite_information_movement_telescope] using ht

/-- Literal geometrically discounted successive-posterior information, in bits. -/
def discountedInformationMovementBits (γ : ℝ) (π : ValidCausalPolicy Action Observation) : ℝ :=
  ∑' n, γ^n * (expectedInformationMovement π n / Real.log 2)

theorem discountedInformationMovementBits_eq (γ : ℝ)
    (π : ValidCausalPolicy Action Observation) :
    discountedInformationMovementBits γ π = discountedInformation γ π / Real.log 2 := by
  simp only [discountedInformationMovementBits, expectedInformationMovement_eq,
    discountedInformation, PrefixDiscount.value, ← mul_div_assoc, tsum_div_const]

/-- Every proper discounted literal return is a convergent real series. -/
theorem discountedInformationMovementBits_summable (γ : ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (π : ValidCausalPolicy Action Observation) :
    Summable (fun n => γ^n * (expectedInformationMovement π n / Real.log 2)) := by
  have hs : Summable (fun n => γ^n * expectedInformationMovement π n) := by
    apply Summable.of_nonneg_of_le
      (fun n => mul_nonneg (pow_nonneg hγ _) (expectedInformationMovement_nonneg π n))
      _ (informationMovement_hasSum π).summable
    intro n
    exact mul_le_of_le_one_left (expectedInformationMovement_nonneg π n)
      (pow_le_one₀ hγ hγ1)
  simpa only [mul_div_assoc] using hs.div_const (Real.log 2)

/-- Exact global optima of the literal discounted reward in the manuscript. -/
theorem discountedInformationMovementBits_maximizer_iff (γ : ℝ)
    (hγ : 0 < γ) (hγ1 : γ < 1) (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, discountedInformationMovementBits γ ρ ≤ discountedInformationMovementBits γ π) ↔
      inspectionProbability π.1 = 1 := by
  have hl : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  simp only [discountedInformationMovementBits_eq, div_le_div_iff_of_pos_right hl]
  constructor
  · intro h
    by_contra hs
    have hslt := lt_of_le_of_ne (inspectionProbability_le_one π.1 π.2) hs
    exact (not_lt_of_ge (h ⟨inspectPolicy,inspectPolicy_valid⟩))
      (discountedInformation_strict γ hγ hγ1 π hslt)
  · intro hs ρ
    rw [(discountedInformation_eq_iff γ hγ hγ1 π).2 hs]
    by_cases hr : inspectionProbability ρ.1 = 1
    · exact le_of_eq ((discountedInformation_eq_iff γ hγ hγ1 ρ).2 hr)
    · exact (discountedInformation_strict γ hγ hγ1 ρ
        (lt_of_le_of_ne (inspectionProbability_le_one ρ.1 ρ.2) hr)).le

/-- The complete undiscounted sum of literal KL rewards is two bits for every policy. -/
theorem completeInformationMovementBits_eq (π : ValidCausalPolicy Action Observation) :
    (∑' n, expectedInformationMovement π n / Real.log 2) = 2 := by
  rw [tsum_div_const, (informationMovement_hasSum π).tsum_eq]
  have hl : Real.log (2:ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  exact mul_div_cancel_right₀ 2 hl

end IdExp.AlarmPanelPosterior
