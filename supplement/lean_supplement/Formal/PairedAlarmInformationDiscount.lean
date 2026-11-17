import Formal.PairedAlarmInformationFinite
import Formal.PairedAlarmInformationComplete
import Formal.CountablePosteriorKL
import Formal.AlarmPanelPosteriorDiscount

/-!
# Proper-discount information and Brier returns on the paired alarm

For every fixed `0 < γ < 1`, the geometrically discounted information return
and the geometrically discounted ordinary Brier return
`Σ_{n≥0} γ^n E‖β_{n+1}-β_n‖²` are maximized exactly by the policies with startup
inspection probability `s = 1`. The complete undiscounted objectives still tie
all policies (`PairedAlarmInformationComplete`).

The information reward is the literal expected KL divergence of the new
full-world posterior from the preceding one,
`E[KL(β_{n+1} ‖ β_n)]`, a countable coordinate sum on every positive-probability
history. It equals the prefix-information increment `I(Θ;H_{n+1}) - I(Θ;H_n)`
(`expectedInformationMovement_eq`), in nats; the paper's bit-valued reward is
`discountedInformationMovementBits`. The Abel-summation step uses the generic
`IdExp.PrefixDiscount` lemmas about bounded real prefix values; no
alternating-interface theorem is applied to the paired response.
Optimization is done at each fixed `γ`; no limit `γ ↑ 1` is interchanged with it.
-/

noncomputable section
namespace IdExp.PairedAlarm.Information
open MeasureTheory Finset Set Filter Topology
open PulseBrierScore (prior)

/-! ## Discounted prefix-information and Brier returns -/

/-- Discounted information return `Σ_{n≥0} γ^n (I(Θ;H_{n+1}) - I(Θ;H_n))`, in nats. -/
def discountedInformation (γ : ℝ) (π : ValidCausalPolicy Action Observation) : ℝ :=
  PrefixDiscount.value γ (prefixInformation π)

/-- Discounted ordinary Brier return `Σ_{n≥0} γ^n E‖β_{n+1}-β_n‖²`. -/
def discountedBrier (γ : ℝ) (π : ValidCausalPolicy Action Observation) : ℝ :=
  ∑' n, γ^n * expectedMovement π n

theorem discountedBrier_eq (γ : ℝ) (π : ValidCausalPolicy Action Observation) :
    discountedBrier γ π = PrefixDiscount.value γ (prefixPotential π) := by
  simp only [discountedBrier, PrefixDiscount.value, expectedMovement_eq]

/-- For `0 ≤ γ ≤ 1` the discounted Brier series genuinely converges. -/
theorem discountedBrier_summable (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (π : ValidCausalPolicy Action Observation) :
    Summable (fun n => γ^n * expectedMovement π n) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (pow_nonneg hγ _) (expectedMovement_nonneg π n))
    _ (movement_hasSum π).summable
  intro n
  exact mul_le_of_le_one_left (expectedMovement_nonneg π n) (pow_le_one₀ hγ hγ1)

theorem discountedInformation_strict (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1)
    (π : ValidCausalPolicy Action Observation) (hs : inspectionProbability π.1 < 1) :
    discountedInformation γ π < discountedInformation γ inspectValid := by
  apply PrefixDiscount.value_strict γ (2*Real.log 2) hγ hγ1 _ _ (information_bounds π)
    (information_bounds inspectValid)
  · simp [information_zero]
  · exact finiteInformation_le π.1 π.2
  · exact finiteInformation_strict π.1 π.2 0 hs

theorem discountedBrier_strict (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1)
    (π : ValidCausalPolicy Action Observation) (hs : inspectionProbability π.1 < 1) :
    discountedBrier γ π < discountedBrier γ inspectValid := by
  rw [discountedBrier_eq, discountedBrier_eq]
  apply PrefixDiscount.value_strict γ 1 hγ hγ1 _ _ (potential_bounds π)
    (potential_bounds inspectValid)
  · simp [prefixPotential_zero]
  · exact finiteBrier_le π.1 π.2
  · exact finiteBrier_strict π.1 π.2 0 hs

theorem discountedInformation_eq_iff (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1)
    (π : ValidCausalPolicy Action Observation) :
    discountedInformation γ π = discountedInformation γ inspectValid ↔
      inspectionProbability π.1 = 1 := by
  constructor
  · intro he; by_contra hs
    exact (ne_of_lt (discountedInformation_strict γ hγ hγ1 π
      (lt_of_le_of_ne (inspectionProbability_le_one π.1 π.2) hs))) he
  · intro hs
    have he : prefixInformation π = prefixInformation inspectValid := by
      funext n; cases n with
      | zero => simp [information_zero]
      | succ n => exact (finiteInformation_eq_iff π.1 π.2 n).mpr hs
    simp only [discountedInformation, he]

theorem discountedBrier_eq_iff (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1)
    (π : ValidCausalPolicy Action Observation) :
    discountedBrier γ π = discountedBrier γ inspectValid ↔
      inspectionProbability π.1 = 1 := by
  constructor
  · intro he; by_contra hs
    exact (ne_of_lt (discountedBrier_strict γ hγ hγ1 π
      (lt_of_le_of_ne (inspectionProbability_le_one π.1 π.2) hs))) he
  · intro hs
    have he : prefixPotential π = prefixPotential inspectValid := by
      funext n; cases n with
      | zero => simp [prefixPotential_zero]
      | succ n => exact (finiteBrier_eq_iff π.1 π.2 n).mpr hs
    simp only [discountedBrier_eq, he]

/-- Exact global maximizers of the discounted information return, `0 < γ < 1`. -/
theorem discountedInformation_maximizer_iff (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1)
    (π : ValidCausalPolicy Action Observation) :
    (∀ ρ : ValidCausalPolicy Action Observation,
      discountedInformation γ ρ ≤ discountedInformation γ π) ↔
      inspectionProbability π.1 = 1 := by
  constructor
  · intro h
    by_contra hs
    exact not_lt_of_ge (h inspectValid) (discountedInformation_strict γ hγ hγ1 π
      (lt_of_le_of_ne (inspectionProbability_le_one π.1 π.2) hs))
  · intro hs ρ
    rw [(discountedInformation_eq_iff γ hγ hγ1 π).2 hs]
    by_cases hr : inspectionProbability ρ.1 = 1
    · exact le_of_eq ((discountedInformation_eq_iff γ hγ hγ1 ρ).2 hr)
    · exact (discountedInformation_strict γ hγ hγ1 ρ
        (lt_of_le_of_ne (inspectionProbability_le_one ρ.1 ρ.2) hr)).le

/-- Exact global maximizers of the discounted ordinary Brier return, `0 < γ < 1`. -/
theorem discountedBrier_maximizer_iff (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1)
    (π : ValidCausalPolicy Action Observation) :
    (∀ ρ : ValidCausalPolicy Action Observation,
      discountedBrier γ ρ ≤ discountedBrier γ π) ↔
      inspectionProbability π.1 = 1 := by
  constructor
  · intro h
    by_contra hs
    exact not_lt_of_ge (h inspectValid) (discountedBrier_strict γ hγ hγ1 π
      (lt_of_le_of_ne (inspectionProbability_le_one π.1 π.2) hs))
  · intro hs ρ
    rw [(discountedBrier_eq_iff γ hγ hγ1 π).2 hs]
    by_cases hr : inspectionProbability ρ.1 = 1
    · exact le_of_eq ((discountedBrier_eq_iff γ hγ hγ1 ρ).2 hr)
    · exact (discountedBrier_strict γ hγ hγ1 ρ
        (lt_of_le_of_ne (inspectionProbability_le_one ρ.1 ρ.2) hr)).le

/-- Every `s = 1` policy has a strictly larger discounted information return
than every `s < 1` policy. -/
theorem discountedInformation_lt_of_lt (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1)
    (π ρ : ValidCausalPolicy Action Observation)
    (hπ : inspectionProbability π.1 = 1) (hρ : inspectionProbability ρ.1 < 1) :
    discountedInformation γ ρ < discountedInformation γ π := by
  rw [(discountedInformation_eq_iff γ hγ hγ1 π).2 hπ]
  exact discountedInformation_strict γ hγ hγ1 ρ hρ

/-- Every `s = 1` policy has a strictly larger discounted Brier return than
every `s < 1` policy. -/
theorem discountedBrier_lt_of_lt (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1)
    (π ρ : ValidCausalPolicy Action Observation)
    (hπ : inspectionProbability π.1 = 1) (hρ : inspectionProbability ρ.1 < 1) :
    discountedBrier γ ρ < discountedBrier γ π := by
  rw [(discountedBrier_eq_iff γ hγ hγ1 π).2 hπ]
  exact discountedBrier_strict γ hγ hγ1 ρ hρ

/-! ## The literal successive-posterior information reward -/

/-- Expected KL of the new full-world posterior relative to the preceding one,
in nats. These are the actual posteriors of the full action-observation records. -/
def expectedInformationMovement (π : ValidCausalPolicy Action Observation) (n : ℕ) : ℝ :=
  ∑ h : CausalFiniteTrace Action Observation (n+1),
    priorSignalMass prior (record π (n+1)) h *
      ∑' θ, CountableBrier.posterior prior
        (record π (n+1)) (record_valid π (n+1)) h θ *
        Real.log (CountableBrier.posterior prior
          (record π (n+1)) (record_valid π (n+1)) h θ /
          CountableBrier.posterior prior
            (record π n) (record_valid π n) (Fin.init h) θ)

theorem record_prefix (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    finiteDecisionLaw (record π (n+1)) (causalPrefixRule n) = record π n :=
  causalFiniteExperiment_prefix π.1 π.2 response response_valid n

/-- Every positive-probability history has a summable literal posterior-KL
coordinate series. Null records have zero weight in the expected reward. -/
theorem informationMovement_history_summable (π : ValidCausalPolicy Action Observation)
    (n : ℕ) (h : CausalFiniteTrace Action Observation (n+1))
    (hh : 0 < priorSignalMass prior (record π (n+1)) h) :
    Summable (fun θ => CountableBrier.posterior prior
      (record π (n+1)) (record_valid π (n+1)) h θ *
      Real.log (CountableBrier.posterior prior
        (record π (n+1)) (record_valid π (n+1)) h θ /
        CountableBrier.posterior prior
          (record π n) (record_valid π n) (Fin.init h) θ)) := by
  have hj : 0 < priorSignalMass prior (record π (n+1)) h *
      causalPrefixRule n h (Fin.init h) := by simpa [causalPrefixRule] using hh
  have he := CountablePosteriorKL.posteriorKL_summable
    prior PulseInformation.mass_pos
    (record π (n+1)) (record_valid π (n+1))
    (causalPrefixRule n) (causalPrefixRule_mem_stochasticRules n) h (Fin.init h) hj
  simpa only [CountableBrier.posterior_apply, record_prefix] using he

/-- A positive-probability posterior update cannot give positive mass to a
world assigned zero mass by its preceding posterior. -/
theorem informationMovement_history_support (π : ValidCausalPolicy Action Observation)
    (n : ℕ) (h : CausalFiniteTrace Action Observation (n+1))
    (hh : 0 < priorSignalMass prior (record π (n+1)) h) (θ : World)
    (hz : CountableBrier.posterior prior
      (record π n) (record_valid π n) (Fin.init h) θ = 0) :
    CountableBrier.posterior prior
      (record π (n+1)) (record_valid π (n+1)) h θ = 0 := by
  have hj : 0 < priorSignalMass prior (record π (n+1)) h *
      causalPrefixRule n h (Fin.init h) := by simpa [causalPrefixRule] using hh
  have he := CountablePosteriorKL.posteriorKL_support
    prior PulseInformation.mass_pos
    (record π (n+1)) (record_valid π (n+1))
    (causalPrefixRule n) (causalPrefixRule_mem_stochasticRules n) h (Fin.init h) hj θ
  simp only [CountableBrier.posterior_apply, record_prefix] at he
  simpa only [CountableBrier.posterior_apply] using
    he (by simpa only [CountableBrier.posterior_apply] using hz)

/-- The exact countable chain identity: the expected successive-posterior KL is
the prefix-information increment. -/
theorem expectedInformationMovement_eq (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    expectedInformationMovement π n = prefixInformation π (n+1) - prefixInformation π n := by
  have he := CountablePosteriorKL.information_gap_eq_expected_posteriorKL
    prior PulseInformation.mass_pos
    (record π (n+1)) (record_valid π (n+1)) (causalPrefixRule n)
    (causalPrefixRule_mem_stochasticRules n)
  simp only [CountableBrier.posterior_apply, record_prefix] at he
  simp only [causalPrefixRule, mul_ite, mul_one, mul_zero, ite_mul,
    zero_mul, sum_ite_eq', Finset.mem_univ, if_true] at he
  simpa only [expectedInformationMovement, CountableBrier.posterior_apply,
    prefixInformation] using he.symm

/-- Every literal expected information increment is nonnegative. -/
theorem expectedInformationMovement_nonneg (π : ValidCausalPolicy Action Observation)
    (n : ℕ) : 0 ≤ expectedInformationMovement π n := by
  rw [expectedInformationMovement_eq]
  apply sub_nonneg.mpr
  have he := infinitePriorInformation_mono_garbling prior
    (record π (n+1)) (record_valid π (n+1)) (fun _ => measurable_of_countable _)
    (causalPrefixRule n) (causalPrefixRule_mem_stochasticRules n)
  rw [record_prefix] at he
  exact he

/-- Actual successive posterior KL telescopes at every finite horizon. -/
theorem finite_information_movement_telescope (π : ValidCausalPolicy Action Observation)
    (N : ℕ) : (∑ n ∈ range N, expectedInformationMovement π n) = prefixInformation π N := by
  induction N with
  | zero => simp [information_zero]
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

/-- The discounted prefix-information return is the discounted literal KL sum. -/
theorem discountedInformation_eq_tsum (γ : ℝ) (π : ValidCausalPolicy Action Observation) :
    discountedInformation γ π = ∑' n, γ^n * expectedInformationMovement π n := by
  simp only [discountedInformation, PrefixDiscount.value, expectedInformationMovement_eq]

/-- For `0 ≤ γ ≤ 1` the discounted information series genuinely converges. -/
theorem discountedInformation_summable (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (π : ValidCausalPolicy Action Observation) :
    Summable (fun n => γ^n * expectedInformationMovement π n) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (pow_nonneg hγ _) (expectedInformationMovement_nonneg π n))
    _ (informationMovement_hasSum π).summable
  intro n
  exact mul_le_of_le_one_left (expectedInformationMovement_nonneg π n) (pow_le_one₀ hγ hγ1)

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
  simpa only [mul_div_assoc] using
    (discountedInformation_summable γ hγ hγ1 π).div_const (Real.log 2)

/-- Exact global optima of the literal discounted successive-posterior KL reward
(in bits), for every fixed `0 < γ < 1`. -/
theorem discountedInformationMovementBits_maximizer_iff (γ : ℝ)
    (hγ : 0 < γ) (hγ1 : γ < 1) (π : ValidCausalPolicy Action Observation) :
    (∀ ρ : ValidCausalPolicy Action Observation,
      discountedInformationMovementBits γ ρ ≤ discountedInformationMovementBits γ π) ↔
      inspectionProbability π.1 = 1 := by
  have hl : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  simp only [discountedInformationMovementBits_eq, div_le_div_iff_of_pos_right hl]
  exact discountedInformation_maximizer_iff γ hγ hγ1 π

theorem discountedInformationMovementBits_lt_of_lt (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1)
    (π ρ : ValidCausalPolicy Action Observation)
    (hπ : inspectionProbability π.1 = 1) (hρ : inspectionProbability ρ.1 < 1) :
    discountedInformationMovementBits γ ρ < discountedInformationMovementBits γ π := by
  have hl : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  rw [discountedInformationMovementBits_eq, discountedInformationMovementBits_eq]
  exact div_lt_div_of_pos_right (discountedInformation_lt_of_lt γ hγ hγ1 π ρ hπ hρ) hl

/-- The complete undiscounted sum of literal KL rewards is two bits for every policy. -/
theorem completeInformationMovementBits_eq (π : ValidCausalPolicy Action Observation) :
    (∑' n, expectedInformationMovement π n / Real.log 2) = 2 := by
  rw [tsum_div_const, (informationMovement_hasSum π).tsum_eq]
  have hl : Real.log (2:ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  exact mul_div_cancel_right₀ 2 hl

/-- The discounted maxima are attained, by inspection, for every `0 < γ < 1`. -/
theorem discounted_maxima_attained (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1) :
    (∀ ρ : ValidCausalPolicy Action Observation,
      discountedInformationMovementBits γ ρ ≤ discountedInformationMovementBits γ inspectValid) ∧
    (∀ ρ : ValidCausalPolicy Action Observation,
      discountedInformation γ ρ ≤ discountedInformation γ inspectValid) ∧
    (∀ ρ : ValidCausalPolicy Action Observation,
      discountedBrier γ ρ ≤ discountedBrier γ inspectValid) :=
  ⟨(discountedInformationMovementBits_maximizer_iff γ hγ hγ1 inspectValid).2
      inspectPolicy_inspectionProbability,
    (discountedInformation_maximizer_iff γ hγ hγ1 inspectValid).2
      inspectPolicy_inspectionProbability,
    (discountedBrier_maximizer_iff γ hγ hγ1 inspectValid).2
      inspectPolicy_inspectionProbability⟩

end IdExp.PairedAlarm.Information
