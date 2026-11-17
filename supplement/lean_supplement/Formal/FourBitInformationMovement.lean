import Formal.FourBitNative

/-!
# Literal successive-posterior information in the four-bit example

The selected paper's information reward for one update compares the new
full-world posterior `p = β_t` with the preceding one `q = β_(t-1)`:
`r_info(q,p) = ∑_θ p(θ) log₂ (p(θ)/q(θ))`, with terms where `p(θ)=0`
contributing zero. This module identifies the expectation of that literal
reward on the actual sixteen-world records with the posterior-potential
increments whose optimizers `FourBitPosteriorControls` and `FourBitNative`
compute. Natural-log and bit units, null records, the support condition and the
finite support of the discounted series are explicit. The uniform prior, the
sixteen deterministic worlds and the unrestricted class of valid randomized
full-history policies are those of `FourBitPosterior`.
-/
noncomputable section
namespace IdExp.FourBitPosterior
open Finset ScheduledReveal

/-- Expected KL of the new full-world posterior from the preceding one, in nats:
`E[KL(β_(n+1) ‖ β_n)]`. The expectation uses the actual prior-mixture law of the
full action-observation record; the old posterior is evaluated at the retained
prefix `Fin.init h` of the new record `h`. -/
def expectedInformationMovement (π : Policy) (n : ℕ) : ℝ :=
  ∑ h : CausalFiniteTrace Action Observation (n+1),
    finiteBayesMass prior (record π (n+1)) h *
      finiteKL (posterior π (n+1) h) (posterior π n (Fin.init h))

/-- On every positive-probability record, the new posterior is absolutely
continuous with respect to the preceding posterior. Hence the literal reward
never meets a positive numerator over a zero denominator there. -/
theorem informationMovement_support (π : Policy) (n : ℕ)
    (h : CausalFiniteTrace Action Observation (n+1))
    (hh : 0 < finiteBayesMass prior (record π (n+1)) h) (θ : World)
    (hz : posterior π n (Fin.init h) θ = 0) :
    posterior π (n+1) h θ = 0 := by
  have hj : 0 < garbleJoint prior (record π (n+1)) (causalPrefixRule n) h (Fin.init h) := by
    simpa [garbleJoint, causalPrefixRule] using hh
  have hg : finiteDecisionLaw (record π (n+1)) (causalPrefixRule n) = record π n :=
    causalFiniteExperiment_prefix π.1 π.2 response (ScheduledReveal.response_valid signal) n
  exact posterior_garble_support prior prior_valid (record π (n+1)) (record_valid π (n+1))
    (causalPrefixRule n) (causalPrefixRule_mem_stochasticRules n) h (Fin.init h) hj θ
    (by rw [hg]; exact hz)

/-- On every positive-probability record, the conventional extended KL, which is
`⊤` for a positive numerator over a zero denominator, is finite and equals the
real-valued `finiteKL` used in this module. -/
theorem informationMovement_extended_eq (π : Policy) (n : ℕ)
    (h : CausalFiniteTrace Action Observation (n+1))
    (hh : 0 < finiteBayesMass prior (record π (n+1)) h) :
    finiteKLExtended (posterior π (n+1) h) (posterior π n (Fin.init h)) =
      (finiteKL (posterior π (n+1) h) (posterior π n (Fin.init h)) : EReal) := by
  unfold finiteKLExtended
  rw [if_pos (fun θ hz => informationMovement_support π n h hh θ hz)]

private theorem ereal_coe_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, EReal.coe_add, ih]

/-- Expected literal reward under the conventional extended-real KL convention:
`E[KL(β_(n+1) ‖ β_n)]` in `EReal`, with the actual record law as weights. -/
def expectedInformationMovementExtended (π : Policy) (n : ℕ) : EReal :=
  ∑ h : CausalFiniteTrace Action Observation (n+1),
    (finiteBayesMass prior (record π (n+1)) h : EReal) *
      finiteKLExtended (posterior π (n+1) h) (posterior π n (Fin.init h))

/-- The two zero conventions give the same expected reward: null records have
weight zero, and positive records satisfy the support condition. -/
theorem expectedInformationMovementExtended_eq (π : Policy) (n : ℕ) :
    expectedInformationMovementExtended π n = (expectedInformationMovement π n : EReal) := by
  rw [expectedInformationMovementExtended, expectedInformationMovement, ereal_coe_finset_sum]
  apply sum_congr rfl
  intro h _
  rcases (finiteBayesMass_nonneg prior (record π (n+1)) prior_valid.1
      (fun θ s => (record_valid π (n+1) θ).1 s) h).lt_or_eq with hpos | hzero
  · rw [informationMovement_extended_eq π n h hpos, ← EReal.coe_mul]
  · rw [← hzero]
    simp

/-- The information-potential increment is the literal expected KL divergence of
successive actual posteriors, in nats, including null records. -/
theorem information_increment_eq_posteriorKL (π : Policy) (n : ℕ) :
    prefixPotential .information π (n+1) - prefixPotential .information π n =
      ∑ h : CausalFiniteTrace Action Observation (n+1),
        finiteBayesMass prior (record π (n+1)) h *
          finiteKL (posterior π (n+1) h) (posterior π n (Fin.init h)) := by
  have hp (k : ℕ) : prefixPotential .information π k =
      finiteBayesInformation prior (record π k) - ent prior := by
    have hq : prefixPotential .information π k =
        finiteBayesPotential (fun p => -ent p) prior (record π k) := by
      unfold prefixPotential finiteBayesPotential finiteBayesMass
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro h _
      rw [sum_mul]
      apply sum_congr rfl
      intro θ _
      simp only [potential]
      ring
    rw [hq, finiteBayesInformation]
    simp only [finiteBayesPotential, mul_neg, sum_neg_distrib]
    ring
  have hg : finiteDecisionLaw (record π (n+1)) (causalPrefixRule n) = record π n :=
    causalFiniteExperiment_prefix π.1 π.2 response (ScheduledReveal.response_valid signal) n
  have he := information_gap_eq_expected_posteriorKL prior prior_valid
    (record π (n+1)) (record_valid π (n+1)) (causalPrefixRule n)
    (causalPrefixRule_mem_stochasticRules n)
  rw [hg] at he
  simp only [garbleJoint, causalPrefixRule, mul_ite, mul_one, mul_zero, ite_mul,
    zero_mul, sum_ite_eq', mem_univ, ↓reduceIte] at he
  rw [hp, hp]
  convert he using 1
  ring

theorem expectedInformationMovement_eq (π : Policy) (n : ℕ) :
    expectedInformationMovement π n =
      prefixPotential .information π (n+1) - prefixPotential .information π n :=
  (information_increment_eq_posteriorKL π n).symm

/-- After the third update no further posterior movement occurs. -/
theorem expectedInformationMovement_after_three (π : Policy) (n : ℕ) (hn : 3 ≤ n) :
    expectedInformationMovement π n = 0 := by
  rw [expectedInformationMovement_eq, control_after_three .information π n hn]

/-- Geometrically discounted literal successive-posterior KL reward, in nats.
The reward for the update from `β_n` to `β_(n+1)` has weight `γ^n`; `γ = 1` is
the complete undiscounted sum. -/
def informationKLObjective (γ : ℝ) (π : Policy) : ℝ :=
  ∑' n, γ^n * expectedInformationMovement π n

/-- The discounted series is an actual finite sum for every real `γ`, so its
`tsum` is never a junk value. -/
theorem informationKLObjective_hasSum (γ : ℝ) (π : Policy) :
    HasSum (fun n => γ^n * expectedInformationMovement π n)
      (∑ n ∈ range 3, γ^n * expectedInformationMovement π n) := by
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  rw [expectedInformationMovement_after_three π n
    (by simpa only [mem_range, not_lt] using hn), mul_zero]

theorem informationKLObjective_eq_controlObjective (γ : ℝ) (π : Policy) :
    informationKLObjective γ π = controlObjective .information γ π := by
  simp only [informationKLObjective, controlObjective, expectedInformationMovement_eq]

/-- Exact value of the literal objective: the initial mixture of the FULL value
`4 log 2` and the PARTIAL value `log 2 (1+γ+γ²)`. -/
theorem informationKLObjective_eq (γ : ℝ) (π : Policy) :
    informationKLObjective γ π = fullProbability π*(4*Real.log 2) +
      (1-fullProbability π)*(Real.log 2*(1+γ+γ^2)) := by
  rw [informationKLObjective_eq_controlObjective, controlObjective_eq]
  rfl

theorem informationKL_eq_max_iff (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (π : Policy) :
    informationKLObjective γ π = 4*Real.log 2 ↔ fullProbability π = 1 := by
  rw [informationKLObjective_eq_controlObjective]
  exact control_eq_max_iff .information γ hγ hγ1 π

/-- Exact global maximizers of the literal successive-posterior KL objective
over all valid randomized full-history policies, for `0 ≤ γ ≤ 1`. -/
theorem informationKL_maximizer_iff (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (π : Policy) :
    (∀ ρ : Policy, informationKLObjective γ ρ ≤ informationKLObjective γ π) ↔
      fullProbability π = 1 := by
  simp only [informationKLObjective_eq_controlObjective]
  exact control_maximizer_iff .information γ hγ hγ1 π

/-- The maximum of the literal objective is attained: the feasible always-FULL
fixed policy is a global maximizer for `0 ≤ γ ≤ 1`. -/
theorem informationKL_fullPolicy_maximizer (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    ∀ ρ : Policy, informationKLObjective γ ρ ≤ informationKLObjective γ (fixedPolicy true) :=
  (informationKL_maximizer_iff γ hγ hγ1 (fixedPolicy true)).mpr (by simp)

/-- Every global maximizer of the literal objective has zero deficiency to the
actual native one-step FULL experiment at every collection time `t ≥ 3`. -/
theorem informationKL_optimum_native_deficiency_zero (γ : ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (π : Policy)
    (hopt : ∀ ρ : Policy, informationKLObjective γ ρ ≤ informationKLObjective γ π)
    (n : ℕ) (hn : 3 ≤ n+1) :
    finiteDeficiency (record π (n+1)) fullTarget = 0 := by
  rw [native_deficiency_exact π n hn, (informationKL_maximizer_iff γ hγ hγ1 π).mp hopt]
  norm_num

/-- Every global maximizer has zero eventual FULL deficiency. -/
theorem informationKL_optimum_eventual_deficiency_zero (γ : ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (π : Policy)
    (hopt : ∀ ρ : Policy, informationKLObjective γ ρ ≤ informationKLObjective γ π) :
    sInf (Set.range (fun t => finiteDeficiency (record π t) fullTarget)) = 0 := by
  rw [eventual_native_deficiency, (informationKL_maximizer_iff γ hγ hγ1 π).mp hopt]
  norm_num

/-! ## The paper's bit-valued reward -/

/-- The paper's one-update information reward `r_info(q,p)` in bits, with the
old posterior `q` first and the new posterior `p` second. -/
def informationRewardBits (q p : World → ℝ) : ℝ :=
  ∑ θ, p θ * Real.logb 2 (p θ / q θ)

theorem informationRewardBits_eq (q p : World → ℝ) :
    informationRewardBits q p = finiteKL p q / Real.log 2 := by
  simp only [informationRewardBits, finiteKL, Real.logb, sum_div, mul_div_assoc]

/-- Expected literal bit reward `E[r_info(β_n, β_(n+1))]`. -/
def expectedInformationMovementBits (π : Policy) (n : ℕ) : ℝ :=
  ∑ h : CausalFiniteTrace Action Observation (n+1),
    finiteBayesMass prior (record π (n+1)) h *
      informationRewardBits (posterior π n (Fin.init h)) (posterior π (n+1) h)

theorem expectedInformationMovementBits_eq (π : Policy) (n : ℕ) :
    expectedInformationMovementBits π n = expectedInformationMovement π n / Real.log 2 := by
  simp only [expectedInformationMovementBits, expectedInformationMovement,
    informationRewardBits_eq, sum_div, mul_div_assoc]

def informationKLObjectiveBits (γ : ℝ) (π : Policy) : ℝ :=
  ∑' n, γ^n * expectedInformationMovementBits π n

theorem informationKLObjectiveBits_eq_div (γ : ℝ) (π : Policy) :
    informationKLObjectiveBits γ π = informationKLObjective γ π / Real.log 2 := by
  simp only [informationKLObjectiveBits, informationKLObjective,
    expectedInformationMovementBits_eq, ← mul_div_assoc, tsum_div_const]

/-- The paper's table row in bits: FULL earns `4`, PARTIAL earns `1+γ+γ²`. -/
theorem informationKLObjectiveBits_eq (γ : ℝ) (π : Policy) :
    informationKLObjectiveBits γ π =
      fullProbability π*4 + (1-fullProbability π)*(1+γ+γ^2) := by
  have hl : Real.log (2:ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [informationKLObjectiveBits_eq_div, informationKLObjective_eq, div_eq_iff hl]
  ring

theorem informationKLBits_eq_max_iff (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (π : Policy) :
    informationKLObjectiveBits γ π = 4 ↔ fullProbability π = 1 := by
  have hl : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  rw [informationKLObjectiveBits_eq_div, div_eq_iff (ne_of_gt hl)]
  exact informationKL_eq_max_iff γ hγ hγ1 π

theorem informationKLBits_maximizer_iff (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (π : Policy) :
    (∀ ρ : Policy, informationKLObjectiveBits γ ρ ≤ informationKLObjectiveBits γ π) ↔
      fullProbability π = 1 := by
  have hl : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  simp only [informationKLObjectiveBits_eq_div, div_le_div_iff_of_pos_right hl]
  exact informationKL_maximizer_iff γ hγ hγ1 π

/-- The bit-valued literal objective attains its maximum `4` at the feasible
always-FULL fixed policy for `0 ≤ γ ≤ 1`. -/
theorem informationKLBits_fullPolicy_maximizer (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    ∀ ρ : Policy,
      informationKLObjectiveBits γ ρ ≤ informationKLObjectiveBits γ (fixedPolicy true) :=
  (informationKLBits_maximizer_iff γ hγ hγ1 (fixedPolicy true)).mpr (by simp)

end IdExp.FourBitPosterior
