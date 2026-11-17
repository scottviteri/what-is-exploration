import Formal.FiniteProbability

/-!
# Exact Bayesian prediction gain on a finite or countable world class

The history, action, and observed response are fixed. `q` is the preceding
posterior and `L` gives each world's likelihood of that same response. Only
posterior weights change when the observation is rescored. Real `tsum` permits
an arbitrary index type; the probability and bounded-likelihood hypotheses prove
summability, and so in particular cover both finite and countable world classes.
-/
namespace IdExp.BayesianPredictionGain
noncomputable section
variable {Θ : Type*}
attribute [local instance] Classical.propDecidable

def predictive (q L : Θ → ℝ) : ℝ := ∑' θ, q θ * L θ

def posterior (q L : Θ → ℝ) (θ : Θ) : ℝ := q θ * L θ / predictive q L

def gain (q L : Θ → ℝ) : ℝ :=
  Real.logb 2 ((∑' θ, posterior q L θ * L θ) / predictive q L)

/-- The realized posterior KL reward in bits, with zero-mass terms equal to zero. -/
def informationGain (q L : Θ → ℝ) : ℝ :=
  ∑' θ, posterior q L θ * Real.logb 2 (posterior q L θ / q θ)

theorem posterior_null (q L : Θ → ℝ) {θ : Θ} (h : q θ = 0) :
    posterior q L θ = 0 := by simp [posterior, h]

theorem likelihood_summable (q L : Θ → ℝ) (hq : Summable q)
    (hq0 : ∀ θ, 0 ≤ q θ) (hL0 : ∀ θ, 0 ≤ L θ) (hL1 : ∀ θ, L θ ≤ 1) :
    Summable (fun θ => q θ * L θ) := by
  apply Summable.of_nonneg_of_le (fun θ => mul_nonneg (hq0 θ) (hL0 θ)) _ hq
  intro θ
  exact mul_le_of_le_one_right (hq0 θ) (hL1 θ)

theorem squared_likelihood_summable (q L : Θ → ℝ) (hq : Summable q)
    (hq0 : ∀ θ, 0 ≤ q θ) (hL0 : ∀ θ, 0 ≤ L θ) (hL1 : ∀ θ, L θ ≤ 1) :
    Summable (fun θ => q θ * L θ ^ 2) := by
  apply likelihood_summable q (fun θ => L θ ^ 2) hq hq0 (fun θ => sq_nonneg _)
  intro θ
  nlinarith [hL0 θ, hL1 θ]

theorem posterior_summable (q L : Θ → ℝ) (hqL : Summable (fun θ => q θ * L θ)) :
    Summable (posterior q L) := hqL.div_const _

theorem posterior_nonneg (q L : Θ → ℝ) (hq0 : ∀ θ, 0 ≤ q θ)
    (hL0 : ∀ θ, 0 ≤ L θ) (θ : Θ) : 0 ≤ posterior q L θ := by
  exact div_nonneg (mul_nonneg (hq0 θ) (hL0 θ))
    (tsum_nonneg fun θ => mul_nonneg (hq0 θ) (hL0 θ))

theorem posterior_sum (q L : Θ → ℝ) (hz : predictive q L ≠ 0) :
    ∑' θ, posterior q L θ = 1 := by
  simp only [posterior, tsum_div_const]
  exact div_self hz

/-- The posterior-weighted likelihood is the old squared-likelihood average
normalized once. The context and response stay fixed. -/
theorem updated_probability_eq (q L : Θ → ℝ) :
    (∑' θ, posterior q L θ * L θ) =
      (∑' θ, q θ * L θ ^ 2) / predictive q L := by
  rw [← tsum_div_const]
  apply tsum_congr
  intro θ
  unfold posterior
  ring

theorem gain_eq_squared_likelihood (q L : Θ → ℝ) :
    gain q L = Real.logb 2 ((∑' θ, q θ * L θ ^ 2) / predictive q L ^ 2) := by
  rw [gain, updated_probability_eq, div_div, pow_two]

/-- The support restriction handles zero-prior worlds explicitly. -/
theorem renyi_summand_eq (q L : Θ → ℝ) (hq0 : ∀ θ, 0 ≤ q θ)
    (hz : predictive q L ≠ 0) (θ : Θ) :
    (if 0 < q θ then posterior q L θ ^ 2 / q θ else 0) =
      q θ * L θ ^ 2 / predictive q L ^ 2 := by
  split_ifs with hq
  · unfold posterior
    field_simp
  · have hzero : q θ = 0 := le_antisymm (not_lt.mp hq) (hq0 θ)
    simp [hzero]

theorem gain_eq_renyi (q L : Θ → ℝ) (hq0 : ∀ θ, 0 ≤ q θ)
    (hz : predictive q L ≠ 0) :
    gain q L = Real.logb 2
      (∑' θ, if 0 < q θ then posterior q L θ ^ 2 / q θ else 0) := by
  rw [gain_eq_squared_likelihood]
  congr 1
  simp_rw [renyi_summand_eq q L hq0 hz]
  exact tsum_div_const.symm

theorem renyi_summable (q L : Θ → ℝ) (hq : Summable q)
    (hq0 : ∀ θ, 0 ≤ q θ) (hL0 : ∀ θ, 0 ≤ L θ) (hL1 : ∀ θ, L θ ≤ 1)
    (hz : predictive q L ≠ 0) :
    Summable (fun θ => if 0 < q θ then posterior q L θ ^ 2 / q θ else 0) := by
  simp_rw [renyi_summand_eq q L hq0 hz]
  exact (squared_likelihood_summable q L hq hq0 hL0 hL1).div_const _

/-- A response with world-independent likelihood supplies no prediction gain. -/
theorem gain_eq_zero_of_constant (q L : Θ → ℝ) (hqsum : ∑' θ, q θ = 1)
    (c : ℝ) (hc : c ≠ 0) (hL : ∀ θ, q θ ≠ 0 → L θ = c) : gain q L = 0 := by
  have hprod : ∀ θ, q θ * L θ = q θ * c := by
    intro θ; by_cases h : q θ = 0
    · simp [h]
    · rw [hL θ h]
  have hz : predictive q L = c := by
    simp only [predictive, hprod, tsum_mul_right, hqsum, one_mul]
  have hp : posterior q L = q := by
    funext θ
    simp only [posterior, hprod, hz, mul_div_cancel_right₀ _ hc]
  simp only [gain, hp]
  change Real.logb 2 (predictive q L / predictive q L) = 0
  rw [hz, div_self hc, Real.logb_one]

/-- Prior mass of an answer cell. -/
def cellMass (q : Θ → ℝ) (s : Set Θ) : ℝ := ∑' θ, if θ ∈ s then q θ else 0

def cellLikelihood (s : Set Θ) (c : ℝ) (θ : Θ) : ℝ := if θ ∈ s then c else 0

theorem predictive_cell (q : Θ → ℝ) (s : Set Θ) (c : ℝ) :
    predictive q (cellLikelihood s c) = c * cellMass q s := by
  unfold predictive cellMass cellLikelihood
  rw [← tsum_mul_left]
  apply tsum_congr
  intro θ
  split_ifs <;> ring

theorem posterior_cell (q : Θ → ℝ) (s : Set Θ) (c : ℝ) (hc : c ≠ 0) (θ : Θ) :
    posterior q (cellLikelihood s c) θ = if θ ∈ s then q θ / cellMass q s else 0 := by
  rw [posterior, predictive_cell]
  unfold cellLikelihood
  split_ifs <;> simp_all [mul_div_mul_left, mul_comm]

theorem gain_cell (q : Θ → ℝ) (s : Set Θ) (c : ℝ) (hc : c ≠ 0)
    (hm : cellMass q s ≠ 0) :
    gain q (cellLikelihood s c) = -Real.logb 2 (cellMass q s) := by
  have hz : predictive q (cellLikelihood s c) ≠ 0 := by
    rw [predictive_cell]; exact mul_ne_zero hc hm
  have hnum : (∑' θ, posterior q (cellLikelihood s c) θ * cellLikelihood s c θ) = c := by
    have hterm : ∀ θ, posterior q (cellLikelihood s c) θ * cellLikelihood s c θ =
        posterior q (cellLikelihood s c) θ * c := by
      intro θ
      rw [posterior_cell q s c hc]
      unfold cellLikelihood
      split_ifs <;> simp
    simp_rw [hterm]
    rw [tsum_mul_right, posterior_sum q (cellLikelihood s c) hz, one_mul]
  rw [gain, hnum, predictive_cell]
  have hquot : c / (c * cellMass q s) = (cellMass q s)⁻¹ := by field_simp
  rw [hquot, Real.logb_inv]

theorem informationGain_cell (q : Θ → ℝ) (s : Set Θ) (c : ℝ) (hc : c ≠ 0)
    (hm : cellMass q s ≠ 0) :
    informationGain q (cellLikelihood s c) = -Real.logb 2 (cellMass q s) := by
  have hz : predictive q (cellLikelihood s c) ≠ 0 := by
    rw [predictive_cell]; exact mul_ne_zero hc hm
  have hterm : ∀ θ,
      posterior q (cellLikelihood s c) θ *
        Real.logb 2 (posterior q (cellLikelihood s c) θ / q θ) =
      posterior q (cellLikelihood s c) θ * (-Real.logb 2 (cellMass q s)) := by
    intro θ
    rw [posterior_cell q s c hc]
    split_ifs with hs
    · by_cases hq : q θ = 0
      · simp [hq]
      · have hr : q θ / cellMass q s / q θ = (cellMass q s)⁻¹ := by field_simp
        rw [hr, Real.logb_inv]
    · simp
  unfold informationGain
  simp_rw [hterm]
  rw [tsum_mul_right, posterior_sum q (cellLikelihood s c) hz, one_mul]

/-- Answer-cell updates have exactly the same realized PG and posterior KL. -/
theorem gain_eq_informationGain_of_cell (q : Θ → ℝ) (s : Set Θ) (c : ℝ)
    (hc : c ≠ 0) (hm : cellMass q s ≠ 0) :
    gain q (cellLikelihood s c) = informationGain q (cellLikelihood s c) := by
  rw [gain_cell q s c hc hm, informationGain_cell q s c hc hm]


/-- Sequential conditioning agrees with multiplying the two likelihoods. -/
theorem posterior_update (q A L : Θ → ℝ) (hA : predictive q A ≠ 0) :
    posterior (posterior q A) L = posterior q (fun θ => A θ * L θ) := by
  have hz : predictive (posterior q A) L =
      predictive q (fun θ => A θ * L θ) / predictive q A := by
    unfold predictive
    rw [← tsum_div_const]
    apply tsum_congr
    intro θ
    unfold posterior predictive
    ring
  funext θ
  simp only [posterior, hz]
  by_cases hS : predictive q (fun θ => A θ * L θ) = 0
  · simp [hS]
  · field_simp

/-- A world-independent factor in a record likelihood cancels from Bayes' rule. -/
theorem posterior_scale (q L : Θ → ℝ) (c : ℝ) (hc : c ≠ 0) :
    posterior q (fun θ => L θ * c) = posterior q L := by
  have hz : predictive q (fun θ => L θ * c) = predictive q L * c := by
    unfold predictive
    simp_rw [← mul_assoc]
    exact tsum_mul_right
  funext θ
  simp only [posterior, hz]
  simpa only [mul_assoc] using mul_div_mul_right (q θ * L θ) (predictive q L) hc

/-- The cell equality also holds on null events under the zero-reward convention. -/
theorem gain_eq_informationGain_cell_total (q : Θ → ℝ) (s : Set Θ) (c : ℝ) :
    gain q (cellLikelihood s c) = informationGain q (cellLikelihood s c) := by
  by_cases hc : c = 0
  · simp [gain, informationGain, posterior, predictive, cellLikelihood, hc]
  · by_cases hm : cellMass q s = 0
    · have hz : predictive q (cellLikelihood s c) = 0 := by rw [predictive_cell, hm, mul_zero]
      simp [gain, informationGain, posterior, hz]
    · exact gain_eq_informationGain_of_cell q s c hc hm

end
end IdExp.BayesianPredictionGain
