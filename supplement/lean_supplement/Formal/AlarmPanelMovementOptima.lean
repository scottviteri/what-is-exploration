import Formal.AlarmPanelMovementSeries

/-! Global optimizer characterization for the literal Hellinger and Absolute
returns on the full alarm/panel policy class. -/
noncomputable section
namespace IdExp.AlarmPanelMovement
open AlarmPanel AlarmPanelVariance PosteriorMovement Finset

theorem weighted_summable {f : ℕ → ℝ} (hf : Summable f) (hn : ∀ k, 0 ≤ f k)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (e : ℕ → ℕ) :
    Summable (fun k => γ^(e k)*f k) := by
  apply Summable.of_nonneg_of_le (fun k => mul_nonneg (pow_nonneg hγ _) (hn k)) _ hf
  intro k
  exact mul_le_of_le_one_left (hn k) (pow_le_one₀ hγ hγ1)

def inspectValue (kind : Kind) (γ : ℝ) : ℝ :=
  fairReward kind + ∑' k, γ^(2*k+2)*inspectTerm kind k

def playValue (kind : Kind) (γ : ℝ) : ℝ := ∑' k, γ^(2*k+2)*playTerm kind k

theorem mode_gap (kind : Kind) (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    playValue kind γ < inspectValue kind γ := by
  have hi := weighted_summable (inspect_summable kind) (inspect_nonneg kind) γ hγ hγ1
    (fun k => 2*k+2)
  have hp := weighted_summable (play_summable kind) (fun k => (play_bounds kind k).1)
    γ hγ hγ1 (fun k => 2*k+2)
  have hb (k : ℕ) : γ^(2*k+2)*playTerm kind k - γ^(2*k+2)*inspectTerm kind k ≤
      penalty kind k := by
    calc _ = γ^(2*k+2)*(playTerm kind k-inspectTerm kind k) := by ring
      _ ≤ γ^(2*k+2)*penalty kind k :=
        mul_le_mul_of_nonneg_left (play_extra_le_penalty kind k) (pow_nonneg hγ _)
      _ ≤ penalty kind k := mul_le_of_le_one_left (penalty_nonneg kind k)
        (pow_le_one₀ hγ hγ1)
  have h := (hp.sub hi).tsum_le_tsum hb (penalty_summable kind)
  rw [hp.tsum_sub hi] at h
  have ht := penalty_sum_lt kind
  unfold playValue inspectValue
  linarith

theorem stage_nonneg (kind : Kind) (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    0 ≤ stage kind π n := by
  rcases n with _ | n
  · rw [stage_root]; exact mul_nonneg (inspectionProbability_nonneg π.1 π.2) (fair_bounds kind).1.le
  · rcases Nat.even_or_odd n with ⟨k,hk⟩ | ⟨k,hk⟩
    · rw [hk, show (k+k)+1=2*k+1 by omega, stage_panel]
    · rw [hk, show (2*k+1)+1=2*k+2 by omega, stage_monitor]
      exact add_nonneg
        (mul_nonneg (inspectionProbability_nonneg π.1 π.2) (inspect_nonneg kind k))
        (mul_nonneg (sub_nonneg.mpr (inspectionProbability_le_one π.1 π.2)) (play_bounds kind k).1)

theorem stage_summable (kind : Kind) (π : ValidCausalPolicy Action Observation) :
    Summable (stage kind π) := by
  apply (summable_nat_add_iff 1).1
  apply Summable.even_add_odd
  · simp only [stage_panel]; exact summable_zero
  · simp only [Nat.add_assoc, show (1:ℕ)+1=2 by decide, stage_monitor]
    exact ((inspect_summable kind).mul_left _).add ((play_summable kind).mul_left _)

/-- Discounted sums and the complete sum are finite for every policy. -/
theorem discounted_summable (kind : Kind) (π : ValidCausalPolicy Action Observation)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) : Summable (fun n => γ^n*stage kind π n) :=
  weighted_summable (stage_summable kind π) (stage_nonneg kind π) γ hγ hγ1 id

/-- Exact root mixture of the actual full-history expected return. -/
theorem discounted_eq (kind : Kind) (π : ValidCausalPolicy Action Observation)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    discounted kind γ π = inspectionProbability π.1 * inspectValue kind γ +
      (1-inspectionProbability π.1)*playValue kind γ := by
  have hi := weighted_summable (inspect_summable kind) (inspect_nonneg kind) γ hγ hγ1
    (fun k => 2*k+2)
  have hp := weighted_summable (play_summable kind) (fun k => (play_bounds kind k).1)
    γ hγ hγ1 (fun k => 2*k+2)
  have hm : Summable (fun k => γ^(2*k+2)*stage kind π (2*k+2)) := by
    simp only [stage_monitor, mul_add, mul_left_comm _ (inspectionProbability π.1),
      mul_left_comm _ (1-inspectionProbability π.1)]
    exact (hi.mul_left _).add (hp.mul_left _)
  have hz : Summable (fun k => γ^(2*k+1)*stage kind π (2*k+1)) := by
    simp only [stage_panel, mul_zero]; exact summable_zero
  have he := @tsum_even_add_odd ℝ _ _ _ _ (fun n => γ^(n+1)*stage kind π (n+1)) hz
    (by simpa only [Nat.add_assoc, show (1:ℕ)+1=2 by decide] using hm)
  simp only [stage_panel, mul_zero, tsum_zero, zero_add, Nat.add_assoc,
    show (1:ℕ)+1=2 by decide] at he
  have ht := (discounted_summable kind π γ hγ hγ1).sum_add_tsum_nat_add 1
  simp only [sum_range_one, pow_zero, one_mul] at ht
  rw [← he, stage_root] at ht
  simp only [stage_monitor, mul_add, mul_left_comm _ (inspectionProbability π.1),
    mul_left_comm _ (1-inspectionProbability π.1)] at ht
  rw [Summable.tsum_add (hi.mul_left _) (hp.mul_left _), tsum_mul_left, tsum_mul_left] at ht
  unfold discounted inspectValue playValue
  rw [← ht]
  ring

theorem discounted_le (kind : Kind) (π : ValidCausalPolicy Action Observation)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    discounted kind γ π ≤ inspectValue kind γ := by
  rw [discounted_eq kind π γ hγ hγ1]
  have hg := mode_gap kind γ hγ hγ1
  have hs := inspectionProbability_le_one π.1 π.2
  nlinarith

/-- Every optimum inspects initially; this includes all proper discounts and γ=1. -/
theorem discounted_eq_max_iff (kind : Kind) (π : ValidCausalPolicy Action Observation)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    discounted kind γ π = inspectValue kind γ ↔ inspectionProbability π.1 = 1 := by
  rw [discounted_eq kind π γ hγ hγ1]
  have hg := mode_gap kind γ hγ hγ1
  constructor
  · intro he; nlinarith
  · intro he; simp [he]

/-- Every reward optimum has zero inspection deficiency at every nonempty
finite prefix, uniformly over the countable world class. -/
theorem optimal_deficiency_zero (kind : Kind) (π : ValidCausalPolicy Action Observation)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hopt : discounted kind γ π = inspectValue kind γ) (n : ℕ) :
    finiteDeficiency (experiment π.1 (n+1)) (experiment inspectPolicy 1) = 0 := by
  rw [inspection_deficiency_exact π.1 π.2 n,
    (discounted_eq_max_iff kind π γ hγ hγ1).mp hopt]
  norm_num

end IdExp.AlarmPanelMovement
