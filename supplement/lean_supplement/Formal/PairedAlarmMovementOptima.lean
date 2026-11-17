import Formal.PairedAlarmMovementRewards
import Formal.AlarmPanelMovementOptima

/-!
# Optimizers of the Hellinger and Absolute returns on the paired alarm

Weights `γ^(t-1)` on step `t`, with startup weight one; alarm tick `k` is
scored at step `k+2`, weight `γ^(k+1)`. For every `0 ≤ γ ≤ 1` (in particular
every `0 < γ ≤ 1`, and the complete return at `γ = 1`), both literal returns are
summable for every valid randomized history policy and equal the root mixture
`s·J(I) + (1-s)·J(P)`, with `s = inspectionProbability π` and
`J(I) = fairReward + Σ_k γ^(k+1) inspectTerm k`,
`J(P) = Σ_k γ^(k+1) playTerm k`. PLAY's extra tick payment is at most the
summable envelope `AlarmPanelMovement.penalty` (exactly `p_k` for Absolute,
at most the paper's `u_k` for Hellinger), whose sum is strictly below
INSPECT's startup payment; weights in `[0,1]` preserve the bound. Hence the
maximum is attained and the maximizers are exactly the policies with `s = 1`.

The per-tick numbers `inspectTerm k`, `playTerm k` are the same
interface-independent numbers as in the alternating study, so their series
bounds are transported from `Formal.AlarmPanelMovementSeries` by `rfl`; no
alternating-interface response theorem is used.
-/

noncomputable section
namespace IdExp.PairedAlarm.Movement
open PosteriorMovement Finset
open AlarmPanelVariance (alarmMass silentMass alarmMass_pos silentMass_pos silentMass_eq)

/-! ### Interface-independent tick series -/

theorem inspectTerm_eq (kind : Kind) :
    inspectTerm kind = AlarmPanelMovement.inspectTerm kind := rfl

theorem playTerm_eq (kind : Kind) : playTerm kind = AlarmPanelMovement.playTerm kind := rfl

theorem play_bounds (kind : Kind) (k : ℕ) :
    0 ≤ playTerm kind k ∧ playTerm kind k ≤ 4 * alarmMass k :=
  AlarmPanelMovement.play_bounds kind k

theorem play_summable (kind : Kind) : Summable (playTerm kind) :=
  AlarmPanelMovement.play_summable kind

theorem inspect_summable (kind : Kind) : Summable (inspectTerm kind) :=
  AlarmPanelMovement.inspect_summable kind

theorem inspect_nonneg (kind : Kind) (k : ℕ) : 0 ≤ inspectTerm kind k :=
  AlarmPanelMovement.inspect_nonneg kind k

/-- PLAY's extra Absolute payment at tick `k` is exactly `p_k = a_k/S_k`. -/
theorem absolute_extra (k : ℕ) :
    playTerm .absolute k - inspectTerm .absolute k = alarmMass k / silentMass k := by
  have ha := alarmMass_pos k
  unfold playTerm inspectTerm binaryReward fairReward
  rw [silentMass_eq]
  field_simp
  ring

/-- PLAY's extra Hellinger payment at tick `k` is at most the paper's
`u_k = (3-2c)a_k - 1/4·1{k=0} - √2/16·1{k=1}`, with `c = 2-√2`. -/
theorem hellinger_extra_le (k : ℕ) :
    playTerm .hellinger k - inspectTerm .hellinger k ≤
      (3 - 2 * fairReward .hellinger) * alarmMass k - (if k = 0 then 1/4 else 0) -
        (if k = 1 then Real.sqrt 2 / 16 else 0) :=
  AlarmPanelMovement.play_extra_le_penalty .hellinger k

/-- PLAY's extra payment is below the summable nonnegative envelope. -/
theorem play_extra_le_penalty (kind : Kind) (k : ℕ) :
    playTerm kind k - inspectTerm kind k ≤ AlarmPanelMovement.penalty kind k :=
  AlarmPanelMovement.play_extra_le_penalty kind k

/-! ### Branch values and the uniform strict gap -/

/-- The INSPECT branch value `J_γ(I)`. -/
def inspectValue (kind : Kind) (γ : ℝ) : ℝ :=
  fairReward kind + ∑' k, γ^(k+1) * inspectTerm kind k

/-- The PLAY branch value `J_γ(P)`. -/
def playValue (kind : Kind) (γ : ℝ) : ℝ := ∑' k, γ^(k+1) * playTerm kind k

theorem inspect_weighted_summable (kind : Kind) (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    Summable (fun k => γ^(k+1) * inspectTerm kind k) :=
  AlarmPanelMovement.weighted_summable (inspect_summable kind) (inspect_nonneg kind)
    γ hγ hγ1 (fun k => k+1)

theorem play_weighted_summable (kind : Kind) (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    Summable (fun k => γ^(k+1) * playTerm kind k) :=
  AlarmPanelMovement.weighted_summable (play_summable kind) (fun k => (play_bounds kind k).1)
    γ hγ hγ1 (fun k => k+1)

/-- `J^Abs(I) = 1 + Σ_k γ^(k+1) T_k` with `T_k = 2a_k`. -/
theorem inspectValue_absolute (γ : ℝ) :
    inspectValue .absolute γ = 1 + ∑' k, γ^(k+1) * (2 * alarmMass k) := by
  simp [inspectValue, inspectTerm, fairReward]

/-- `J^Abs(P) = Σ_k γ^(k+1) 4a_k(1-p_k)` with `p_k = a_k/S_k`. -/
theorem playValue_absolute (γ : ℝ) :
    playValue .absolute γ =
      ∑' k, γ^(k+1) * (4 * alarmMass k * (1 - alarmMass k / silentMass k)) := by
  unfold playValue
  congr 1
  funext k
  have hs := silentMass_pos k
  simp only [playTerm, binaryReward]
  field_simp

/-- `J^Hel(I) = c + Σ_k γ^(k+1) c T_k` with `c = 2-√2` and `T_k = 2a_k`. -/
theorem inspectValue_hellinger (γ : ℝ) :
    inspectValue .hellinger γ =
      (2 - Real.sqrt 2) + ∑' k, γ^(k+1) * ((2 - Real.sqrt 2) * (2 * alarmMass k)) := by
  unfold inspectValue inspectTerm
  simp only [fairReward]
  congr 1
  congr 1
  funext k
  ring

/-- `J^Hel(P) = Σ_k γ^(k+1) S_k g_Hel(p_k)`. -/
theorem playValue_hellinger (γ : ℝ) :
    playValue .hellinger γ =
      ∑' k, γ^(k+1) * (silentMass k * binaryReward .hellinger (alarmMass k / silentMass k)) :=
  rfl

/-- INSPECT's branch strictly beats PLAY's for every weight `0 ≤ γ ≤ 1`. -/
theorem mode_gap (kind : Kind) (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    playValue kind γ < inspectValue kind γ := by
  have hi := inspect_weighted_summable kind γ hγ hγ1
  have hp := play_weighted_summable kind γ hγ hγ1
  have hb (k : ℕ) : γ^(k+1) * playTerm kind k - γ^(k+1) * inspectTerm kind k ≤
      AlarmPanelMovement.penalty kind k := by
    calc _ = γ^(k+1) * (playTerm kind k - inspectTerm kind k) := by ring
      _ ≤ γ^(k+1) * AlarmPanelMovement.penalty kind k :=
        mul_le_mul_of_nonneg_left (play_extra_le_penalty kind k) (pow_nonneg hγ _)
      _ ≤ AlarmPanelMovement.penalty kind k :=
        mul_le_of_le_one_left (AlarmPanelMovement.penalty_nonneg kind k) (pow_le_one₀ hγ hγ1)
  have h := (hp.sub hi).tsum_le_tsum hb (AlarmPanelMovement.penalty_summable kind)
  rw [hp.tsum_sub hi] at h
  have ht := AlarmPanelMovement.penalty_sum_lt kind
  unfold playValue inspectValue
  linarith

/-! ### Returns of every policy -/

theorem stage_nonneg (kind : Kind) (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    0 ≤ stage kind π n := by
  rcases n with _ | k
  · rw [stage_root]
    exact mul_nonneg (inspectionProbability_nonneg π.1 π.2)
      (AlarmPanelMovement.fair_bounds kind).1.le
  · rw [stage_tick]
    exact add_nonneg
      (mul_nonneg (inspectionProbability_nonneg π.1 π.2) (inspect_nonneg kind k))
      (mul_nonneg (sub_nonneg.mpr (inspectionProbability_le_one π.1 π.2))
        (play_bounds kind k).1)

theorem stage_summable (kind : Kind) (π : ValidCausalPolicy Action Observation) :
    Summable (stage kind π) := by
  apply (summable_nat_add_iff 1).1
  simp only [stage_tick]
  exact ((inspect_summable kind).mul_left _).add ((play_summable kind).mul_left _)

/-- The weighted reward series converges for every policy and every
`0 ≤ γ ≤ 1`; at `γ = 1` this is the complete return. -/
theorem discounted_summable (kind : Kind) (π : ValidCausalPolicy Action Observation)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) : Summable (fun n => γ^n * stage kind π n) :=
  AlarmPanelMovement.weighted_summable (stage_summable kind π) (stage_nonneg kind π) γ hγ hγ1 id

/-- Exact root mixture of the actual full-history expected return. -/
theorem discounted_eq (kind : Kind) (π : ValidCausalPolicy Action Observation)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    discounted kind γ π = inspectionProbability π.1 * inspectValue kind γ +
      (1 - inspectionProbability π.1) * playValue kind γ := by
  have hi := inspect_weighted_summable kind γ hγ hγ1
  have hp := play_weighted_summable kind γ hγ hγ1
  have ht := (discounted_summable kind π γ hγ hγ1).sum_add_tsum_nat_add 1
  simp only [sum_range_one, pow_zero, one_mul, stage_root, stage_tick, mul_add,
    mul_left_comm _ (inspectionProbability π.1),
    mul_left_comm _ (1 - inspectionProbability π.1)] at ht
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

/-- Equality with INSPECT's value holds exactly at root inspection probability one. -/
theorem discounted_eq_max_iff (kind : Kind) (π : ValidCausalPolicy Action Observation)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    discounted kind γ π = inspectValue kind γ ↔ inspectionProbability π.1 = 1 := by
  rw [discounted_eq kind π γ hγ hγ1]
  have hg := mode_gap kind γ hγ hγ1
  constructor
  · intro he; nlinarith
  · intro he; simp [he]

/-! ### Attainment and the optimizer set -/

/-- The pure policy that always inspects. -/
def inspectWitness : ValidCausalPolicy Action Observation :=
  ⟨detPolicy (fun _ => inspect), isCausalPolicy_detPolicy _⟩

theorem inspectWitness_probability : inspectionProbability inspectWitness.1 = 1 := by
  simp [inspectWitness, inspectionProbability, detPolicy]

theorem discounted_inspectWitness (kind : Kind) (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    discounted kind γ inspectWitness = inspectValue kind γ :=
  (discounted_eq_max_iff kind inspectWitness γ hγ hγ1).mpr inspectWitness_probability

/-- The maximum over all valid randomized history policies is attained, and
equals INSPECT's branch value. -/
theorem isGreatest_discounted (kind : Kind) (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    IsGreatest (Set.range (discounted kind γ)) (inspectValue kind γ) :=
  ⟨⟨inspectWitness, discounted_inspectWitness kind γ hγ hγ1⟩,
    by rintro _ ⟨ρ, rfl⟩; exact discounted_le kind ρ γ hγ hγ1⟩

/-- Optimizer characterization for either published reward and every
`0 ≤ γ ≤ 1`: a policy maximizes the return iff it inspects at startup with
probability one. -/
theorem isMaximizer_iff (kind : Kind) (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (π : ValidCausalPolicy Action Observation) :
    (∀ ρ : ValidCausalPolicy Action Observation, discounted kind γ ρ ≤ discounted kind γ π) ↔
      inspectionProbability π.1 = 1 := by
  rw [← discounted_eq_max_iff kind π γ hγ hγ1]
  constructor
  · intro h
    exact le_antisymm (discounted_le kind π γ hγ hγ1)
      ((discounted_inspectWitness kind γ hγ hγ1).symm.le.trans (h inspectWitness))
  · intro h ρ
    rw [h]
    exact discounted_le kind ρ γ hγ hγ1

/-! ### The complete undiscounted return (`γ = 1`) -/

theorem complete_summable (kind : Kind) (π : ValidCausalPolicy Action Observation) :
    Summable (stage kind π) :=
  stage_summable kind π

theorem complete_eq (kind : Kind) (π : ValidCausalPolicy Action Observation) :
    complete kind π = inspectionProbability π.1 * inspectValue kind 1 +
      (1 - inspectionProbability π.1) * playValue kind 1 := by
  rw [complete_eq_discounted_one, discounted_eq kind π 1 zero_le_one le_rfl]

theorem complete_isMaximizer_iff (kind : Kind) (π : ValidCausalPolicy Action Observation) :
    (∀ ρ : ValidCausalPolicy Action Observation, complete kind ρ ≤ complete kind π) ↔
      inspectionProbability π.1 = 1 := by
  simp only [complete_eq_discounted_one]
  exact isMaximizer_iff kind 1 zero_le_one le_rfl π

end IdExp.PairedAlarm.Movement
