import Formal.PairedAlarmPseudoCountReturn
import Formal.PairedAlarmPseudoCountExpectation

/-!
# Continuing categorical pseudo-counts on the simultaneous alarm interface

The objective `J_H(π)` is the actual geometric-prior expectation, over worlds,
observations, and policy randomization, of every successive before/after
eight-label density bonus `1/√(N_h(o)+1)` in the full causal record of length
`H`, startup included. For each `H ≥ 64` its global maximum over all valid
randomized history policies is attained by a deterministic finite plan, and
every maximizer assigns zero probability to the startup inspection.

The complete nonnegative total and the ordinary expected time average are
different objectives: the former is infinite and the latter tends to zero for
every policy, so both tie all policies.
-/

namespace IdExp.PairedAlarm.PseudoCount
noncomputable section
open Finset Filter Topology IdExp.AlarmPanel.PseudoCountBounds

/-- `J_H(π) = E_{α,π} Σ_o S(N_H(o))`: the actual prior-expected `H`-step sum of the
continuing density-derived bonus. -/
def objective (H : ℕ) (π : ValidCausalPolicy Action Observation) : ℝ :=
  recordObjective π.1 H (fun w => densityReturn (archive w))

/-- The objective is literally the expectation of `Σ_o S(N_H(o))` over the eight labels. -/
theorem objective_eq_countReturn (H : ℕ) (π : ValidCausalPolicy Action Observation) :
    objective H π = recordObjective π.1 H (fun w => countReturn (archive w)) := by
  simp only [objective, densityReturn_eq_countReturn]

theorem objective_inspectBranch_le (H : ℕ) (π : ValidCausalPolicy Action Observation) :
    objective H ⟨inspectBranch π.1, inspectBranch_valid π.1 π.2⟩ ≤
      2 * Real.sqrt H + 2 := by
  apply recordObjective_le_of_support _ (inspectBranch_valid π.1 π.2) H
  intro θ w hw
  exact inspecting_densityReturn_le π.1 θ H w hw

theorem objective_alt_ge (H : ℕ) :
    countSum (H / 2 - 1) + countSum ((H - 1) / 2 - 1) ≤
      objective H ⟨altPolicy, altPolicy_valid⟩ := by
  apply le_recordObjective_of_support _ altPolicy_valid H
  intro θ w hw
  exact alt_densityReturn_ge θ H w hw

/-- For `H ≥ 64` the alternating-play witness strictly beats every inspection branch. -/
theorem objective_inspectBranch_lt_alt (H : ℕ) (hH : 64 ≤ H)
    (π : ValidCausalPolicy Action Observation) :
    objective H ⟨inspectBranch π.1, inspectBranch_valid π.1 π.2⟩ <
      objective H ⟨altPolicy, altPolicy_valid⟩ :=
  (objective_inspectBranch_le H π).trans_lt
    ((countSum_alternating_gap H hH).trans_le (objective_alt_ge H))

/-- Attainment is discharged by the finite causal-plan decomposition of the
literal record objective, not assumed as a separate optimization premise. -/
theorem objective_attained (H : ℕ) :
    ∃ τ : CausalPlan Action Observation H,
      ∀ ρ : ValidCausalPolicy Action Observation,
        objective H ρ ≤ objective H ⟨causalPolicyOfPlan H τ,
          isCausalPolicy_causalPolicyOfPlan H τ⟩ := by
  obtain ⟨τ, hτ⟩ := exists_maximizing_plan H (fun w => densityReturn (archive w))
  exact ⟨τ, fun ρ => hτ ρ.1 ρ.2⟩

/-- Every optimizer skips inspection at each scoring horizon at least 64.
This is only a necessary condition: play continuations can have different scores. -/
theorem objective_maximizer_skips_inspection (H : ℕ) (hH : 64 ≤ H)
    (π : ValidCausalPolicy Action Observation)
    (hopt : ∀ ρ : ValidCausalPolicy Action Observation, objective H ρ ≤ objective H π) :
    inspectionProbability π.1 = 0 := by
  cases H with
  | zero => omega
  | succ n =>
    let πI : ValidCausalPolicy Action Observation :=
      ⟨inspectBranch π.1, inspectBranch_valid π.1 π.2⟩
    let πP : ValidCausalPolicy Action Observation :=
      ⟨playBranch π.1, playBranch_valid π.1 π.2⟩
    have hm : objective (n+1) π =
        inspectionProbability π.1 * objective (n+1) πI +
        (1-inspectionProbability π.1) * objective (n+1) πP :=
      recordObjective_branch_mixture π.1 π.2 n (fun w => densityReturn (archive w))
    have hi : objective (n+1) πI ≤ 2 * Real.sqrt (n+1 : ℕ) + 2 :=
      objective_inspectBranch_le (n+1) π
    have hg : 2 * Real.sqrt (n+1 : ℕ) + 2 < objective (n+1) π :=
      (countSum_alternating_gap (n+1) hH).trans_le
        ((objective_alt_ge (n+1)).trans (hopt ⟨altPolicy, altPolicy_valid⟩))
    have hs0 := inspectionProbability_nonneg π.1 π.2
    have hs1 := inspectionProbability_le_one π.1 π.2
    have hmi := mul_le_mul_of_nonneg_left hi hs0
    have hmp := mul_le_mul_of_nonneg_left (hopt πP) (sub_nonneg.mpr hs1)
    have hgap : 0 < objective (n+1) π - (2 * Real.sqrt (n+1 : ℕ) + 2) := by linarith
    have hh : inspectionProbability π.1 *
        (objective (n+1) π - (2 * Real.sqrt (n+1 : ℕ) + 2)) ≤ 0 := by nlinarith
    have hz : inspectionProbability π.1 ≤ 0 := by
      by_contra hn
      have hp := mul_pos (lt_of_not_ge hn) hgap
      linarith
    exact le_antisymm hz hs0

/-- R4: for every integer `H ≥ 64`, `J_H` attains its global maximum over all valid
randomized history policies, and every maximizer has inspection probability zero. -/
theorem objective_large_horizon (H : ℕ) (hH : 64 ≤ H) :
    (∃ π : ValidCausalPolicy Action Observation,
      ∀ ρ : ValidCausalPolicy Action Observation, objective H ρ ≤ objective H π) ∧
    ∀ π : ValidCausalPolicy Action Observation,
      (∀ ρ : ValidCausalPolicy Action Observation, objective H ρ ≤ objective H π) →
        inspectionProbability π.1 = 0 := by
  obtain ⟨τ, hτ⟩ := objective_attained H
  exact ⟨⟨⟨causalPolicyOfPlan H τ, isCausalPolicy_causalPolicyOfPlan H τ⟩, hτ⟩,
    fun π hopt => objective_maximizer_skips_inspection H hH π hopt⟩

/-! ## Complete and long-run average returns tie every policy -/

/-- Every valid policy has the same distribution-free square-root growth envelope. -/
theorem objective_sqrt_bounds (H : ℕ) (π : ValidCausalPolicy Action Observation) :
    Real.sqrt H ≤ objective H π ∧ objective H π ≤ 2 * Real.sqrt (8 * H) := by
  constructor
  · apply le_recordObjective_of_support _ π.2 H
    intro θ w _
    simpa only [List.length_ofFn] using (densityReturn_sqrt_bounds (archive w)).1
  · apply recordObjective_le_of_support _ π.2 H
    intro θ w _
    simpa only [List.length_ofFn] using (densityReturn_sqrt_bounds (archive w)).2

theorem objective_nonneg (H : ℕ) (π : ValidCausalPolicy Action Observation) :
    0 ≤ objective H π := (Real.sqrt_nonneg H).trans (objective_sqrt_bounds H π).1

/-- Every actual expected partial sum diverges, regardless of exploration. -/
theorem objective_tendsto_atTop (π : ValidCausalPolicy Action Observation) :
    Tendsto (fun H : ℕ => objective H π) atTop atTop :=
  tendsto_atTop_mono (fun H => (objective_sqrt_bounds H π).1)
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

/-- Extended total of the nonnegative finite returns. -/
def completeObjective (π : ValidCausalPolicy Action Observation) : ENNReal :=
  ⨆ H : ℕ, ENNReal.ofReal (objective H π)

/-- The complete nonnegative objective ties every policy at infinity. -/
theorem completeObjective_eq_top (π : ValidCausalPolicy Action Observation) :
    completeObjective π = ⊤ := by
  by_contra hne
  obtain ⟨H, hH⟩ := ((objective_tendsto_atTop π).eventually
    (eventually_gt_atTop ((completeObjective π).toReal + 1))).exists
  have hu : ENNReal.ofReal (objective H π) ≤ completeObjective π :=
    le_iSup (fun n : ℕ => ENNReal.ofReal (objective n π)) H
  have hr := (ENNReal.ofReal_le_iff_le_toReal hne).mp hu
  linarith

/-- Ordinary expected time averages tie every policy at zero. -/
theorem objective_average_tendsto_zero (π : ValidCausalPolicy Action Observation) :
    Tendsto (fun H : ℕ => objective H π / H) atTop (𝓝 0) := by
  have hg : Tendsto (fun H : ℕ => (2 * Real.sqrt 8) / Real.sqrt H) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  apply squeeze_zero (fun H => div_nonneg (objective_nonneg H π) (by positivity)) _ hg
  intro H
  by_cases hz : H = 0
  · subst H; simp
  have hH : (0 : ℝ) < H := by exact_mod_cast Nat.pos_of_ne_zero hz
  have hs : 0 < Real.sqrt (H : ℝ) := Real.sqrt_pos.mpr hH
  have hu := div_le_div_of_nonneg_right (objective_sqrt_bounds H π).2 hH.le
  have he : 2 * Real.sqrt (8 * (H : ℝ)) / H = 2 * Real.sqrt 8 / Real.sqrt (H : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)]
    apply (div_eq_div_iff (ne_of_gt hH) (ne_of_gt hs)).2
    have h8 := Real.sqrt_nonneg 8
    nlinarith [Real.sq_sqrt hH.le]
  exact hu.trans_eq he

/-- R4, limiting objectives: complete totals diverge to `+∞` and long-run averages
`J_H/H` vanish, for every valid policy. -/
theorem limiting_objectives_tie (π : ValidCausalPolicy Action Observation) :
    Tendsto (fun H : ℕ => objective H π) atTop atTop ∧
      completeObjective π = ⊤ ∧
      Tendsto (fun H : ℕ => objective H π / H) atTop (𝓝 0) :=
  ⟨objective_tendsto_atTop π, completeObjective_eq_top π, objective_average_tendsto_zero π⟩

end
end IdExp.PairedAlarm.PseudoCount
