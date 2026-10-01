import Formal.AlarmPanelPseudoCountReturn
import Formal.AlarmPanelPseudoCountExpectation

/-!
# Continuing categorical pseudo-counts at arbitrarily large finite budgets

The objective is the actual geometric-prior expectation of every successive
before/after density bonus in the full causal record. For each T >= 64 its
maximum is attained by a deterministic finite plan, and every optimizer starts
without inspection. Arbitrary later actions retain native deficiency one half.

The complete nonnegative total and ordinary expected time average are different
objectives: the former is infinite and the latter zero for every policy.
-/
namespace IdExp.AlarmPanel.PseudoCount
noncomputable section
open Finset Filter Topology PseudoCountBounds

/-- Actual prior-expected T-step sum of the continuing density-derived bonus. -/
def objective (T : ℕ) (π : ValidCausalPolicy Action Observation) : ℝ :=
  recordObjective π.1 T (fun w => densityReturn (archive w))

theorem objective_inspectBranch_le (T : ℕ) (π : ValidCausalPolicy Action Observation) :
    objective T ⟨inspectBranch π.1, inspectBranch_valid π.1 π.2⟩ ≤
      2 * Real.sqrt T + 2 := by
  apply recordObjective_le_of_support _ (inspectBranch_valid π.1 π.2) T
  intro θ w hw
  exact inspecting_densityReturn_le π.1 θ T w hw

theorem objective_high_ge (T : ℕ) :
    countSum (T / 2) + countSum ((T - 1) / 2 - 1) ≤
      objective T ⟨highPolicy, highPolicy_valid⟩ := by
  apply le_recordObjective_of_support _ highPolicy_valid T
  intro θ w hw
  exact high_densityReturn_ge θ T w hw

/-- Attainment is discharged by the finite causal-plan decomposition of the
literal record objective, not assumed as a separate optimization premise. -/
theorem objective_attained (T : ℕ) :
    ∃ τ : CausalPlan Action Observation T,
      ∀ ρ : ValidCausalPolicy Action Observation,
        objective T ρ ≤ objective T ⟨causalPolicyOfPlan T τ,
          isCausalPolicy_causalPolicyOfPlan T τ⟩ := by
  obtain ⟨τ, hτ⟩ := exists_maximizing_plan T (fun w => densityReturn (archive w))
  exact ⟨τ, fun ρ => hτ ρ.1 ρ.2⟩

/-- Every optimizer skips inspection at each scoring horizon at least 64.
This is only a necessary condition: play continuations can have different scores. -/
theorem objective_maximizer_skips_inspection (T : ℕ) (hT : 64 ≤ T)
    (π : ValidCausalPolicy Action Observation)
    (hopt : ∀ ρ : ValidCausalPolicy Action Observation, objective T ρ ≤ objective T π) :
    inspectionProbability π.1 = 0 := by
  cases T with
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
      (countSum_large_horizon_gap (n+1) hT).trans_le
        ((objective_high_ge (n+1)).trans (hopt ⟨highPolicy, highPolicy_valid⟩))
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

/-- Literal all-optima failure, including attainment, every positive collection
time, arbitrary post-cutoff continuation, and a sufficient strict dominator. -/
theorem all_large_horizon_optima_fail (T : ℕ) (hT : 64 ≤ T) :
    (∃ π : ValidCausalPolicy Action Observation,
      ∀ ρ : ValidCausalPolicy Action Observation, objective T ρ ≤ objective T π) ∧
    CausalNativelySufficient response ⟨inspectPolicy, inspectPolicy_valid⟩ ∧
    ∀ π : ValidCausalPolicy Action Observation,
      (∀ ρ : ValidCausalPolicy Action Observation, objective T ρ ≤ objective T π) →
        inspectionProbability π.1 = 0 ∧
        (∀ t : ℕ, 0 < t → finiteDeficiency (experiment π.1 t)
          (experiment inspectPolicy 1) = 1 / 2) ∧
        CausalFinitaryDominates response ⟨inspectPolicy, inspectPolicy_valid⟩ π ∧
        ¬ CausalFinitaryDominates response π ⟨inspectPolicy, inspectPolicy_valid⟩ := by
  obtain ⟨τ, hτ⟩ := objective_attained T
  refine ⟨⟨⟨causalPolicyOfPlan T τ, isCausalPolicy_causalPolicyOfPlan T τ⟩, hτ⟩,
    inspection_natively_sufficient, ?_⟩
  intro π hopt
  have hs := objective_maximizer_skips_inspection T hT π hopt
  refine ⟨hs, ?_, inspection_strictly_dominates π.1 π.2 (by rw [hs]; norm_num)⟩
  intro t ht
  cases t with
  | zero => omega
  | succ n => rw [inspection_deficiency_exact π.1 π.2 n, hs]; norm_num

/-- Every valid policy has the same distribution-free square-root growth envelope. -/
theorem objective_sqrt_bounds (T : ℕ) (π : ValidCausalPolicy Action Observation) :
    Real.sqrt T ≤ objective T π ∧ objective T π ≤ 4 * Real.sqrt T := by
  constructor
  · apply le_recordObjective_of_support _ π.2 T
    intro θ w _
    simpa only [List.length_ofFn] using (densityReturn_sqrt_bounds (archive w)).1
  · apply recordObjective_le_of_support _ π.2 T
    intro θ w _
    rw [densityReturn_eq_countReturn]
    simpa only [List.length_ofFn] using countReturn_le_four_sqrt (archive w)

theorem objective_nonneg (T : ℕ) (π : ValidCausalPolicy Action Observation) :
    0 ≤ objective T π := (Real.sqrt_nonneg T).trans (objective_sqrt_bounds T π).1

/-- Every actual expected partial sum diverges, regardless of exploration. -/
theorem objective_tendsto_atTop (π : ValidCausalPolicy Action Observation) :
    Tendsto (fun T : ℕ => objective T π) atTop atTop :=
  tendsto_atTop_mono (fun T => (objective_sqrt_bounds T π).1)
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

/-- Extended total of the nonnegative finite returns. -/
def completeObjective (π : ValidCausalPolicy Action Observation) : ENNReal :=
  ⨆ T : ℕ, ENNReal.ofReal (objective T π)

/-- The complete nonnegative objective ties every policy at infinity. -/
theorem completeObjective_eq_top (π : ValidCausalPolicy Action Observation) :
    completeObjective π = ⊤ := by
  by_contra hne
  obtain ⟨T, hT⟩ := ((objective_tendsto_atTop π).eventually
    (eventually_gt_atTop ((completeObjective π).toReal + 1))).exists
  have hu : ENNReal.ofReal (objective T π) ≤ completeObjective π :=
    le_iSup (fun n : ℕ => ENNReal.ofReal (objective n π)) T
  have hr := (ENNReal.ofReal_le_iff_le_toReal hne).mp hu
  linarith

/-- Ordinary expected time averages tie every policy at zero. -/
theorem objective_average_tendsto_zero (π : ValidCausalPolicy Action Observation) :
    Tendsto (fun T : ℕ => objective T π / T) atTop (𝓝 0) := by
  have hg : Tendsto (fun T : ℕ => (4 : ℝ) / Real.sqrt T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  apply squeeze_zero (fun T => div_nonneg (objective_nonneg T π) (by positivity)) _ hg
  intro T
  by_cases hz : T = 0
  · subst T; simp
  have hT : (0 : ℝ) < T := by exact_mod_cast Nat.pos_of_ne_zero hz
  have hs : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.mpr hT
  have hu := div_le_div_of_nonneg_right (objective_sqrt_bounds T π).2 hT.le
  have he : 4 * Real.sqrt (T : ℝ) / T = 4 / Real.sqrt (T : ℝ) := by
    apply (div_eq_div_iff (ne_of_gt hT) (ne_of_gt hs)).2
    nlinarith [Real.sq_sqrt hT.le]
  exact hu.trans_eq he

end
end IdExp.AlarmPanel.PseudoCount
