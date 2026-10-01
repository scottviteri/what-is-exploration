import Formal.AlarmPanelMultiStepChannel
import Formal.AlarmPanelEmpowermentAverage

/-!
# Expected-average empowerment for every fixed positive channel horizon

The same alarm/panel interface works for every `n ≥ 1`. Multi-step capacity is
computed from literal open-loop probes, then evaluated at actual visited histories
of arbitrary randomized causal policies. The limit below is proved from all finite
expected sums under the actual prior. No continuation or convergence premise is
supplied by the caller. Units are nats; divide by log 2 for the paper's bits.
-/
namespace IdExp.AlarmPanel.Control
open Finset Filter Topology
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

/-- Expected physical n-step sensor capacity at actual decision time t. -/
def multiStepStage (n : ℕ) (π : ValidCausalPolicy Action Observation) (θ : World) (t : ℕ) : ℝ :=
  ∑ w : CausalFiniteTrace Action Observation t,
    experiment π.1 t θ w * multiStepCapacity θ (List.ofFn w) n

theorem multiStepStage_zero (n : ℕ) (π : ValidCausalPolicy Action Observation) (θ : World) :
    multiStepStage n π θ 0 = multiStepCapacity θ [] n := by
  simp [multiStepStage, experiment, causalFiniteExperiment, causalTraceProb, causalTraceProbFrom]

theorem multiStepStage_succ (n : ℕ) (π : ValidCausalPolicy Action Observation)
    (θ : World) (t : ℕ) :
    multiStepStage (n + 1) π θ (t + 1) =
      if (t + 1 + n) % 2 = 1 then (1 - inspectionProbability π.1) * Real.log 2 else 0 := by
  have hl (w : CausalFiniteTrace Action Observation (t + 1)) :
      multiStepCapacity θ (List.ofFn w) (n + 1) =
        if (t + 1 + n) % 2 = 1 ∧ (w 0).1 ≠ 0 then Real.log 2 else 0 := by
    rw [multiStepCapacity_tail θ (List.ofFn w) (by simp)]
    simp only [List.length_ofFn, inspected_ofFn]
  simp only [multiStepStage, hl]
  by_cases ht : (t + 1 + n) % 2 = 1
  · simp only [ht, true_and, if_true]
    have hr := causalFiniteExperiment_root_action_mass response response_valid π t θ 0
    have hn := (experiment_valid π.1 π.2 (t + 1) θ).2
    have he : (∑ w : CausalFiniteTrace Action Observation (t + 1),
        if (w 0).1 ≠ 0 then experiment π.1 (t + 1) θ w else 0) = 1 - π.1 [] 0 := by
      have hs : (∑ w : CausalFiniteTrace Action Observation (t + 1),
          if (w 0).1 = 0 then experiment π.1 (t + 1) θ w else 0) +
          (∑ w : CausalFiniteTrace Action Observation (t + 1),
          if (w 0).1 ≠ 0 then experiment π.1 (t + 1) θ w else 0) =
          ∑ w : CausalFiniteTrace Action Observation (t + 1), experiment π.1 (t + 1) θ w := by
        rw [← sum_add_distrib]
        apply sum_congr rfl; intro w _
        by_cases ha : (w 0).1 = 0 <;> simp [ha]
      change (∑ w, if (w 0).1 = 0 then experiment π.1 (t + 1) θ w else 0) = _ at hr
      rw [hr, hn] at hs
      linarith
    calc
      _ = (∑ w : CausalFiniteTrace Action Observation (t + 1),
          if (w 0).1 ≠ 0 then experiment π.1 (t + 1) θ w else 0) * Real.log 2 := by
        simp only [sum_mul]
        apply sum_congr rfl; intro w _
        split_ifs <;> ring
      _ = _ := by rw [he]; rfl
  · simp [ht]

/-- Number of positive visited times whose probe ends at a panel.
`extra` is the probe length minus one; `H` is the visited reward horizon. -/
def terminalPanelCount (extra H : ℕ) : ℕ :=
  if extra % 2 = 0 then H / 2 else (H - 1) / 2

theorem terminalPanelCount_step (extra m : ℕ) :
    terminalPanelCount extra (m + 2) = terminalPanelCount extra (m + 1) +
      (if (m + 1 + extra) % 2 = 1 then 1 else 0) := by
  unfold terminalPanelCount
  split_ifs <;> omega

/-- Literal finite sum over the actual history law. -/
def multiStepFinite (n : ℕ) (π : ValidCausalPolicy Action Observation) (θ : World) (H : ℕ) : ℝ :=
  ∑ t ∈ Finset.range H, multiStepStage n π θ t

theorem multiStepFinite_eq (n m : ℕ) (π : ValidCausalPolicy Action Observation) (θ : World) :
    multiStepFinite (n + 1) π θ (m + 1) = multiStepCapacity θ [] (n + 1) +
      (terminalPanelCount n (m + 1) : ℝ) * (1 - inspectionProbability π.1) * Real.log 2 := by
  induction m with
  | zero => simp [multiStepFinite, multiStepStage_zero, terminalPanelCount]
  | succ m ih =>
    have hs : multiStepFinite (n + 1) π θ (m + 2) =
        multiStepFinite (n + 1) π θ (m + 1) + multiStepStage (n + 1) π θ (m + 1) := by
      simp [multiStepFinite, Finset.sum_range_succ]
    rw [hs, ih, multiStepStage_succ, terminalPanelCount_step]
    split_ifs <;> simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] <;> ring

/-- Actual world-prior integral, preserving the physical-channel conditioning. -/
def multiStepPriorFinite (n : ℕ) (π : ValidCausalPolicy Action Observation) (H : ℕ) : ℝ :=
  ∫ θ, multiStepFinite n π θ H ∂AlarmPanelPrior.prior

theorem multiStepPriorFinite_eq (n m : ℕ) (π : ValidCausalPolicy Action Observation) :
    multiStepPriorFinite (n + 1) π (m + 1) =
      (multiStepCapacity none [] (n + 1) + multiStepCapacity (some 0) [] (n + 1)) / 2 +
      (terminalPanelCount n (m + 1) : ℝ) * (1 - inspectionProbability π.1) * Real.log 2 := by
  unfold multiStepPriorFinite
  rw [AlarmPanelPrior.integral_none_some _ (by
    intro k
    rw [multiStepFinite_eq, multiStepFinite_eq, multiStepCapacity_root_some])]
  rw [multiStepFinite_eq, multiStepFinite_eq]
  ring

/-- Expected reward per visited decision, not capacity divided by probe length. -/
def multiStepPriorAverage (n : ℕ) (π : ValidCausalPolicy Action Observation) (H : ℕ) : ℝ :=
  multiStepPriorFinite n π H / (H : ℝ)

theorem shiftedPanelFraction_tendsto :
    Tendsto (fun m : ℕ => ((m / 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hc : Tendsto (fun m : ℕ => (1 : ℝ) / ((m + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).2 (tendsto_const_div_atTop_nhds_zero_nat _)
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub hc).sub panelFraction_tendsto
  have he (m : ℕ) : ((m / 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) =
      1 - 1 / ((m + 1 : ℕ) : ℝ) - (((m + 1) / 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) := by
    have hd : (m / 2 : ℕ) + (m + 1) / 2 = m := by omega
    have hdr : ((m / 2 : ℕ) : ℝ) + (((m + 1) / 2 : ℕ) : ℝ) = (m : ℝ) := by
      exact_mod_cast hd
    have hm : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    nlinarith
  simp_rw [he]
  convert h using 1 <;> norm_num

theorem terminalPanelFraction_tendsto (n : ℕ) :
    Tendsto (fun m : ℕ => (terminalPanelCount n (m + 1) : ℝ) / ((m + 1 : ℕ) : ℝ))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  by_cases hn : n % 2 = 0
  · simpa [terminalPanelCount, hn] using panelFraction_tendsto
  · simpa [terminalPanelCount, hn] using shiftedPanelFraction_tendsto

/-- The full sequence of actual finite expected averages converges, for each
fixed positive probe horizon; no parity subsequence or limit assumption. -/
theorem multiStepPriorAverage_tendsto (n : ℕ) (π : ValidCausalPolicy Action Observation) :
    Tendsto (multiStepPriorAverage (n + 1) π) atTop
      (𝓝 ((1 - inspectionProbability π.1) * Real.log 2 / 2)) := by
  apply (tendsto_add_atTop_iff_nat 1).1
  have hc : Tendsto (fun m : ℕ =>
      ((multiStepCapacity none [] (n + 1) + multiStepCapacity (some 0) [] (n + 1)) / 2) /
        ((m + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).2 (tendsto_const_div_atTop_nhds_zero_nat _)
  have hp := ((terminalPanelFraction_tendsto n).mul_const
    (1 - inspectionProbability π.1)).mul_const (Real.log 2)
  have h := hc.add hp
  convert h using 1
  · funext m
    rw [multiStepPriorAverage, multiStepPriorFinite_eq]
    ring
  · congr 1
    ring

/-- Limit of the actual finite expected averages at a fixed probe horizon. -/
def multiStepLongRunAverage (n : ℕ) (π : ValidCausalPolicy Action Observation) : ℝ :=
  limUnder atTop (multiStepPriorAverage n π)

theorem multiStepLongRunAverage_eq (n : ℕ) (π : ValidCausalPolicy Action Observation) :
    multiStepLongRunAverage (n + 1) π =
      (1 - inspectionProbability π.1) * Real.log 2 / 2 :=
  (multiStepPriorAverage_tendsto n π).limUnder_eq

theorem multiStepLongRunAverage_maximizer_iff (n : ℕ) (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, multiStepLongRunAverage (n + 1) ρ ≤ multiStepLongRunAverage (n + 1) π) ↔
      inspectionProbability π.1 = 0 := by
  simpa only [multiStepLongRunAverage_eq, longRunEmpowermentAverage_eq] using
    longRunEmpowermentAverage_maximizer_iff π

/-- End-to-end native failure at every positive channel horizon, with the same
world class, exact optimizer set, attained optimum, and arbitrary continuation. -/
theorem multiStep_all_positive_horizons (n : ℕ) (hn : 1 ≤ n) :
    (∃ π, ∀ ρ, multiStepLongRunAverage n ρ ≤ multiStepLongRunAverage n π) ∧
      ∀ π : ValidCausalPolicy Action Observation,
        (∀ ρ, multiStepLongRunAverage n ρ ≤ multiStepLongRunAverage n π) →
          (∀ t : ℕ, 1 ≤ t →
            finiteDeficiency (experiment π.1 t) (experiment inspectPolicy 1) = 1 / 2) ∧
          eventualInspectionDeficiency π = 1 / 2 ∧
          CausalFinitaryDominates response ⟨inspectPolicy, inspectPolicy_valid⟩ π ∧
          ¬ CausalFinitaryDominates response π ⟨inspectPolicy, inspectPolicy_valid⟩ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  refine ⟨⟨noveltyPolicy, (multiStepLongRunAverage_maximizer_iff m noveltyPolicy).2
    noveltyPolicy_root⟩, ?_⟩
  intro π hopt
  apply longRunEmpowermentAverage_all_optima_failure.2 π
  exact (longRunEmpowermentAverage_maximizer_iff π).2
    ((multiStepLongRunAverage_maximizer_iff m π).1 hopt)

end
end IdExp.AlarmPanel.Control
