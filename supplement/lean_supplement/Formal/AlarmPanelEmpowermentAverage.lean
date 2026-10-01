import Formal.AlarmPanelUndiscounted
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Long-run average empowerment on the alarm/panel interface

The one-step physical sensor-channel capacities are summed over all visited
states before a finite horizon, integrated under the actual geometric prior,
and divided by that horizon. The full sequence of these expected averages
converges, not merely its odd-horizon subsequence. Its limit defines the
objective. There is no discount or finite reward cutoff.

All maximizers skip inspection, retain permanent inspection deficiency one
half, and are strictly finitarily dominated by inspection. Actual policies may
randomize and adapt at every history; no continuation is fixed in this proof.
-/

namespace IdExp.AlarmPanel.Control

open Filter Topology
noncomputable section

/-- Literal undiscounted sum of the first `H` expected visited capacities in a
fixed physical world. The action-channel horizon remains one step. -/
def empowermentFinite (π : ValidCausalPolicy Action Observation) (θ : World) (H : ℕ) : ℝ :=
  ∑ t ∈ Finset.range H, empowermentStage π θ t

theorem empowermentFinite_succ (π : ValidCausalPolicy Action Observation)
    (θ : World) (H : ℕ) :
    empowermentFinite π θ (H + 1) = empowermentFinite π θ H + empowermentStage π θ H := by
  simp only [empowermentFinite, Finset.sum_range_succ]

/-- At a positive horizon there are exactly `H / 2` panel ticks. -/
theorem empowermentFinite_eq_succ (π : ValidCausalPolicy Action Observation)
    (θ : World) (n : ℕ) :
    empowermentFinite π θ (n + 1) = localCapacity θ [] +
      (((n + 1) / 2 : ℕ) : ℝ) * (1 - inspectionProbability π.1) * Real.log 2 := by
  induction n with
  | zero => simp [empowermentFinite, empowermentStage_zero]
  | succ n ih =>
    rw [empowermentFinite_succ, ih, empowermentStage_succ]
    by_cases ho : (n + 1) % 2 = 1
    · have hd : (n + 1 + 1) / 2 = (n + 1) / 2 + 1 := by omega
      simp only [ho, if_true, hd, Nat.cast_add, Nat.cast_one,
        inspectionProbability, inspect]
      ring
    · have hd : (n + 1 + 1) / 2 = (n + 1) / 2 := by omega
      simp only [ho, if_false, hd, add_zero]

/-- Prior average of the actual finite visited-capacity sum. -/
def priorEmpowermentFinite (π : ValidCausalPolicy Action Observation) (H : ℕ) : ℝ :=
  ∫ θ, empowermentFinite π θ H ∂AlarmPanelPrior.prior

theorem priorEmpowermentFinite_eq_succ (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    priorEmpowermentFinite π (n + 1) =
      (localCapacity none [] + localCapacity (some 0) []) / 2 +
        (((n + 1) / 2 : ℕ) : ℝ) * (1 - inspectionProbability π.1) * Real.log 2 := by
  unfold priorEmpowermentFinite
  rw [AlarmPanelPrior.integral_none_some _ (by
    intro k
    rw [empowermentFinite_eq_succ, empowermentFinite_eq_succ]
    rfl)]
  rw [empowermentFinite_eq_succ, empowermentFinite_eq_succ]
  ring

/-- Finite expected reward per decision. The value at horizon zero is harmless
for the limit; every positive horizon has its literal arithmetic-mean meaning. -/
def priorEmpowermentAverage (π : ValidCausalPolicy Action Observation) (H : ℕ) : ℝ :=
  priorEmpowermentFinite π H / (H : ℝ)

/-- The panel-tick fraction tends to one half along every positive horizon. -/
theorem panelFraction_tendsto :
    Tendsto (fun n : ℕ => (((n + 1) / 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hr : Tendsto (fun n : ℕ => (((n + 1) % 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).2 (tendsto_mod_div_atTop_nhds_zero_nat (by norm_num : 0 < 2))
  have he (n : ℕ) : (((n + 1) / 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) =
      (1 - (((n + 1) % 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) / 2 := by
    have hd : (((n + 1) % 2 : ℕ) : ℝ) + 2 * (((n + 1) / 2 : ℕ) : ℝ) =
        ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.mod_add_div (n + 1) 2
    have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    nlinarith
  simp_rw [he]
  simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hr).div_const (2 : ℝ)

/-- The actual normalized finite sums converge along the full horizon sequence.
No parity restriction or supplied convergence assumption is used. -/
theorem priorEmpowermentAverage_tendsto (π : ValidCausalPolicy Action Observation) :
    Tendsto (priorEmpowermentAverage π) atTop
      (𝓝 ((1 - inspectionProbability π.1) * Real.log 2 / 2)) := by
  apply (tendsto_add_atTop_iff_nat 1).1
  have hc : Tendsto (fun n : ℕ =>
      ((localCapacity none [] + localCapacity (some 0) []) / 2) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).2 (tendsto_const_div_atTop_nhds_zero_nat _)
  have hp := (panelFraction_tendsto.mul_const (1 - inspectionProbability π.1)).mul_const
    (Real.log 2)
  have h := hc.add hp
  convert h using 1
  · funext n
    rw [priorEmpowermentAverage, priorEmpowermentFinite_eq_succ]
    ring
  · congr 1
    ring

/-- The long-run objective is the limit of the actual finite expected averages,
not a separately stipulated function of the startup probability. -/
def longRunEmpowermentAverage (π : ValidCausalPolicy Action Observation) : ℝ :=
  limUnder atTop (priorEmpowermentAverage π)

theorem longRunEmpowermentAverage_eq (π : ValidCausalPolicy Action Observation) :
    longRunEmpowermentAverage π = (1 - inspectionProbability π.1) * Real.log 2 / 2 :=
  (priorEmpowermentAverage_tendsto π).limUnder_eq

/-- All and only non-inspecting startup policies maximize the long-run average. -/
theorem longRunEmpowermentAverage_maximizer_iff
    (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, longRunEmpowermentAverage ρ ≤ longRunEmpowermentAverage π) ↔
      inspectionProbability π.1 = 0 := by
  rw [← priorEmpowermentTwo_maximizer_iff π]
  simp only [longRunEmpowermentAverage_eq, priorEmpowermentTwo_eq]
  constructor <;> intro h ρ <;> have hh := h ρ <;> linarith

theorem longRunEmpowermentAverage_attained :
    ∀ ρ, longRunEmpowermentAverage ρ ≤ longRunEmpowermentAverage noveltyPolicy :=
  (longRunEmpowermentAverage_maximizer_iff noveltyPolicy).2 noveltyPolicy_root

/-- Every optimizer of the literal undiscounted average has permanent native
loss, even though no finite reward cutoff or discount was used. -/
theorem longRunEmpowermentAverage_all_optima_failure :
    (∃ π, ∀ ρ, longRunEmpowermentAverage ρ ≤ longRunEmpowermentAverage π) ∧
      ∀ π : ValidCausalPolicy Action Observation,
        (∀ ρ, longRunEmpowermentAverage ρ ≤ longRunEmpowermentAverage π) →
          (∀ t : ℕ, 1 ≤ t →
            finiteDeficiency (experiment π.1 t) (experiment inspectPolicy 1) = 1 / 2) ∧
          eventualInspectionDeficiency π = 1 / 2 ∧
          CausalFinitaryDominates response ⟨inspectPolicy, inspectPolicy_valid⟩ π ∧
          ¬ CausalFinitaryDominates response π ⟨inspectPolicy, inspectPolicy_valid⟩ := by
  refine ⟨⟨noveltyPolicy, longRunEmpowermentAverage_attained⟩, ?_⟩
  intro π hopt
  apply priorEmpowermentTwo_all_optima_failure.2 π
  exact (priorEmpowermentTwo_maximizer_iff π).2
    ((longRunEmpowermentAverage_maximizer_iff π).1 hopt)

end
end IdExp.AlarmPanel.Control
