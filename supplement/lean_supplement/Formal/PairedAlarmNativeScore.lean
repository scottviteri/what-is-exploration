import Formal.PairedAlarmNativeAudit
import Formal.NativeCapabilitySelection

/-! The rich positive weighted native objective on the current paired interface.
Its maximizers are exactly the policies that inspect at startup with
probability one, and the startup-inspection coordinate gives an explicit
regret bound. Port of the native-score part of
`Formal.AlarmPanelNativeDiagnostic`; no alternating-interface theorem is used. -/
noncomputable section
namespace IdExp.PairedAlarm
open Finset Set Filter Topology

theorem eventual_inspection_loss (π : ValidCausalPolicy Action Observation) :
    eventualLoss response π (experiment inspectPolicy 1) = (1-inspectionProbability π.1)/2 := by
  have he : (fun t => finiteDeficiency (causalFiniteExperiment π.1 response t)
      (experiment inspectPolicy 1)) =ᶠ[atTop] (fun _ => (1-inspectionProbability π.1)/2) := by
    filter_upwards [eventually_ge_atTop 1] with t ht
    cases t with
    | zero => omega
    | succ n => exact inspection_deficiency_exact π.1 π.2 n
  exact tendsto_nhds_unique
    (tendsto_eventualLoss response response_valid π _
      (experiment_valid inspectPolicy inspectPolicy_valid 1))
    (tendsto_const_nhds.congr' he.symm)

def nativeWeightedObjective (ρ : ℕ → ℕ → ValidCausalPolicy Action Observation)
    (w : ℕ → ℝ) (π : ValidCausalPolicy Action Observation) : ℝ :=
  weightedProfileScore w (nativeCapabilityProfile response response_valid ρ π)

theorem nativeWeightedObjective_le_one (ρ : ℕ → ℕ → ValidCausalPolicy Action Observation)
    (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j) (π : ValidCausalPolicy Action Observation) :
    nativeWeightedObjective ρ w π ≤ 1 := by
  unfold nativeWeightedObjective weightedProfileScore weightedScore
  have hn : 0 ≤ ∑' j, w j * (nativeCapabilityProfile response response_valid ρ π j : ℝ) :=
    tsum_nonneg fun j =>
      mul_nonneg (hw j) (nativeCapabilityProfile response response_valid ρ π j).2.1
  linarith

theorem nativeWeightedObjective_eq_one_iff
    (ρ : ℕ → ℕ → ValidCausalPolicy Action Observation)
    (hρ : DenseRecordFamily response (fun n k => experiment (ρ n k).1 n))
    (w : ℕ → ℝ) (hw : ∀ j, 0 < w j) (hsum : Summable w)
    (π : ValidCausalPolicy Action Observation) :
    nativeWeightedObjective ρ w π = 1 ↔ inspectionProbability π.1 = 1 := by
  have hz : nativeWeightedObjective ρ w π = 1 ↔
      nativeCapabilityProfile response response_valid ρ π = zeroProfile := by
    constructor
    · intro he
      funext j
      apply Subtype.ext
      have hc := profile_coordinate_le_weighted_regret hw hsum
        (nativeCapabilityProfile response response_valid ρ π) j
      change (nativeCapabilityProfile response response_valid ρ π j : ℝ) ≤
        (1-nativeWeightedObjective ρ w π)/w j at hc
      rw [he] at hc
      norm_num at hc
      exact le_antisymm hc (nativeCapabilityProfile response response_valid ρ π j).2.1
    · intro he
      simp [nativeWeightedObjective, he]
  rw [hz, nativeCapabilityProfile_eq_zero_iff response response_valid ρ hρ,
    sufficient_iff_inspectionProbability_one π.1 π.2]

/-- The maximizers of the rich native score are exactly the policies with
startup inspection probability one, whatever their later continuation. -/
theorem nativeWeightedObjective_maximizer_iff
    (ρ : ℕ → ℕ → ValidCausalPolicy Action Observation)
    (hρ : DenseRecordFamily response (fun n k => experiment (ρ n k).1 n))
    (w : ℕ → ℝ) (hw : ∀ j, 0 < w j) (hsum : Summable w)
    (π : ValidCausalPolicy Action Observation) :
    (∀ σ, nativeWeightedObjective ρ w σ ≤ nativeWeightedObjective ρ w π) ↔
      inspectionProbability π.1 = 1 := by
  have href := (nativeWeightedObjective_eq_one_iff ρ hρ w hw hsum
    ⟨inspectPolicy,inspectPolicy_valid⟩).2 inspectPolicy_inspectionProbability
  constructor
  · intro hmax
    have he := hmax ⟨inspectPolicy,inspectPolicy_valid⟩
    rw [href] at he
    exact (nativeWeightedObjective_eq_one_iff ρ hρ w hw hsum π).1
      (le_antisymm (nativeWeightedObjective_le_one ρ w (fun j => (hw j).le) π) he)
  · intro hs σ
    rw [(nativeWeightedObjective_eq_one_iff ρ hρ w hw hsum π).2 hs]
    exact nativeWeightedObjective_le_one ρ w (fun j => (hw j).le) σ

/-- An explicit quantitative regret bound when the rich family literally
contains the startup inspection at coordinate `(1,k)`. -/
theorem nativeWeightedObjective_gap
    (ρ : ℕ → ℕ → ValidCausalPolicy Action Observation)
    (w : ℕ → ℝ) (hw : ∀ j, 0 < w j) (hsum : Summable w)
    (k : ℕ) (hk : ρ 1 k = ⟨inspectPolicy,inspectPolicy_valid⟩)
    (π : ValidCausalPolicy Action Observation) :
    nativeWeightedObjective ρ w π ≤ 1 - w (Nat.pair 1 k) * (1-inspectionProbability π.1)/2 := by
  have hc := profile_coordinate_le_weighted_regret hw hsum
    (nativeCapabilityProfile response response_valid ρ π) (Nat.pair 1 k)
  rw [nativeCapabilityProfile_pair, hk] at hc
  change eventualLoss response π (experiment inspectPolicy 1) ≤
    (1-nativeWeightedObjective ρ w π)/w (Nat.pair 1 k) at hc
  rw [eventual_inspection_loss] at hc
  have hb := (le_div_iff₀ (hw (Nat.pair 1 k))).mp hc
  nlinarith

end IdExp.PairedAlarm
