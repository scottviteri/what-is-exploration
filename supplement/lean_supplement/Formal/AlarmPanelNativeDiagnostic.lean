import Formal.AlarmPanelNativeAudit
import Formal.NativeCapabilitySelection

/-! The restricted three-step diagnostic and the rich positive weighted
native objective have different completion guarantees on this same interface. -/
noncomputable section
namespace IdExp.AlarmPanel
open Finset Set Filter Topology

 def playPolicy : CausalPolicy Action Observation := detPolicy (fun _ => play0)
 theorem playPolicy_valid : IsCausalPolicy playPolicy := isCausalPolicy_detPolicy _
@[simp] theorem playPolicy_inspectionProbability : inspectionProbability playPolicy = 0 := by
  norm_num [inspectionProbability, playPolicy, detPolicy, play0, inspect]

 def diagnosticReplay (t : ℕ) (ht : 3 ≤ t) (h : CausalFiniteTrace Action Observation t) :=
   experiment playPolicy 3 (if (h ⟨2,by omega⟩).2 = 1 then some 0 else none)

 theorem diagnosticReplay_valid (t : ℕ) (ht : 3 ≤ t) : diagnosticReplay t ht ∈ stochasticRules _ _ := by
  intro h _
  exact experiment_valid playPolicy playPolicy_valid 3 _

 theorem diagnosticReplay_supported (π : CausalPolicy Action Observation) (θ : World)
    (t : ℕ) (ht : 3 ≤ t) (h : CausalFiniteTrace Action Observation t)
    (hh : experiment π t θ h ≠ 0) : diagnosticReplay t ht h = experiment playPolicy 3 θ := by
  have ho := supported_monitor π θ t 0 (by omega) h hh
  have hmon : MonitorEquivalent 3 (if (h ⟨2,by omega⟩).2 = 1 then some 0 else none) θ := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst k
    change (if (h ⟨2,by omega⟩).2 = 1 then some 0 else none) = some 0 ↔ θ = some 0
    change (h ⟨2,by omega⟩).2 = monitorLabel θ 0 at ho
    rw [ho]
    by_cases he : θ = some 0 <;> simp [monitorLabel, he]
  exact no_inspection_rows_eq playPolicy playPolicy_inspectionProbability 3 hmon

 theorem diagnosticReplay_law (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (t : ℕ) (ht : 3 ≤ t) :
    finiteDecisionLaw (experiment π t) (diagnosticReplay t ht) = experiment playPolicy 3 := by
  funext θ u
  unfold finiteDecisionLaw
  have he : ∀ h, experiment π t θ h * diagnosticReplay t ht h u =
      experiment π t θ h * experiment playPolicy 3 θ u := by
    intro h
    by_cases hh : experiment π t θ h = 0
    · simp [hh]
    · rw [diagnosticReplay_supported π θ t ht h hh]
  simp_rw [he]
  rw [← Finset.sum_mul, (experiment_valid π hπ t θ).2, one_mul]

/-- Every policy has already completed this restricted actual native target
at the first monitor tick, including policies permanently missing inspection. -/
 theorem diagnostic_deficiency_zero (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (t : ℕ) (ht : 3 ≤ t) : finiteDeficiency (experiment π t) (experiment playPolicy 3) = 0 := by
  apply le_antisymm
  · apply finiteDeficiency_le_of_decoder _ _ (diagnosticReplay t ht) (diagnosticReplay_valid t ht)
    intro θ
    apply le_of_eq
    apply (decodeErr_eq_zero_iff _ _ _ θ).2
    intro u
    exact congrFun (congrFun (diagnosticReplay_law π hπ t ht) θ) u
  · exact finiteDeficiency_nonneg_of_valid _ _ (experiment_valid π hπ t)
      (experiment_valid playPolicy playPolicy_valid 3)

 theorem eventual_inspection_loss (π : ValidCausalPolicy Action Observation) :
    eventualLoss response π (experiment inspectPolicy 1) = (1-inspectionProbability π.1)/2 := by
  have he : (fun t => finiteDeficiency (causalFiniteExperiment π.1 response t)
      (experiment inspectPolicy 1)) =ᶠ[atTop] (fun _ => (1-inspectionProbability π.1)/2) := by
    filter_upwards [eventually_ge_atTop 1] with t ht
    cases t with
    | zero => omega
    | succ n => exact inspection_deficiency_exact π.1 π.2 n
  exact tendsto_nhds_unique
    (tendsto_eventualLoss response response_valid π _ (experiment_valid inspectPolicy inspectPolicy_valid 1))
    (tendsto_const_nhds.congr' he.symm)

 def nativeWeightedObjective (ρ : ℕ → ℕ → ValidCausalPolicy Action Observation)
    (w : ℕ → ℝ) (π : ValidCausalPolicy Action Observation) : ℝ :=
   weightedProfileScore w (nativeCapabilityProfile response response_valid ρ π)

 theorem nativeWeightedObjective_le_one (ρ : ℕ → ℕ → ValidCausalPolicy Action Observation)
    (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j) (π : ValidCausalPolicy Action Observation) :
    nativeWeightedObjective ρ w π ≤ 1 := by
  unfold nativeWeightedObjective weightedProfileScore weightedScore
  have hn : 0 ≤ ∑' j, w j * (nativeCapabilityProfile response response_valid ρ π j : ℝ) :=
    tsum_nonneg fun j => mul_nonneg (hw j) (nativeCapabilityProfile response response_valid ρ π j).2.1
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

end IdExp.AlarmPanel
