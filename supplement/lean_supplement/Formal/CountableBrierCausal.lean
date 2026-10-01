import Formal.CountableBrierStrictness
import Formal.CausalAverageScoreStrictness

/-! Actual policy-record Brier strictness on countable worlds. The compact
positive-atom specialization imposes no bound on Shannon entropy. -/
namespace IdExp.CountableBrier
open MeasureTheory Set
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 1000000
variable {Θ P A O : Type*} [Countable Θ] [MeasurableSpace Θ]
  [MeasurableSingletonClass Θ] [Fintype A] [Fintype O] [Nonempty A] [Nonempty O]
  (μ : Measure Θ) [IsProbabilityMeasure μ]

/-- Complete expected full-label Brier potential of literal causal records. -/
def causalTotalPotential (ps : Θ → CausalBehavior A O) (π : ValidCausalPolicy A O) : ℝ≥0∞ :=
  ⨆ n, ENNReal.ofReal (potential μ (causalBehaviorFiniteExperiment π.1 ps n)
    (causalBehaviorFiniteExperiment_valid π.1 π.2 ps n))

/-- Subtracting the prior potential gives the ordinary complete squared-posterior gain. -/
def causalCompleteGain (ps : Θ → CausalBehavior A O) (π : ValidCausalPolicy A O) : ℝ :=
  (causalTotalPotential μ ps π).toReal - (FullLabelBrierReport.ofMeasure μ).potential

theorem causalTotalPotential_le_one (ps : Θ → CausalBehavior A O)
    (π : ValidCausalPolicy A O) : causalTotalPotential μ ps π ≤ 1 :=
  totalPotential_le_one μ (causalFamilyFiniteProcess ps (fun _ => measurable_of_countable _) id) π

/-- The actual complete policy-history score has exactly the reverse-average equality condition. -/
theorem causalTotalPotential_eq_iff_reverse (ps : Θ → CausalBehavior A O)
    (π ρ : ValidCausalPolicy A O)
    (h : CausalBehaviorAverageFinitaryDominates μ ps π ρ) :
    causalTotalPotential μ ps π = causalTotalPotential μ ps ρ ↔
      CausalBehaviorAverageFinitaryDominates μ ps ρ π :=
  totalPotential_eq_iff_reverse μ
    (causalFamilyFiniteProcess ps (fun _ => measurable_of_countable _) id) h

/-- Any feasible family: the exact remaining obstruction to uniform strictness is order lifting. -/
theorem causalTotalPotential_uniform_strictness_iff [Nonempty Θ]
    (ps : Θ → CausalBehavior A O) (policies : P → ValidCausalPolicy A O) :
    StrictlyMonotoneFor
      (fun π ρ => CausalBehaviorFinitaryDominates ps (policies π) (policies ρ))
      (fun π => causalTotalPotential μ ps (policies π)) ↔
    ReverseDominanceLifts
      (fun π ρ => CausalBehaviorFinitaryDominates ps (policies π) (policies ρ))
      (fun π ρ => CausalBehaviorAverageFinitaryDominates μ ps (policies π) (policies ρ)) :=
  totalPotential_uniform_strictness_iff μ
    (causalFamilyFiniteProcess ps (fun _ => measurable_of_countable _) policies)

section Compact
variable [TopologicalSpace Θ] [T2Space Θ] [BorelSpace Θ] [CompactSpace Θ] [Nonempty Θ]

/-- Compact continuous countable worlds and positive atoms suffice for strictness;
finite prior entropy and existence of a sufficient policy are both unnecessary. -/
theorem causalTotalPotential_uniform_strict_of_compact_atoms
    (hp : ∀ θ, 0 < μ.real {θ}) (ps : Θ → CausalBehavior A O) (hps : Continuous ps)
    (policies : P → ValidCausalPolicy A O) :
    StrictlyMonotoneFor
      (fun π ρ => CausalBehaviorFinitaryDominates ps (policies π) (policies ρ))
      (fun π => causalTotalPotential μ ps (policies π)) := by
  apply (causalTotalPotential_uniform_strictness_iff μ ps policies).mpr
  intro π ρ _ hr
  exact (causalBehavior_averageDominates_iff_uniform_of_compact_atoms μ hp ps hps
    (policies ρ) (policies π)).mp hr

/-- The ordinary real-valued prior-subtracted Brier gain inherits the same strict comparison. -/
theorem causalCompleteGain_strict_of_compact_atoms
    (hp : ∀ θ, 0 < μ.real {θ}) (ps : Θ → CausalBehavior A O) (hps : Continuous ps)
    (π ρ : ValidCausalPolicy A O) (h : CausalBehaviorFinitaryDominates ps π ρ)
    (hn : ¬ CausalBehaviorFinitaryDominates ps ρ π) :
    causalCompleteGain μ ps ρ < causalCompleteGain μ ps π := by
  have hs := (causalTotalPotential_uniform_strict_of_compact_atoms μ hp ps hps id).2 π ρ h hn
  have hπ : causalTotalPotential μ ps π ≠ ⊤ :=
    ne_top_of_le_ne_top (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) (causalTotalPotential_le_one μ ps π)
  have hρ : causalTotalPotential μ ps ρ ≠ ⊤ :=
    ne_top_of_le_ne_top (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) (causalTotalPotential_le_one μ ps ρ)
  exact sub_lt_sub_right ((ENNReal.toReal_lt_toReal hρ hπ).mpr hs) _

end Compact
end
end IdExp.CountableBrier
