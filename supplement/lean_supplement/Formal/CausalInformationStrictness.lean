import Formal.ExtendedInformationStrictness
import Formal.CompactPriorAverageComparison
import Formal.CausalBehaviorCapability
import Formal.CausalInformationAdmissibility

/-!
# Information strictness for actual controlled-prefix policy records

These wrappers instantiate the growing experiments with literal randomized
policy action-observation records, discharging validity, measurability and
prefix refinement. The feasible policy family is arbitrary. Core results need
only measurable behavior masses; the positive-atom corollary adds compactness
and continuity in the canonical controlled-prefix topology.
-/
namespace IdExp
open MeasureTheory Set Finset Filter Topology
open scoped ENNReal
noncomputable section
set_option linter.unusedSectionVars false

variable {Θ P A O : Type*} [MeasurableSpace Θ]
  [Fintype A] [Fintype O] [Nonempty A] [Nonempty O]

/-- Actual growing experiments for any chosen feasible family of valid policies. -/
def causalFamilyFiniteProcess (ps : Θ → CausalBehavior A O)
    (hm : ∀ h, Measurable (fun θ => (ps θ).mass h))
    (policies : P → ValidCausalPolicy A O) :
    MeasurableFiniteProcess Θ P (CausalFiniteTrace A O) where
  experiment := fun π n => causalBehaviorFiniteExperiment (policies π).1 ps n
  valid := fun π n => causalBehaviorFiniteExperiment_valid _ (policies π).2 ps n
  measurable := fun π n x => by
    change Measurable (fun θ => causalPolicyProb (policies π).1 (List.ofFn x) *
      (ps θ).mass (List.ofFn x))
    exact (hm _).const_mul _
  refines := fun π m n hmn => by
    rw [causalBehaviorFiniteExperiment_eq_toResponse, causalBehaviorFiniteExperiment_eq_toResponse]
    exact causalFiniteExperiment_prefix_blackwell_of_le _ (policies π).2 _
      (causalBehaviorResponsePresentation_valid ps) hmn

/-- The prior averages conditional simulation errors of one common decoder. -/
def CausalBehaviorAverageFinitaryDominates (μ : Measure Θ)
    (ps : Θ → CausalBehavior A O) (π ρ : ValidCausalPolicy A O) : Prop :=
  ∀ n ε, 0 < ε → ∃ T, ∀ t, T ≤ t → priorAverageDeficiency μ
    (causalBehaviorFiniteExperiment π.1 ps t) (causalBehaviorFiniteExperiment ρ.1 ps n) < ε

/-- Complete mutual information of literal action-observation records, in nats. -/
def causalBehaviorTotalInformation (μ : Measure Θ)
    (ps : Θ → CausalBehavior A O) (π : ValidCausalPolicy A O) : ℝ≥0∞ :=
  ⨆ n, ENNReal.ofReal (infinitePriorInformation μ (causalBehaviorFiniteExperiment π.1 ps n))

@[simp] theorem causalFamilyFiniteProcess_uniformDominates_iff
    (ps : Θ → CausalBehavior A O) (hm : ∀ h, Measurable (fun θ => (ps θ).mass h))
    (policies : P → ValidCausalPolicy A O) (π ρ : P) :
    (causalFamilyFiniteProcess ps hm policies).UniformDominates π ρ ↔
      CausalBehaviorFinitaryDominates ps (policies π) (policies ρ) := Iff.rfl

@[simp] theorem causalFamilyFiniteProcess_averageDominates_iff
    (μ : Measure Θ) (ps : Θ → CausalBehavior A O)
    (hm : ∀ h, Measurable (fun θ => (ps θ).mass h))
    (policies : P → ValidCausalPolicy A O) (π ρ : P) :
    (causalFamilyFiniteProcess ps hm policies).AverageDominates μ π ρ ↔
      CausalBehaviorAverageFinitaryDominates μ ps (policies π) (policies ρ) := Iff.rfl

@[simp] theorem causalFamilyFiniteProcess_totalInformation
    (μ : Measure Θ) (ps : Θ → CausalBehavior A O)
    (hm : ∀ h, Measurable (fun θ => (ps θ).mass h))
    (policies : P → ValidCausalPolicy A O) (π : P) :
    (causalFamilyFiniteProcess ps hm policies).totalInformation μ π =
      causalBehaviorTotalInformation μ ps (policies π) := rfl

/-- Actual finite-information equality detects exactly reverse average recovery. -/
theorem causalBehavior_information_eq_iff_reverse_average
    (μ : Measure Θ) [IsProbabilityMeasure μ] (ps : Θ → CausalBehavior A O)
    (hm : ∀ h, Measurable (fun θ => (ps θ).mass h))
    (π ρ : ValidCausalPolicy A O)
    (hb : causalBehaviorTotalInformation μ ps π ≠ ⊤)
    (h : CausalBehaviorAverageFinitaryDominates μ ps π ρ) :
    causalBehaviorTotalInformation μ ps π = causalBehaviorTotalInformation μ ps ρ ↔
      CausalBehaviorAverageFinitaryDominates μ ps ρ π :=
  (causalFamilyFiniteProcess ps hm id).totalInformation_eq_iff_averageDominates_reverse μ hb h

/-- The finite-prefix reverse bound, with real suprema used only when bounded. -/
theorem causalBehavior_reverse_average_bound
    (μ : Measure Θ) [IsProbabilityMeasure μ] (ps : Θ → CausalBehavior A O)
    (hm : ∀ h, Measurable (fun θ => (ps θ).mass h))
    (π ρ : ValidCausalPolicy A O)
    (hb : causalBehaviorTotalInformation μ ps π ≠ ⊤)
    (h : CausalBehaviorAverageFinitaryDominates μ ps π ρ) (m n : ℕ) :
    priorAverageDeficiency μ (causalBehaviorFiniteExperiment ρ.1 ps m)
        (causalBehaviorFiniteExperiment π.1 ps n) ≤
      Real.sqrt (((causalBehaviorTotalInformation μ ps π).toReal -
        infinitePriorInformation μ (causalBehaviorFiniteExperiment ρ.1 ps m))/2) := by
  let M := causalFamilyFiniteProcess ps hm id
  have hbound := (M.informationBounded_iff_totalInformation_ne_top μ π).mpr hb
  have hrev := M.reverse_prefix_le_information_tail μ hbound h m n
  rw [← M.totalInformation_toReal μ π] at hrev
  exact hrev

/-- **Exact causal criterion:** reverse-average lifting and exclusion of two
infinite scores on a strict pair are necessary and sufficient, on any family. -/
theorem causalBehavior_totalInformation_strictness_iff [Nonempty Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ] (ps : Θ → CausalBehavior A O)
    (hm : ∀ h, Measurable (fun θ => (ps θ).mass h))
    (policies : P → ValidCausalPolicy A O) :
    ((∀ π ρ, CausalBehaviorFinitaryDominates ps (policies π) (policies ρ) →
      causalBehaviorTotalInformation μ ps (policies ρ) ≤ causalBehaviorTotalInformation μ ps (policies π)) ∧
     (∀ π ρ, CausalBehaviorFinitaryDominates ps (policies π) (policies ρ) →
      ¬ CausalBehaviorFinitaryDominates ps (policies ρ) (policies π) →
      causalBehaviorTotalInformation μ ps (policies ρ) < causalBehaviorTotalInformation μ ps (policies π))) ↔
    ((∀ π ρ, CausalBehaviorFinitaryDominates ps (policies π) (policies ρ) →
      CausalBehaviorAverageFinitaryDominates μ ps (policies ρ) (policies π) →
      CausalBehaviorFinitaryDominates ps (policies ρ) (policies π)) ∧
     (∀ π ρ, CausalBehaviorFinitaryDominates ps (policies π) (policies ρ) →
      ¬ CausalBehaviorFinitaryDominates ps (policies ρ) (policies π) →
      ¬ (causalBehaviorTotalInformation μ ps (policies π) = ⊤ ∧
         causalBehaviorTotalInformation μ ps (policies ρ) = ⊤))) :=
  (causalFamilyFiniteProcess ps hm policies).totalInformation_strictlyMonotone_iff μ

section Compact
variable [TopologicalSpace Θ] [T2Space Θ] [BorelSpace Θ] [CompactSpace Θ] [Nonempty Θ]

/-- The canonical behavior topology supplies precisely the measurable masses. -/
theorem measurable_behavior_mass_of_continuous (ps : Θ → CausalBehavior A O)
    (hps : Continuous ps) (h : CausalHistory A O) :
    Measurable (fun θ => (ps θ).mass h) :=
  (((continuous_apply h).comp causalBehavior_mass_isEmbedding.continuous).comp hps).measurable

/-- On a compact behavior class with a positive atom at every world, the
prior-average and uniform process orders coincide. Countability need not be
supplied separately: the positive-atom assumption is the proof's exact premise. -/
theorem causalBehavior_averageDominates_iff_uniform_of_compact_atoms
    (μ : Measure Θ) [IsProbabilityMeasure μ] (hp : ∀ θ, 0 < μ.real {θ})
    (ps : Θ → CausalBehavior A O) (hps : Continuous ps)
    (π ρ : ValidCausalPolicy A O) :
    CausalBehaviorAverageFinitaryDominates μ ps π ρ ↔ CausalBehaviorFinitaryDominates ps π ρ := by
  let M := causalFamilyFiniteProcess ps (measurable_behavior_mass_of_continuous ps hps) id
  exact M.averageDominates_iff_uniform_of_compact_atoms μ hp
    (fun π n x => continuous_behaviorAcquired_coordinate ps hps π.1 n x) π ρ

/-- Compact positive-atom strictness with finite actual information, for any
feasible family. There is no identifying-policy or greatestness premise. -/
theorem causalBehavior_information_strict_of_compact_atoms
    (μ : Measure Θ) [IsProbabilityMeasure μ] (hp : ∀ θ, 0 < μ.real {θ})
    (ps : Θ → CausalBehavior A O) (hps : Continuous ps)
    (π ρ : ValidCausalPolicy A O) (hb : causalBehaviorTotalInformation μ ps π ≠ ⊤)
    (h : CausalBehaviorFinitaryDominates ps π ρ)
    (hn : ¬ CausalBehaviorFinitaryDominates ps ρ π) :
    causalBehaviorTotalInformation μ ps ρ < causalBehaviorTotalInformation μ ps π := by
  let M := causalFamilyFiniteProcess ps (measurable_behavior_mass_of_continuous ps hps) id
  have ha : M.AverageDominates μ π ρ := M.averageDominates_of_uniform μ h
  apply lt_of_le_of_ne (M.totalInformation_mono_of_averageDominates μ ha)
  intro he
  have hr := (M.totalInformation_eq_iff_averageDominates_reverse μ hb ha).mp he.symm
  exact hn ((causalBehavior_averageDominates_iff_uniform_of_compact_atoms μ hp ps hps ρ π).mp hr)

/-- Finite atomic prior entropy discharges finite information for every policy. -/
theorem causalBehavior_information_strict_of_compact_finite_entropy
    (μ : Measure Θ) [IsProbabilityMeasure μ] (hp : ∀ θ, 0 < μ.real {θ})
    (hi : Integrable (fun θ => -Real.log (μ.real {θ})) μ)
    (ps : Θ → CausalBehavior A O) (hps : Continuous ps)
    (π ρ : ValidCausalPolicy A O) (h : CausalBehaviorFinitaryDominates ps π ρ)
    (hn : ¬ CausalBehaviorFinitaryDominates ps ρ π) :
    causalBehaviorTotalInformation μ ps ρ < causalBehaviorTotalInformation μ ps π := by
  let M := causalFamilyFiniteProcess ps (measurable_behavior_mass_of_continuous ps hps) id
  apply causalBehavior_information_strict_of_compact_atoms μ hp ps hps π ρ ?_ h hn
  exact (M.informationBounded_iff_totalInformation_ne_top μ π).mp
    (M.informationBounded_of_atomic_entropy μ hp hi π)

end Compact
end
end IdExp
