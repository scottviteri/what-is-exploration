import Formal.FinitePolicyFlow
import Formal.FiniteDecoderAllocation

/-!
# Exact finite linear feasibility for acquired native losses

A finite full-history realization flow and per-target decoder allocations
characterize the weighted deficiency sublevels of all behavioral collectors.
The world class is finite and nonempty; the controlled-prefix behaviors are
literal inputs, the source signal is its full action-observation record, and
finite target alphabets may differ. All policy and decoder randomization is
allowed, including zero realization weights and zero loss thresholds.

The constraints below are linear in w, x, d, r, z: controlled behavior and
target masses are fixed coefficients. No supplied decoder or optimizer,
positive source support, or solver correctness hypothesis is used. The
implementation's pruning of impossible observations remains separate.
-/
namespace IdExp
open Finset
noncomputable section
set_option linter.unusedSectionVars false

variable {A O Θ J : Type*} {Y : J → Type*}
  [Fintype A] [Fintype O] [Nonempty A] [Nonempty O]
  [Fintype Θ] [Nonempty Θ] [Fintype J]
  [∀ j, Fintype (Y j)] [∀ j, Nonempty (Y j)]

def policyFlowTerminalWeights (H : ℕ) (w : PolicyFlowNode A O H → ℝ) :
    CausalFiniteTrace A O H → ℝ :=
  fun h => w (policyFlowNode H (List.ofFn h) (by simp))

def controlledTerminalLikelihood (ps : Θ → CausalBehavior A O) (H : ℕ) :
    Θ → CausalFiniteTrace A O H → ℝ :=
  fun θ h => (ps θ).mass (List.ofFn h)

theorem finiteFlowExperiment_eq_allocationSource
    (ps : Θ → CausalBehavior A O) (H : ℕ) (w : PolicyFlowNode A O H → ℝ) :
    finiteFlowExperiment ps H w =
      allocationSource (controlledTerminalLikelihood ps H) (policyFlowTerminalWeights H w) := rfl

/-- Restricting an arbitrary policy to its weights preserves its full acquired law. -/
theorem finiteFlowExperiment_policyFlowWeights
    (ps : Θ → CausalBehavior A O) (H : ℕ) (π : ValidCausalPolicy A O) :
    finiteFlowExperiment ps H (policyFlowWeights H π) =
      causalBehaviorFiniteExperiment π.1 ps H := by
  funext θ h
  simp only [finiteFlowExperiment, policyFlowWeights, causalDecisionHistory_policyFlowNode]
  rfl

/-- At each feasible flow, the allocation/slack projection is exactly the
weighted-loss sublevel, not merely an upper relaxation of that sublevel. -/
theorem finiteFlow_weighted_loss_le_iff_allocation_slacks
    (ps : Θ → CausalBehavior A O) (H : ℕ) (w : PolicyFlowNode A O H → ℝ)
    (x : CausalDecisionPoint A O H → A → ℝ) (hf : IsFinitePolicyFlow H w x)
    (T : ∀ j, FiniteExperiment Θ (Y j)) (v : J → ℝ) (hv : ∀ j, 0 ≤ v j) (c : ℝ) :
    (∑ j, v j * finiteDeficiency (finiteFlowExperiment ps H w) (T j)) ≤ c ↔
      ∃ (d : J → ℝ) (r : ∀ j, CausalFiniteTrace A O H → Y j → ℝ)
        (z : ∀ j, Θ → Y j → ℝ),
        (∀ j, AllocationSlackCertificate (controlledTerminalLikelihood ps H)
          (policyFlowTerminalWeights H w) (T j) (d j) (r j) (z j)) ∧
        (∑ j, v j * d j) ≤ c := by
  rw [finiteFlowExperiment_eq_allocationSource]
  exact weightedDeficiency_le_iff_allocation_slacks _ _
    (fun h => hf.weight_nonneg _) T v hv c

/-- The complete finite linear constraint system: policy flow, target-specific
unrestricted decoder allocations, worldwise TV slacks, and the weighted cutoff. -/
structure CausalWeightedLossProgram (ps : Θ → CausalBehavior A O) (H : ℕ)
    (T : ∀ j, FiniteExperiment Θ (Y j)) (v : J → ℝ) (c : ℝ)
    (w : PolicyFlowNode A O H → ℝ) (x : CausalDecisionPoint A O H → A → ℝ)
    (d : J → ℝ) (r : ∀ j, CausalFiniteTrace A O H → Y j → ℝ)
    (z : ∀ j, Θ → Y j → ℝ) : Prop where
  flow : IsFinitePolicyFlow H w x
  targets : ∀ j, AllocationSlackCertificate (controlledTerminalLikelihood ps H)
    (policyFlowTerminalWeights H w) (T j) (d j) (r j) (z j)
  cutoff : (∑ j, v j * d j) ≤ c

/-- **All-policy finite linear-program equivalence.** For every real loss
threshold, feasible full-history variables exist exactly when a valid
behavioral collector meets that weighted deficiency threshold. Source validity
comes from the controlled behavior and reconstructed policy. Targets are fixed
before the source record; each receives one world-independent random decoder. -/
theorem exists_causalPolicy_weighted_loss_le_iff_flow_program
    (ps : Θ → CausalBehavior A O) (H : ℕ)
    (T : ∀ j, FiniteExperiment Θ (Y j)) (v : J → ℝ) (hv : ∀ j, 0 ≤ v j) (c : ℝ) :
    (∃ π : ValidCausalPolicy A O,
      (∑ j, v j * finiteDeficiency (causalBehaviorFiniteExperiment π.1 ps H) (T j)) ≤ c) ↔
      ∃ (w : PolicyFlowNode A O H → ℝ) (x : CausalDecisionPoint A O H → A → ℝ)
        (d : J → ℝ) (r : ∀ j, CausalFiniteTrace A O H → Y j → ℝ)
        (z : ∀ j, Θ → Y j → ℝ), CausalWeightedLossProgram ps H T v c w x d r z := by
  constructor
  · rintro ⟨π, hπ⟩
    let w := policyFlowWeights H π
    let x := policyFlowActions H π
    have hf : IsFinitePolicyFlow H w x := isFinitePolicyFlow_of_policy H π
    have hc : (∑ j, v j * finiteDeficiency (finiteFlowExperiment ps H w) (T j)) ≤ c := by
      simpa only [w, finiteFlowExperiment_policyFlowWeights] using hπ
    obtain ⟨d, r, z, ht, hb⟩ :=
      (finiteFlow_weighted_loss_le_iff_allocation_slacks ps H w x hf T v hv c).mp hc
    exact ⟨w, x, d, r, z, hf, ht, hb⟩
  · rintro ⟨w, x, d, r, z, hp⟩
    refine ⟨policyOfFiniteFlow H w x hp.flow, ?_⟩
    rw [causalBehaviorFiniteExperiment_policyOfFiniteFlow]
    exact (finiteFlow_weighted_loss_le_iff_allocation_slacks ps H w x hp.flow T v hv c).mpr
      ⟨d, r, z, hp.targets, hp.cutoff⟩

end
end IdExp
