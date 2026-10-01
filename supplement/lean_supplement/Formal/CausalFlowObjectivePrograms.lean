import Formal.CausalFlowLinearProgram
import Formal.FiniteAllocationObjectives

/-!
# Exact all-policy posterior, native minimax, and purpose programs

Realization flows are an exact representation of acquired experiments. This
single equivalence transports arbitrary experiment predicates, then combines
fixed posterior coefficients, native decoder allocations, and the optimized
Bayes-value epigraph. The joint sublevel theorems certify the mathematical
programs used for worst purpose values under a cost cutoff, including the
boundary of a near-optimal set. No interchange of collector minimization and
decision maximization occurs. Numerical matrix generation, impossible-history
pruning, solver tolerances, and claimed decimal endpoints remain separate.
-/
namespace IdExp
open Finset
noncomputable section
set_option linter.unusedSectionVars false

variable {A O Θ : Type*} [Fintype A] [Fintype O] [Nonempty A] [Nonempty O]
  [Fintype Θ] [Nonempty Θ]

/-- A single representation theorem transports every experiment-level
property to finite realization coordinates, preserving conjunctions and
thus selected-family constraints together with downstream evaluations. -/
theorem exists_causalPolicy_property_iff_flow
    (ps : Θ → CausalBehavior A O) (H : ℕ)
    (P : FiniteExperiment Θ (CausalFiniteTrace A O H) → Prop) :
    (∃ π : ValidCausalPolicy A O, P (causalBehaviorFiniteExperiment π.1 ps H)) ↔
      ∃ (w : PolicyFlowNode A O H → ℝ) (x : CausalDecisionPoint A O H → A → ℝ),
        IsFinitePolicyFlow H w x ∧ P (finiteFlowExperiment ps H w) := by
  constructor
  · rintro ⟨π, hπ⟩
    exact ⟨policyFlowWeights H π, policyFlowActions H π, isFinitePolicyFlow_of_policy H π,
      by simpa only [finiteFlowExperiment_policyFlowWeights] using hπ⟩
  · rintro ⟨w, x, hf, hp⟩
    exact ⟨policyOfFiniteFlow H w x hf,
      by simpa only [causalBehaviorFiniteExperiment_policyOfFiniteFlow] using hp⟩

/-- Literal posterior-gain formula in full-history flow coordinates, with
validity discharged from controlled-prefix behaviors and a feasible flow. -/
theorem finiteFlow_posterior_gain_eq_linear
    (ps : Θ → CausalBehavior A O) (H : ℕ)
    (w : PolicyFlowNode A O H → ℝ) (x : CausalDecisionPoint A O H → A → ℝ)
    (hf : IsFinitePolicyFlow H w x) (Φ : (Θ → ℝ) → ℝ)
    (α : Θ → ℝ) (hα : IsDist α) :
    finiteBayesPotential Φ α (finiteFlowExperiment ps H w) - Φ α =
      ∑ h, policyFlowTerminalWeights H w h *
        allocationPosteriorCoefficient Φ α (controlledTerminalLikelihood ps H) h := by
  exact finiteBayesGain_allocationSource Φ α hα _ _
    (finiteFlowExperiment_valid ps H w x hf)

/-- The same formula on literal behavioral-policy path laws. Arbitrary null
controlled prefixes and zero policy weights are included. -/
theorem causalPolicy_posterior_gain_eq_linear
    (ps : Θ → CausalBehavior A O) (H : ℕ) (π : ValidCausalPolicy A O)
    (Φ : (Θ → ℝ) → ℝ) (α : Θ → ℝ) (hα : IsDist α) :
    finiteBayesPotential Φ α (causalBehaviorFiniteExperiment π.1 ps H) - Φ α =
      ∑ h, policyFlowTerminalWeights H (policyFlowWeights H π) h *
        allocationPosteriorCoefficient Φ α (controlledTerminalLikelihood ps H) h := by
  simpa only [finiteFlowExperiment_policyFlowWeights] using
    finiteFlow_posterior_gain_eq_linear ps H _ _ (isFinitePolicyFlow_of_policy H π) Φ α hα

section PosteriorPurpose
variable {D : Type*} [Fintype D] [Nonempty D]

/-- All constraints are linear: the collector's cost is negative posterior
gain and the purpose is evaluated with its own prior and payoff table. -/
structure CausalPosteriorPurposeProgram
    (ps : Θ → CausalBehavior A O) (H : ℕ) (Φ : (Θ → ℝ) → ℝ)
    (α ν : Θ → ℝ) (u : Θ → D → ℝ) (c b : ℝ)
    (w : PolicyFlowNode A O H → ℝ) (x : CausalDecisionPoint A O H → A → ℝ)
    (v : CausalFiniteTrace A O H → ℝ) : Prop where
  flow : IsFinitePolicyFlow H w x
  cutoff : -(∑ h, policyFlowTerminalWeights H w h *
    allocationPosteriorCoefficient Φ α (controlledTerminalLikelihood ps H) h) ≤ c
  purpose : AllocationDecisionEpigraph (controlledTerminalLikelihood ps H)
    (policyFlowTerminalWeights H w) ν u v
  value_bound : (∑ h, v h) ≤ b

/-- Exact all-policy posterior-cost/purpose joint sublevels. For a supplied
cost cutoff, equality of every value sublevel identifies the mathematical
worst-purpose optimization. Planning and evaluation priors remain separate;
only the planning prior needs normalization for the gain baseline formula. -/
theorem exists_causalPolicy_posterior_purpose_le_iff_flow_program
    (ps : Θ → CausalBehavior A O) (H : ℕ) (Φ : (Θ → ℝ) → ℝ)
    (α : Θ → ℝ) (hα : IsDist α) (ν : Θ → ℝ) (u : Θ → D → ℝ) (c b : ℝ) :
    (∃ π : ValidCausalPolicy A O,
      -(finiteBayesPotential Φ α (causalBehaviorFiniteExperiment π.1 ps H) - Φ α) ≤ c ∧
      finiteBayesValue (causalBehaviorFiniteExperiment π.1 ps H) ν u ≤ b) ↔
      ∃ (w : PolicyFlowNode A O H → ℝ) (x : CausalDecisionPoint A O H → A → ℝ)
        (v : CausalFiniteTrace A O H → ℝ),
        CausalPosteriorPurposeProgram ps H Φ α ν u c b w x v := by
  rw [exists_causalPolicy_property_iff_flow ps H (fun E =>
    -(finiteBayesPotential Φ α E - Φ α) ≤ c ∧ finiteBayesValue E ν u ≤ b)]
  constructor
  · rintro ⟨w, x, hf, hc, hb⟩
    rw [finiteFlow_posterior_gain_eq_linear ps H w x hf Φ α hα] at hc
    obtain ⟨v, hv, hsum⟩ :=
      (finiteBayesValue_allocationSource_le_iff_epigraph _ _ ν u b).mp hb
    exact ⟨w, x, v, hf, hc, hv, hsum⟩
  · rintro ⟨w, x, v, hp⟩
    refine ⟨w, x, hp.flow, ?_, ?_⟩
    · rw [finiteFlow_posterior_gain_eq_linear ps H w x hp.flow Φ α hα]
      exact hp.cutoff
    · exact (finiteBayesValue_allocationSource_le_iff_epigraph _ _ ν u b).mpr
        ⟨v, hp.purpose, hp.value_bound⟩

end PosteriorPurpose

section Native
variable {J : Type*} {Y : J → Type*} [Fintype J]
  [∀ j, Fintype (Y j)] [∀ j, Nonempty (Y j)]

/-- A shared native-error cutoff is the minimax epigraph. Each target still
receives an independently chosen world-independent randomized decoder. -/
structure CausalMinimaxLossProgram (ps : Θ → CausalBehavior A O) (H : ℕ)
    (T : ∀ j, FiniteExperiment Θ (Y j)) (c : ℝ)
    (w : PolicyFlowNode A O H → ℝ) (x : CausalDecisionPoint A O H → A → ℝ)
    (r : ∀ j, CausalFiniteTrace A O H → Y j → ℝ)
    (z : ∀ j, Θ → Y j → ℝ) : Prop where
  flow : IsFinitePolicyFlow H w x
  targets : ∀ j, AllocationSlackCertificate (controlledTerminalLikelihood ps H)
    (policyFlowTerminalWeights H w) (T j) c (r j) (z j)

/-- Exact minimax feasibility at each real cutoff. The pointwise formulation
also permits an empty target library, where both sets of constraints vanish. -/
theorem exists_causalPolicy_all_losses_le_iff_flow_program
    (ps : Θ → CausalBehavior A O) (H : ℕ)
    (T : ∀ j, FiniteExperiment Θ (Y j)) (c : ℝ) :
    (∃ π : ValidCausalPolicy A O, ∀ j,
      finiteDeficiency (causalBehaviorFiniteExperiment π.1 ps H) (T j) ≤ c) ↔
      ∃ (w : PolicyFlowNode A O H → ℝ) (x : CausalDecisionPoint A O H → A → ℝ)
        (r : ∀ j, CausalFiniteTrace A O H → Y j → ℝ) (z : ∀ j, Θ → Y j → ℝ),
        CausalMinimaxLossProgram ps H T c w x r z := by
  rw [exists_causalPolicy_property_iff_flow ps H
    (fun E => ∀ j, finiteDeficiency E (T j) ≤ c)]
  constructor
  · rintro ⟨w, x, hf, hc⟩
    have hex := fun j => (finiteDeficiency_le_iff_allocation_slacks
      (controlledTerminalLikelihood ps H) (policyFlowTerminalWeights H w)
      (fun h => hf.weight_nonneg _) (T j) c).mp (hc j)
    choose r z hz using hex
    exact ⟨w, x, r, z, hf, hz⟩
  · rintro ⟨w, x, r, z, hp⟩
    refine ⟨w, x, hp.flow, fun j => ?_⟩
    exact (finiteDeficiency_le_iff_allocation_slacks _ _
      (fun h => hp.flow.weight_nonneg _) (T j) c).mpr ⟨r j, z j, hp.targets j⟩

/-- Literal finite-maximum version of the native minimax program. -/
theorem exists_causalPolicy_max_loss_le_iff_flow_program [Nonempty J]
    (ps : Θ → CausalBehavior A O) (H : ℕ)
    (T : ∀ j, FiniteExperiment Θ (Y j)) (c : ℝ) :
    (∃ π : ValidCausalPolicy A O, Finset.univ.sup' Finset.univ_nonempty
      (fun j => finiteDeficiency (causalBehaviorFiniteExperiment π.1 ps H) (T j)) ≤ c) ↔
      ∃ (w : PolicyFlowNode A O H → ℝ) (x : CausalDecisionPoint A O H → A → ℝ)
        (r : ∀ j, CausalFiniteTrace A O H → Y j → ℝ) (z : ∀ j, Θ → Y j → ℝ),
        CausalMinimaxLossProgram ps H T c w x r z := by
  simpa only [Finset.sup'_le_iff, Finset.mem_univ, forall_true_left] using
    exists_causalPolicy_all_losses_le_iff_flow_program ps H T c

variable {D : Type*} [Fintype D] [Nonempty D]

/-- A native weighted-cost cutoff and a purpose epigraph share the same
flow. This includes every randomized adaptive collector in the sublevel. -/
theorem exists_causalPolicy_weighted_purpose_le_iff_flow_program
    (ps : Θ → CausalBehavior A O) (H : ℕ)
    (T : ∀ j, FiniteExperiment Θ (Y j)) (q : J → ℝ) (hq : ∀ j, 0 ≤ q j)
    (ν : Θ → ℝ) (u : Θ → D → ℝ) (c b : ℝ) :
    (∃ π : ValidCausalPolicy A O,
      (∑ j, q j * finiteDeficiency (causalBehaviorFiniteExperiment π.1 ps H) (T j)) ≤ c ∧
      finiteBayesValue (causalBehaviorFiniteExperiment π.1 ps H) ν u ≤ b) ↔
      ∃ (w : PolicyFlowNode A O H → ℝ) (x : CausalDecisionPoint A O H → A → ℝ)
        (d : J → ℝ) (r : ∀ j, CausalFiniteTrace A O H → Y j → ℝ)
        (z : ∀ j, Θ → Y j → ℝ) (v : CausalFiniteTrace A O H → ℝ),
        CausalWeightedLossProgram ps H T q c w x d r z ∧
        AllocationDecisionEpigraph (controlledTerminalLikelihood ps H)
          (policyFlowTerminalWeights H w) ν u v ∧ (∑ h, v h) ≤ b := by
  rw [exists_causalPolicy_property_iff_flow ps H (fun E =>
    (∑ j, q j * finiteDeficiency E (T j)) ≤ c ∧ finiteBayesValue E ν u ≤ b)]
  constructor
  · rintro ⟨w, x, hf, hc, hb⟩
    obtain ⟨d, r, z, ht, hcut⟩ :=
      (finiteFlow_weighted_loss_le_iff_allocation_slacks ps H w x hf T q hq c).mp hc
    obtain ⟨v, hv, hsum⟩ :=
      (finiteBayesValue_allocationSource_le_iff_epigraph _ _ ν u b).mp hb
    exact ⟨w, x, d, r, z, v, ⟨hf, ht, hcut⟩, hv, hsum⟩
  · rintro ⟨w, x, d, r, z, v, hp, hv, hsum⟩
    exact ⟨w, x, hp.flow,
      (finiteFlow_weighted_loss_le_iff_allocation_slacks ps H w x hp.flow T q hq c).mpr
        ⟨d, r, z, hp.targets, hp.cutoff⟩,
      (finiteBayesValue_allocationSource_le_iff_epigraph _ _ ν u b).mpr ⟨v, hv, hsum⟩⟩

/-- The minimax counterpart of the purpose-envelope program, retaining the
actual common cost cutoff and the inner optimized decision value. -/
theorem exists_causalPolicy_minimax_purpose_le_iff_flow_program
    (ps : Θ → CausalBehavior A O) (H : ℕ)
    (T : ∀ j, FiniteExperiment Θ (Y j)) (ν : Θ → ℝ)
    (u : Θ → D → ℝ) (c b : ℝ) :
    (∃ π : ValidCausalPolicy A O,
      (∀ j, finiteDeficiency (causalBehaviorFiniteExperiment π.1 ps H) (T j) ≤ c) ∧
      finiteBayesValue (causalBehaviorFiniteExperiment π.1 ps H) ν u ≤ b) ↔
      ∃ (w : PolicyFlowNode A O H → ℝ) (x : CausalDecisionPoint A O H → A → ℝ)
        (r : ∀ j, CausalFiniteTrace A O H → Y j → ℝ) (z : ∀ j, Θ → Y j → ℝ)
        (v : CausalFiniteTrace A O H → ℝ),
        CausalMinimaxLossProgram ps H T c w x r z ∧
        AllocationDecisionEpigraph (controlledTerminalLikelihood ps H)
          (policyFlowTerminalWeights H w) ν u v ∧ (∑ h, v h) ≤ b := by
  rw [exists_causalPolicy_property_iff_flow ps H (fun E =>
    (∀ j, finiteDeficiency E (T j) ≤ c) ∧ finiteBayesValue E ν u ≤ b)]
  constructor
  · rintro ⟨w, x, hf, hc, hb⟩
    have hex := fun j => (finiteDeficiency_le_iff_allocation_slacks
      (controlledTerminalLikelihood ps H) (policyFlowTerminalWeights H w)
      (fun h => hf.weight_nonneg _) (T j) c).mp (hc j)
    choose r z hz using hex
    obtain ⟨v, hv, hsum⟩ :=
      (finiteBayesValue_allocationSource_le_iff_epigraph _ _ ν u b).mp hb
    exact ⟨w, x, r, z, v, ⟨hf, hz⟩, hv, hsum⟩
  · rintro ⟨w, x, r, z, v, hp, hv, hsum⟩
    refine ⟨w, x, hp.flow, fun j => ?_, ?_⟩
    · exact (finiteDeficiency_le_iff_allocation_slacks _ _
        (fun h => hp.flow.weight_nonneg _) (T j) c).mpr ⟨r j, z j, hp.targets j⟩
    · exact (finiteBayesValue_allocationSource_le_iff_epigraph _ _ ν u b).mpr ⟨v, hv, hsum⟩

end Native
end
end IdExp
