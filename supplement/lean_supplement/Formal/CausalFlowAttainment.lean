import Formal.CausalFlowObjectivePrograms
import Formal.CapabilityAcquisitionTrajectories

/-!
# Attainment of finite-horizon posterior and purpose optimizations

Full recorded histories leave only finitely many possible posterior vectors
at a fixed horizon. Consequently *every* real-valued posterior potential
induces a continuous finite-horizon score on behavioral policies, even without
continuity or convexity of the potential. This finite-budget fact is distinct
from the regularity needed for infinite-time posterior objectives.
-/
namespace IdExp
open Finset Set
noncomputable section
set_option linter.unusedSectionVars false

variable {A O Θ : Type*} [Fintype A] [Fintype O] [Nonempty A] [Nonempty O]
  [Fintype Θ] [Nonempty Θ]

/-- A fixed-history policy likelihood is a finite product of policy rows. -/
theorem continuous_causalPolicyProb (h : CausalHistory A O) :
    Continuous (fun π : ValidCausalPolicy A O => causalPolicyProb π.1 h) := by
  induction h using List.reverseRecOn with
  | nil => simpa [causalPolicyProb, causalPolicyProbFrom] using
      (continuous_const : Continuous (fun _ : ValidCausalPolicy A O => (1 : ℝ)))
  | append_singleton h ao ih =>
      simp_rw [causalPolicyProb_append_singleton]
      exact ih.mul ((continuous_apply ao.1).comp
        ((continuous_apply h).comp continuous_subtype_val))

/-- Fixed-horizon terminal gain is continuous for any potential whatsoever;
its finitely many posterior coefficients are fixed by the declared class. -/
theorem continuous_causalPolicy_posterior_gain
    (ps : Θ → CausalBehavior A O) (H : ℕ) (Φ : (Θ → ℝ) → ℝ)
    (α : Θ → ℝ) (hα : IsDist α) :
    Continuous (fun π : ValidCausalPolicy A O =>
      finiteBayesPotential Φ α (causalBehaviorFiniteExperiment π.1 ps H) - Φ α) := by
  simp_rw [causalPolicy_posterior_gain_eq_linear ps H _ Φ α hα]
  apply continuous_finsetSum
  intro h _
  have hc := (continuous_causalPolicyProb (List.ofFn h)).mul_const
    (allocationPosteriorCoefficient Φ α (controlledTerminalLikelihood ps H) h)
  convert hc using 1
  funext π
  simp only [policyFlowTerminalWeights, policyFlowWeights,
    causalDecisionHistory_policyFlowNode]


/-- The inner optimized purpose value is continuous in the collector. -/
theorem continuous_causalPolicy_purpose {D : Type*} [Fintype D] [Nonempty D]
    (ps : Θ → CausalBehavior A O) (H : ℕ) (ν : Θ → ℝ) (u : Θ → D → ℝ) :
    Continuous (fun π : ValidCausalPolicy A O =>
      finiteBayesValue (causalBehaviorFiniteExperiment π.1 ps H) ν u) := by
  unfold finiteBayesValue
  apply continuous_finsetSum
  intro h _
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro d _
  unfold finiteDecisionScore
  apply continuous_finsetSum
  intro θ _
  change Continuous (fun π : ValidCausalPolicy A O =>
    ν θ * (causalPolicyProb π.1 (List.ofFn h) * (ps θ).mass (List.ofFn h)) * u θ d)
  exact (continuous_const.mul ((continuous_causalPolicyProb _).mul continuous_const)).mul
    continuous_const

/-- Each finite terminal posterior objective has a maximizing behavioral
policy. No full-revelation or native-sufficiency attainment is implied. -/
theorem exists_causalPolicy_maximizes_posterior_gain
    (ps : Θ → CausalBehavior A O) (H : ℕ) (Φ : (Θ → ℝ) → ℝ)
    (α : Θ → ℝ) (hα : IsDist α) :
    ∃ π : ValidCausalPolicy A O, ∀ σ : ValidCausalPolicy A O,
      finiteBayesPotential Φ α (causalBehaviorFiniteExperiment σ.1 ps H) - Φ α ≤
        finiteBayesPotential Φ α (causalBehaviorFiniteExperiment π.1 ps H) - Φ α := by
  obtain ⟨π, _, hπ⟩ := isCompact_univ.exists_isMaxOn
    (show (Set.univ : Set (ValidCausalPolicy A O)).Nonempty from
      ⟨defaultValidCausalPolicy, Set.mem_univ _⟩)
    (continuous_causalPolicy_posterior_gain ps H Φ α hα).continuousOn
  exact ⟨π, fun σ => hπ (Set.mem_univ σ)⟩

/-- Every continuous full-policy cost has an attained minimum. -/
theorem exists_causalPolicy_minimizes_continuous_cost
    (C : ValidCausalPolicy A O → ℝ) (hC : Continuous C) :
    ∃ π : ValidCausalPolicy A O, ∀ σ : ValidCausalPolicy A O, C π ≤ C σ := by
  obtain ⟨π, _, hπ⟩ := isCompact_univ.exists_isMinOn
    (show (Set.univ : Set (ValidCausalPolicy A O)).Nonempty from
      ⟨defaultValidCausalPolicy, Set.mem_univ _⟩) hC.continuousOn
  exact ⟨π, fun σ => hπ (Set.mem_univ σ)⟩

/-- Native weighted finite-library costs are continuous; weights need not
be normalized, and continuity itself does not require their positivity. -/
theorem continuous_causalPolicy_weighted_loss
    {J : Type*} {Y : J → Type*} [Fintype J] [∀ j, Fintype (Y j)]
    (ps : Θ → CausalBehavior A O) (H : ℕ)
    (T : ∀ j, FiniteExperiment Θ (Y j)) (hT : ∀ j, IsFiniteExperiment (T j))
    (q : J → ℝ) :
    Continuous (fun π : ValidCausalPolicy A O =>
      ∑ j, q j * finiteDeficiency (causalBehaviorFiniteExperiment π.1 ps H) (T j)) := by
  apply continuous_finsetSum
  intro j _
  exact continuous_const.mul (continuous_causalBehaviorPrefixDeficiency T hT ps H j)

/-- Native finite-library minimax costs are continuous as finite maxima. -/
theorem continuous_causalPolicy_max_loss
    {J : Type*} {Y : J → Type*} [Fintype J] [Nonempty J] [∀ j, Fintype (Y j)]
    (ps : Θ → CausalBehavior A O) (H : ℕ)
    (T : ∀ j, FiniteExperiment Θ (Y j)) (hT : ∀ j, IsFiniteExperiment (T j)) :
    Continuous (fun π : ValidCausalPolicy A O => Finset.univ.sup' Finset.univ_nonempty
      (fun j => finiteDeficiency (causalBehaviorFiniteExperiment π.1 ps H) (T j))) := by
  exact Continuous.finset_sup'_apply Finset.univ_nonempty
    (fun j _ => continuous_causalBehaviorPrefixDeficiency T hT ps H j)

/-- Both native cost formulations have actual all-policy minimizers. This
is attainment of a finite compromise, with no claim of complete exploration. -/
theorem exists_causalPolicy_minimizes_native_costs
    {J : Type*} {Y : J → Type*} [Fintype J] [Nonempty J] [∀ j, Fintype (Y j)]
    (ps : Θ → CausalBehavior A O) (H : ℕ)
    (T : ∀ j, FiniteExperiment Θ (Y j)) (hT : ∀ j, IsFiniteExperiment (T j))
    (q : J → ℝ) :
    (∃ π : ValidCausalPolicy A O, ∀ σ : ValidCausalPolicy A O,
      (∑ j, q j * finiteDeficiency (causalBehaviorFiniteExperiment π.1 ps H) (T j)) ≤
        ∑ j, q j * finiteDeficiency (causalBehaviorFiniteExperiment σ.1 ps H) (T j)) ∧
    (∃ π : ValidCausalPolicy A O, ∀ σ : ValidCausalPolicy A O,
      Finset.univ.sup' Finset.univ_nonempty
        (fun j => finiteDeficiency (causalBehaviorFiniteExperiment π.1 ps H) (T j)) ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun j => finiteDeficiency (causalBehaviorFiniteExperiment σ.1 ps H) (T j))) :=
  ⟨exists_causalPolicy_minimizes_continuous_cost _
      (continuous_causalPolicy_weighted_loss ps H T hT q),
    exists_causalPolicy_minimizes_continuous_cost _
      (continuous_causalPolicy_max_loss ps H T hT)⟩

/-- Every nonempty closed cost sublevel has an attained worst optimized
purpose value. This applies to continuous posterior, weighted-native and
minimax costs, with arbitrary real cost/value cutoffs. -/
theorem exists_causalPolicy_minimizes_purpose_on_cost_sublevel
    {D : Type*} [Fintype D] [Nonempty D]
    (ps : Θ → CausalBehavior A O) (H : ℕ) (C : ValidCausalPolicy A O → ℝ)
    (hC : Continuous C) (c : ℝ) (hne : ∃ π, C π ≤ c)
    (ν : Θ → ℝ) (u : Θ → D → ℝ) :
    ∃ π : ValidCausalPolicy A O, C π ≤ c ∧ ∀ σ : ValidCausalPolicy A O,
      C σ ≤ c → finiteBayesValue (causalBehaviorFiniteExperiment π.1 ps H) ν u ≤
        finiteBayesValue (causalBehaviorFiniteExperiment σ.1 ps H) ν u := by
  have hclosed : IsClosed {π : ValidCausalPolicy A O | C π ≤ c} :=
    isClosed_le hC continuous_const
  obtain ⟨π, hp, hm⟩ := hclosed.isCompact.exists_isMinOn hne
    (continuous_causalPolicy_purpose ps H ν u).continuousOn
  exact ⟨π, hp, fun σ hs => hm hs⟩

end
end IdExp
