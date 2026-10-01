import Formal.DecisionEnvelope
import Formal.CausalBehaviorCapability

/-!
# The actual native audit is an envelope of decision disadvantages

This module applies quantitative decision duality to the canonical
controlled-prefix behavior carrier. The displayed benchmark optimizes over
all valid randomized causal collectors with at most the prescribed number
of interactions. Existing causal finite-horizon universality identifies its
worst-purpose disadvantage with the literal native audit.
-/

set_option linter.unusedSectionVars false

namespace IdExp

open Finset Set

universe u

variable {A O Θ X : Type u} [Fintype A] [Fintype O] [Fintype X]
  [Nonempty A] [Nonempty O]

/-- A deterministic native observation plan with its bounded horizon. -/
abbrev BoundedNativeObservationPlan (A O : Type u) (n : ℕ) :=
  Σ m : Fin (n + 1), CausalObservationPlan A O m.1

noncomputable instance boundedNativeObservationPlanNonempty (n : ℕ) :
    Nonempty (BoundedNativeObservationPlan A O n) :=
  ⟨⟨⟨0, Nat.zero_lt_succ n⟩, Classical.arbitrary _⟩⟩

/-- Literal direct-behavior native targets in the bounded menu. -/
noncomputable def boundedNativeBehaviorExperiment
    (ps : Θ → CausalBehavior A O) (n : ℕ)
    (q : BoundedNativeObservationPlan A O n) :
    FiniteExperiment Θ (CausalObservationTrace O q.1.1) :=
  CausalObservationPlan.behaviorPlanExperiment q.2 ps

/-- The native audit's supremum is exactly the bounded native family range. -/
theorem causalBehaviorNativeDeficiencyUpTo_eq_bounded_range
    (E : FiniteExperiment Θ X) (ps : Θ → CausalBehavior A O) (n : ℕ) :
    causalBehaviorNativeDeficiencyUpTo E ps n =
      sSup (Set.range fun q : BoundedNativeObservationPlan A O n =>
        finiteDeficiency E (boundedNativeBehaviorExperiment ps n q)) := by
  unfold causalBehaviorNativeDeficiencyUpTo
  congr 1
  ext d
  constructor
  · rintro ⟨m, hmn, σ, rfl⟩
    exact ⟨⟨⟨m, Nat.lt_succ_of_le hmn⟩, σ⟩, rfl⟩
  · rintro ⟨q, rfl⟩
    exact ⟨q.1.1, Nat.le_of_lt_succ q.1.2, q.2, rfl⟩

/-- Native audit equals the all-purpose decision envelope over actual
finite native observation interventions. -/
theorem causalBehaviorNativeDeficiencyUpTo_eq_nativeDecisionEnvelope
    [Nonempty Θ]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (ps : Θ → CausalBehavior A O) (n : ℕ) :
    causalBehaviorNativeDeficiencyUpTo E ps n =
      finiteDecisionEnvelope E (boundedNativeBehaviorExperiment ps n) := by
  rw [finiteDecisionEnvelope_eq_sSup_deficiency E hE
    (boundedNativeBehaviorExperiment ps n)
    (fun q => CausalObservationPlan.behaviorPlanExperiment_valid q.2 ps)]
  exact causalBehaviorNativeDeficiencyUpTo_eq_bounded_range E ps n

/-- A valid randomized causal collector with its bounded horizon. -/
abbrev BoundedCausalCollector (A O : Type u) [Fintype A] (n : ℕ) :=
  Fin (n + 1) × ValidCausalPolicy A O

noncomputable instance boundedCausalCollectorNonempty (n : ℕ) :
    Nonempty (BoundedCausalCollector A O n) := by
  let τ : CausalPlan A O 0 := Classical.arbitrary _
  exact ⟨⟨⟨0, Nat.zero_lt_succ n⟩,
    ⟨causalPolicyOfPlan 0 τ, isCausalPolicy_causalPolicyOfPlan 0 τ⟩⟩⟩

/-- The acquired experiment of an actual bounded randomized collector. -/
noncomputable def boundedCausalBehaviorExperiment
    (ps : Θ → CausalBehavior A O) (n : ℕ)
    (q : BoundedCausalCollector A O n) :
    FiniteExperiment Θ (CausalFiniteTrace A O q.1.1) :=
  causalBehaviorFiniteExperiment q.2.1 ps q.1.1

/-- The task-specific native experimental benchmark `B_n`: the collector
may depend on the supplied purpose, while its policy is world-independent. -/
noncomputable def causalBehaviorDecisionBenchmark
    (ps : Θ → CausalBehavior A O) (n : ℕ)
    (P : FiniteSupportDecisionProblem Θ) : ℝ :=
  finiteExperimentalBenchmark (boundedCausalBehaviorExperiment ps n) P

/-- The supremum of policy deficiencies is the corresponding bounded
collector family range, without dropping randomized policies. -/
theorem causalBehaviorPolicyDeficiencyUpTo_eq_bounded_range
    (E : FiniteExperiment Θ X) (ps : Θ → CausalBehavior A O) (n : ℕ) :
    causalBehaviorPolicyDeficiencyUpTo E ps n =
      sSup (Set.range fun q : BoundedCausalCollector A O n =>
        finiteDeficiency E (boundedCausalBehaviorExperiment ps n q)) := by
  unfold causalBehaviorPolicyDeficiencyUpTo
  congr 1
  ext d
  constructor
  · rintro ⟨m, hmn, π, hπ, rfl⟩
    exact ⟨⟨⟨m, Nat.lt_succ_of_le hmn⟩, ⟨π, hπ⟩⟩, rfl⟩
  · rintro ⟨q, rfl⟩
    exact ⟨q.1.1, Nat.le_of_lt_succ q.1.2, q.2.1, q.2.2, rfl⟩

/-- **Readiness for an unspecified purpose, literal causal form.** The
native audit equals the largest optimized disadvantage relative to a
purpose-specific randomized collector with at most `n` interactions.
The source signal and action/observation alphabets are finite; the nonempty
world class is arbitrary. Every task uses a finite-support prior and a
nonempty finite decision alphabet with utilities in `[0,1]`. -/
theorem causalBehaviorNativeDeficiencyUpTo_eq_decisionBenchmarkGap
    [Nonempty Θ]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (ps : Θ → CausalBehavior A O) (n : ℕ) :
    causalBehaviorNativeDeficiencyUpTo E ps n =
      sSup (Set.range fun P : FiniteSupportDecisionProblem Θ =>
        causalBehaviorDecisionBenchmark ps n P - finiteDecisionProblemValue E P) := by
  change causalBehaviorNativeDeficiencyUpTo E ps n =
    finiteDecisionEnvelope E (boundedCausalBehaviorExperiment ps n)
  rw [finiteDecisionEnvelope_eq_sSup_deficiency E hE
    (boundedCausalBehaviorExperiment ps n)
    (fun q => causalBehaviorFiniteExperiment_valid q.2.1 q.2.2 ps q.1.1)]
  rw [← causalBehaviorPolicyDeficiencyUpTo_eq_bounded_range]
  exact causalBehavior_finiteHorizonUniversality E hE ps n

/-- The same equality for the actual record acquired by a valid causal
policy, retaining its full action-observation trace. -/
theorem causalBehaviorAcquired_nativeAudit_eq_decisionBenchmarkGap
    [Nonempty Θ]
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (ps : Θ → CausalBehavior A O) (t n : ℕ) :
    causalBehaviorNativeDeficiencyUpTo (causalBehaviorFiniteExperiment π ps t) ps n =
      sSup (Set.range fun P : FiniteSupportDecisionProblem Θ =>
        causalBehaviorDecisionBenchmark ps n P -
          finiteDecisionProblemValue (causalBehaviorFiniteExperiment π ps t) P) :=
  causalBehaviorNativeDeficiencyUpTo_eq_decisionBenchmarkGap _
    (causalBehaviorFiniteExperiment_valid π hπ ps t) ps n

end IdExp
