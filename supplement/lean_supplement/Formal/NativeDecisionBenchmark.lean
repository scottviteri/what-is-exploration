import Formal.NativeDecisionEnvelope
import Formal.FiniteDecisionProblemOperations
import Formal.CausalPolicyMixture

/-!
# A task-specific native benchmark is attained by a deterministic plan

This supplies the taskwise equality (D3) in the comparison appendix. The
existing all-purpose envelope already compares every randomized collector;
here the same benchmark is identified with an actual maximum over literal
observation-only plans at exactly the target budget. The proof reuses the
recorded Kuhn mixture, exact plan relabeling, and prefix garbling.
-/

namespace IdExp

open Finset Set

universe u

variable {A O Θ : Type u} [Fintype A] [Fintype O] [Nonempty A] [Nonempty O]

/-- The finite maximum over deterministic observation-only plans at depth `n`. -/
noncomputable def causalBehaviorPlanDecisionBenchmark
    (ps : Θ → CausalBehavior A O) (n : ℕ) (P : FiniteSupportDecisionProblem Θ) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty fun σ : CausalObservationPlan A O n =>
    finiteDecisionProblemValue (CausalObservationPlan.behaviorPlanExperiment σ ps) P

/-- A deterministic plan's full trace and its observation string have the
same optimized value for every finite-support purpose. -/
theorem finiteDecisionProblemValue_causalPlan_eq_observations
    (ps : Θ → CausalBehavior A O) (n : ℕ) (τ : CausalPlan A O n)
    (P : FiniteSupportDecisionProblem Θ) :
    finiteDecisionProblemValue
        (causalBehaviorFiniteExperiment (causalPolicyOfPlan n τ) ps n) P =
      finiteDecisionProblemValue (CausalObservationPlan.behaviorPlanExperiment
        (CausalObservationPlan.ofCausalPlan τ) ps) P := by
  rw [causalBehaviorFiniteExperiment_eq_toResponse,
    causalBehaviorObservationPlanExperiment_ofCausalPlan_eq_toResponse]
  obtain ⟨h1, h2⟩ := causalPlan_full_observation_blackwell_equiv n τ
    (causalBehaviorResponsePresentation ps)
  exact finiteDecisionProblemValue_eq_of_blackwellEquiv _ _ h1 h2 P

/-- The full-record value equals the weighted values of its deterministic
Kuhn plans, including zero weights and null histories. -/
theorem finiteDecisionProblemValue_causalBehavior_kuhn [DecidableEq A] [DecidableEq O]
    (ps : Θ → CausalBehavior A O) (π : ValidCausalPolicy A O)
    (n : ℕ) (P : FiniteSupportDecisionProblem Θ) :
    finiteDecisionProblemValue (causalBehaviorFiniteExperiment π.1 ps n) P =
      ∑ τ : CausalPlan A O n, kuhnWeight π.1 n τ *
        finiteDecisionProblemValue (CausalObservationPlan.behaviorPlanExperiment
          (CausalObservationPlan.ofCausalPlan τ) ps) P := by
  classical
  rw [causalBehaviorFiniteExperiment_eq_toResponse]
  obtain ⟨h1, h2⟩ := causalFiniteExperiment_kuhn_recorded_equiv π.1 π.2
    (causalBehaviorResponsePresentation ps) n
  rw [finiteDecisionProblemValue_eq_of_blackwellEquiv _ _ h1 h2 P,
    finiteDecisionProblemValue_mixtureCollector _ _ (kuhnWeight_isDist π.1 π.2 n).1]
  apply Finset.sum_congr rfl
  intro τ _
  rw [← causalBehaviorFiniteExperiment_eq_toResponse,
    finiteDecisionProblemValue_causalPlan_eq_observations]

/-- Every bounded randomized collector has task value at most the best
deterministic plan of exactly the budget depth. -/
theorem finiteDecisionProblemValue_causalBehavior_le_planBenchmark
    (ps : Θ → CausalBehavior A O) (π : ValidCausalPolicy A O)
    {m n : ℕ} (hmn : m ≤ n) (P : FiniteSupportDecisionProblem Θ) :
    finiteDecisionProblemValue (causalBehaviorFiniteExperiment π.1 ps m) P ≤
      causalBehaviorPlanDecisionBenchmark ps n P := by
  classical
  have hpref : FiniteBlackwellLE (causalBehaviorFiniteExperiment π.1 ps m)
      (causalBehaviorFiniteExperiment π.1 ps n) := by
    simp only [causalBehaviorFiniteExperiment_eq_toResponse]
    exact causalFiniteExperiment_prefix_blackwell_of_le π.1 π.2
      (causalBehaviorResponsePresentation ps) (causalBehaviorResponsePresentation_valid ps) hmn
  apply (finiteDecisionProblemValue_mono_of_blackwell _ _ hpref P).trans
  rw [finiteDecisionProblemValue_causalBehavior_kuhn]
  calc
    _ ≤ ∑ τ : CausalPlan A O n, kuhnWeight π.1 n τ *
        causalBehaviorPlanDecisionBenchmark ps n P := by
      apply Finset.sum_le_sum
      intro τ _
      apply mul_le_mul_of_nonneg_left _ ((kuhnWeight_isDist π.1 π.2 n).1 τ)
      exact Finset.le_sup'
        (fun σ : CausalObservationPlan A O n =>
          finiteDecisionProblemValue (CausalObservationPlan.behaviorPlanExperiment σ ps) P)
        (Finset.mem_univ (CausalObservationPlan.ofCausalPlan τ))
    _ = _ := by rw [← Finset.sum_mul, (kuhnWeight_isDist π.1 π.2 n).2, one_mul]

/-- **D3:** knowing the task before acquisition never requires randomizing
or stopping early to attain its best native information value. -/
theorem causalBehaviorDecisionBenchmark_eq_planBenchmark
    (ps : Θ → CausalBehavior A O) (n : ℕ) (P : FiniteSupportDecisionProblem Θ) :
    causalBehaviorDecisionBenchmark ps n P = causalBehaviorPlanDecisionBenchmark ps n P := by
  classical
  have hbdd : BddAbove (Set.range fun q : BoundedCausalCollector A O n =>
      finiteDecisionProblemValue (boundedCausalBehaviorExperiment ps n q) P) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨q, rfl⟩
    exact (finiteDecisionProblemValue_mem_unitInterval _
      (causalBehaviorFiniteExperiment_valid q.2.1 q.2.2 ps q.1.1) P).2
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨q, rfl⟩
    exact finiteDecisionProblemValue_causalBehavior_le_planBenchmark ps q.2
      (Nat.le_of_lt_succ q.1.2) P
  · apply Finset.sup'_le
    intro σ _
    let q : BoundedCausalCollector A O n :=
      ⟨⟨n, Nat.lt_succ_self n⟩, ⟨causalPolicyOfPlan n σ.toCausalPlan,
        isCausalPolicy_causalPolicyOfPlan n σ.toCausalPlan⟩⟩
    have hle := le_csSup hbdd (Set.mem_range_self q)
    change finiteDecisionProblemValue
      (causalBehaviorFiniteExperiment (causalPolicyOfPlan n σ.toCausalPlan) ps n) P ≤ _ at hle
    rw [finiteDecisionProblemValue_causalPlan_eq_observations,
      CausalObservationPlan.ofCausalPlan_toCausalPlan] at hle
    exact hle

/-- The taskwise benchmark is attained by one literal native observation
plan, even on an infinite unstructured world class. -/
theorem exists_observationPlan_eq_decisionBenchmark
    (ps : Θ → CausalBehavior A O) (n : ℕ) (P : FiniteSupportDecisionProblem Θ) :
    ∃ σ : CausalObservationPlan A O n,
      causalBehaviorDecisionBenchmark ps n P =
        finiteDecisionProblemValue (CausalObservationPlan.behaviorPlanExperiment σ ps) P := by
  classical
  rw [causalBehaviorDecisionBenchmark_eq_planBenchmark]
  obtain ⟨σ, _, hσ⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun σ : CausalObservationPlan A O n =>
      finiteDecisionProblemValue (CausalObservationPlan.behaviorPlanExperiment σ ps) P)
  exact ⟨σ, hσ⟩

end IdExp
