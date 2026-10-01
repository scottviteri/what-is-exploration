import Formal.NativeDecisionBenchmark

/-!
# Uniform-purpose native decision readiness

The comparison appendix places the supremum over purposes before acquisition
time tends to infinity. This module checks that quantifier order on literal
controlled-behavior records and keeps the target budget independent of the
collection time. No finite world class, attained identification, or uniform
cutoff across all target depths is required.
-/

namespace IdExp

open Finset Set Filter Topology

universe u

variable {A O Θ X : Type u} [Fintype A] [Fintype O] [Fintype X]
  [Nonempty A] [Nonempty O] [Nonempty Θ]

/-- The audit through a fixed budget is attained by one literal observation plan of
exactly the target budget, including budget zero. -/
theorem exists_observationPlan_eq_nativeDeficiencyUpTo
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (ps : Θ → CausalBehavior A O) (n : ℕ) :
    ∃ σ : CausalObservationPlan A O n,
      causalBehaviorNativeDeficiencyUpTo E ps n =
        finiteDeficiency E (CausalObservationPlan.behaviorPlanExperiment σ ps) := by
  rw [causalBehaviorNativeDeficiencyUpTo_eq_raw,
    causalNativeDeficiencyUpTo_eq_terminal E hE _
      (causalBehaviorResponsePresentation_valid ps)]
  obtain ⟨τ, hτ⟩ := exists_causalPlan_eq_nativeDeficiency E
    (causalBehaviorResponsePresentation ps) n
  refine ⟨CausalObservationPlan.ofCausalPlan τ, ?_⟩
  rw [causalBehaviorObservationPlanExperiment_ofCausalPlan_eq_toResponse]
  exact hτ

/-- Every exact-depth native target is bounded by the actual audit through the fixed budget. -/
theorem finiteDeficiency_observationPlan_le_nativeDeficiencyUpTo
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (ps : Θ → CausalBehavior A O) (n : ℕ) (σ : CausalObservationPlan A O n) :
    finiteDeficiency E (CausalObservationPlan.behaviorPlanExperiment σ ps) ≤
      causalBehaviorNativeDeficiencyUpTo E ps n := by
  rw [causalBehaviorNativeDeficiencyUpTo_eq_raw,
    causalNativeDeficiencyUpTo_eq_terminal E hE _
      (causalBehaviorResponsePresentation_valid ps),
    causalBehaviorObservationPlanExperiment_eq_toResponse]
  exact finiteDeficiency_causalPlan_le_native E _ n σ.toCausalPlan

/-- A finite audit threshold is equivalent to the simultaneous readiness
inequality for every purpose, randomized collector and shorter budget. -/
theorem causalBehaviorNativeDeficiencyUpTo_le_iff_decisionReadiness
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (ps : Θ → CausalBehavior A O) (n : ℕ) (ε : ℝ) :
    causalBehaviorNativeDeficiencyUpTo E ps n ≤ ε ↔
      ∀ (P : FiniteSupportDecisionProblem Θ) (ρ : ValidCausalPolicy A O)
        (m : ℕ), m ≤ n →
        finiteDecisionProblemValue (causalBehaviorFiniteExperiment ρ.1 ps m) P - ε ≤
          finiteDecisionProblemValue E P := by
  rw [causalBehaviorNativeDeficiencyUpTo_eq_decisionBenchmarkGap E hE ps n]
  change finiteDecisionEnvelope E (boundedCausalBehaviorExperiment ps n) ≤ ε ↔ _
  rw [finiteDecisionEnvelope_le_iff E hE _
    (fun q => causalBehaviorFiniteExperiment_valid q.2.1 q.2.2 ps q.1.1)]
  constructor
  · intro h P ρ m hm
    have hh := h P (⟨⟨m, Nat.lt_succ_of_le hm⟩, ρ⟩ : BoundedCausalCollector A O n)
    change finiteDecisionProblemValue (causalBehaviorFiniteExperiment ρ.1 ps m) P -
      finiteDecisionProblemValue E P ≤ ε at hh
    linarith
  · intro h P q
    have hh := h P q.2 q.1.1 (Nat.le_of_lt_succ q.1.2)
    change finiteDecisionProblemValue (causalBehaviorFiniteExperiment q.2.1 ps q.1.1) P -
      finiteDecisionProblemValue E P ≤ ε
    linarith

/-- Literal native sufficiency agrees with vanishing finite-budget audits. -/
theorem causalBehaviorNativelySufficient_iff_eventually_nativeAudit_lt
    (ps : Θ → CausalBehavior A O) (π : ValidCausalPolicy A O) :
    CausalBehaviorNativelySufficient ps π ↔
      ∀ n ε, 0 < ε → ∃ T, ∀ t, T ≤ t →
        causalBehaviorNativeDeficiencyUpTo (causalBehaviorFiniteExperiment π.1 ps t) ps n < ε := by
  constructor
  · intro h n ε hε
    obtain ⟨T, hT⟩ := h n ε hε
    refine ⟨T, fun t ht => ?_⟩
    obtain ⟨σ, hσ⟩ := exists_observationPlan_eq_nativeDeficiencyUpTo _
      (causalBehaviorFiniteExperiment_valid π.1 π.2 ps t) ps n
    rw [hσ]
    exact hT t ht σ
  · intro h n ε hε
    obtain ⟨T, hT⟩ := h n ε hε
    exact ⟨T, fun t ht σ =>
      (finiteDeficiency_observationPlan_le_nativeDeficiencyUpTo _
        (causalBehaviorFiniteExperiment_valid π.1 π.2 ps t) ps n σ).trans_lt (hT t ht)⟩

/-- **D4, uniform-time form:** one eventual collection time works for all
finite-support purposes and all native alternatives through the fixed budget.
The time may still depend on that budget and on the requested tolerance. -/
theorem causalBehaviorNativelySufficient_iff_uniformDecisionReadiness
    (ps : Θ → CausalBehavior A O) (π : ValidCausalPolicy A O) :
    CausalBehaviorNativelySufficient ps π ↔
      ∀ n ε, 0 < ε → ∃ T, ∀ t, T ≤ t →
        ∀ (P : FiniteSupportDecisionProblem Θ) (ρ : ValidCausalPolicy A O)
          (m : ℕ), m ≤ n →
          finiteDecisionProblemValue (causalBehaviorFiniteExperiment ρ.1 ps m) P - ε ≤
            finiteDecisionProblemValue (causalBehaviorFiniteExperiment π.1 ps t) P := by
  rw [causalBehaviorNativelySufficient_iff_eventually_nativeAudit_lt]
  constructor
  · intro h n ε hε
    obtain ⟨T, hT⟩ := h n ε hε
    exact ⟨T, fun t ht =>
      (causalBehaviorNativeDeficiencyUpTo_le_iff_decisionReadiness _
        (causalBehaviorFiniteExperiment_valid π.1 π.2 ps t) ps n ε).1 (hT t ht).le⟩
  · intro h n ε hε
    obtain ⟨T, hT⟩ := h n (ε / 2) (half_pos hε)
    refine ⟨T, fun t ht => ?_⟩
    exact ((causalBehaviorNativeDeficiencyUpTo_le_iff_decisionReadiness _
      (causalBehaviorFiniteExperiment_valid π.1 π.2 ps t) ps n (ε / 2)).2
      (hT t ht)).trans_lt (half_lt_self hε)

/-- **D4, limit form:** the purpose supremum remains inside the limit in
collection time. The finite target budget is fixed first. -/
theorem causalBehaviorNativelySufficient_iff_decisionEnvelope_tendsto_zero
    (ps : Θ → CausalBehavior A O) (π : ValidCausalPolicy A O) :
    CausalBehaviorNativelySufficient ps π ↔
      ∀ n, Tendsto (fun t => sSup (Set.range fun P : FiniteSupportDecisionProblem Θ =>
        causalBehaviorDecisionBenchmark ps n P -
          finiteDecisionProblemValue (causalBehaviorFiniteExperiment π.1 ps t) P))
        atTop (𝓝 0) := by
  simp only [← causalBehaviorAcquired_nativeAudit_eq_decisionBenchmarkGap π.1 π.2 ps]
  rw [causalBehaviorNativelySufficient_iff_eventually_nativeAudit_lt]
  constructor
  · intro h n
    apply tendsto_order.2
    constructor
    · intro a ha
      apply Filter.Eventually.of_forall
      intro t
      obtain ⟨σ, hσ⟩ := exists_observationPlan_eq_nativeDeficiencyUpTo _
        (causalBehaviorFiniteExperiment_valid π.1 π.2 ps t) ps n
      rw [hσ]
      exact ha.trans_le (finiteDeficiency_nonneg_of_valid _ _
        (causalBehaviorFiniteExperiment_valid π.1 π.2 ps t)
        (CausalObservationPlan.behaviorPlanExperiment_valid σ ps))
    · intro ε hε
      obtain ⟨T, hT⟩ := h n ε hε
      exact Filter.eventually_atTop.2 ⟨T, hT⟩
  · intro h n ε hε
    exact Filter.eventually_atTop.1 ((tendsto_order.1 (h n)).2 ε hε)

/-- Restrict the existing purpose bundle to one specified decision alphabet.
This is a restriction of the same tasks and values, not a second value definition. -/
abbrev FixedAlphabetDecisionProblem (Θ D : Type u) :=
  {P : FiniteSupportDecisionProblem Θ // P.decisions = D}

noncomputable instance fixedAlphabetDecisionProblemNonempty
    {D : Type u} [Fintype D] [Nonempty D] :
    Nonempty (FixedAlphabetDecisionProblem Θ D) := by
  classical
  let S : Finset Θ := {Classical.arbitrary Θ}
  let _ : Nonempty {θ // θ ∈ S} :=
    ⟨⟨Classical.arbitrary Θ, Finset.mem_singleton_self _⟩⟩
  exact ⟨⟨⟨S, Finset.singleton_nonempty _, D, inferInstance, inferInstance,
    uniformPrior _, isDist_uniformPrior, fun _ _ => 0,
    fun _ _ => ⟨le_rfl, zero_le_one⟩⟩, rfl⟩⟩

/-- Every purpose-specific native benchmark disadvantage is bounded by the audit. -/
theorem causalBehaviorDecisionBenchmark_sub_value_le_nativeAudit
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (ps : Θ → CausalBehavior A O) (n : ℕ) (P : FiniteSupportDecisionProblem Θ) :
    causalBehaviorDecisionBenchmark ps n P - finiteDecisionProblemValue E P ≤
      causalBehaviorNativeDeficiencyUpTo E ps n := by
  obtain ⟨σ, hσ⟩ := exists_observationPlan_eq_decisionBenchmark ps n P
  rw [hσ]
  exact (finiteDecisionProblemValue_sub_le_deficiency E _ hE
    (CausalObservationPlan.behaviorPlanExperiment_valid σ ps) P).trans
      (finiteDeficiency_observationPlan_le_nativeDeficiencyUpTo E hE ps n σ)

/-- **D8, fixed-alphabet clause:** decision alphabet `O^n` already witnesses
the whole horizon-`n` native audit. Priors still have arbitrary finite support,
and no fixed prior is asserted to attain the supremum on an infinite class. -/
theorem causalBehaviorNativeDeficiencyUpTo_eq_fixedAlphabetDecisionEnvelope
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (ps : Θ → CausalBehavior A O) (n : ℕ) :
    causalBehaviorNativeDeficiencyUpTo E ps n =
      sSup (Set.range fun P : FixedAlphabetDecisionProblem Θ (CausalObservationTrace O n) =>
        causalBehaviorDecisionBenchmark ps n P.1 - finiteDecisionProblemValue E P.1) := by
  let gaps := Set.range fun P : FixedAlphabetDecisionProblem Θ (CausalObservationTrace O n) =>
    causalBehaviorDecisionBenchmark ps n P.1 - finiteDecisionProblemValue E P.1
  have hbdd : BddAbove gaps := by
    refine ⟨causalBehaviorNativeDeficiencyUpTo E ps n, ?_⟩
    rintro _ ⟨P, rfl⟩
    exact causalBehaviorDecisionBenchmark_sub_value_le_nativeAudit E hE ps n P.1
  apply le_antisymm
  · by_contra h
    obtain ⟨σ, hσ⟩ := exists_observationPlan_eq_nativeDeficiencyUpTo E hE ps n
    have hlt : sSup gaps < finiteDeficiency E
        (CausalObservationPlan.behaviorPlanExperiment σ ps) := by
      rw [← hσ]
      exact lt_of_not_ge h
    obtain ⟨S, hS, α, u, hα, hu, hgap⟩ :=
      exists_finiteSupport_bayesGap_gt_of_lt_finiteDeficiency E _ hE
        (CausalObservationPlan.behaviorPlanExperiment_valid σ ps) hlt
    let P : FixedAlphabetDecisionProblem Θ (CausalObservationTrace O n) :=
      ⟨⟨S, hS, CausalObservationTrace O n, inferInstance, inferInstance, α, hα, u, hu⟩, rfl⟩
    have hB : finiteDecisionProblemValue
        (CausalObservationPlan.behaviorPlanExperiment σ ps) P.1 ≤
        causalBehaviorDecisionBenchmark ps n P.1 := by
      rw [causalBehaviorDecisionBenchmark_eq_planBenchmark]
      exact Finset.le_sup'
        (fun τ : CausalObservationPlan A O n =>
          finiteDecisionProblemValue (CausalObservationPlan.behaviorPlanExperiment τ ps) P.1)
        (Finset.mem_univ σ)
    have hsup := le_csSup hbdd (Set.mem_range_self P)
    change causalBehaviorDecisionBenchmark ps n P.1 - finiteDecisionProblemValue E P.1 ≤
      sSup gaps at hsup
    change sSup gaps < finiteDecisionProblemValue
      (CausalObservationPlan.behaviorPlanExperiment σ ps) P.1 -
        finiteDecisionProblemValue E P.1 at hgap
    linarith
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨P, rfl⟩
    exact causalBehaviorDecisionBenchmark_sub_value_le_nativeAudit E hE ps n P.1

end IdExp
