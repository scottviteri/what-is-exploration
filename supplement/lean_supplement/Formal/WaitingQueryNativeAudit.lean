import Formal.WaitingQueryBehavior

/-! # The literal depth-one native audit of the countable waiting collector -/

namespace IdExp

open Finset Set

/-- Deterministic native plans on the actual controlled-behavior class have
their literal deterministic observation laws. -/
theorem waitingQuery_nativePlan_dirac {m : ℕ} (σ : CausalObservationPlan Bool Bool m) :
    CausalObservationPlan.behaviorPlanExperiment σ waitingQueryBehavior =
      diracExp (fun θ => detPlanObs m σ.toCausalPlan (waitingQueryOutput θ)) := by
  rw [CausalObservationPlan.behaviorPlanExperiment_toCausalPlan]
  change causalBehaviorPlanExperiment m σ.toCausalPlan
    (fun θ => CausalBehavior.ofResponse (detResponse (waitingQueryOutput θ))
      (isCausalResponse_detResponse _)) = _
  rw [causalBehaviorPlanExperiment_ofResponse, causalPlanObservationExperiment_det]

/-- The observation-only plan that queries immediately. -/
def waitingQueryRootPlan : CausalObservationPlan Bool Bool 1 :=
  (true, fun _ => PUnit.unit)

theorem waitingQueryRootPlan_observation (θ : WaitingQueryWorld) :
    detPlanObs 1 waitingQueryRootPlan.toCausalPlan (waitingQueryOutput θ) =
      fun _ : Fin 1 => θ.isSome := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [detPlanObs, causalTraceObservations, detTraceFin, detTraceList,
    planAction, waitingQueryOutput, waitingQueryRootPlan,
    CausalObservationPlan.toCausalPlan, CausalObservationPlan.toCausalPlanAux,
    CausalPlan.cons, CausalPlan.consFull, causalDecisionPointOfHistory]

theorem waitingQueryRootPlan_experiment :
    CausalObservationPlan.behaviorPlanExperiment waitingQueryRootPlan waitingQueryBehavior =
      diracExp (fun θ => fun _ : Fin 1 => θ.isSome) := by
  rw [waitingQuery_nativePlan_dirac]
  simp_rw [waitingQueryRootPlan_observation]

/-- Every depth-at-most-one native target is simulated with error at most
one half; this includes the horizon-zero target. -/
theorem waitingQuery_nativePlan_deficiency_le_half (t m : ℕ) (hm : m ≤ 1)
    (σ : CausalObservationPlan Bool Bool m) :
    finiteDeficiency (waitingQueryExperiment t)
      (CausalObservationPlan.behaviorPlanExperiment σ waitingQueryBehavior) ≤ (1 / 2 : ℝ) := by
  rw [waitingQueryExperiment_eq_dirac, waitingQuery_nativePlan_dirac]
  have hm' : m = 0 ∨ m = 1 := by omega
  rcases hm' with rfl | rfl
  · have hzero := finiteDeficiency_diracExp_eq_zero_of_separates
      (e := waitingQueryTrace t)
      (f := fun θ => detPlanObs 0 σ.toCausalPlan (waitingQueryOutput θ))
      (fun _ _ _ => Subsingleton.elim _ _)
    rw [hzero]
    norm_num
  · let G : CausalFiniteTrace Bool Bool t → CausalObservationTrace Bool 1 → ℝ :=
      fun _ _ => 1 / 2
    have hG : G ∈ stochasticRules _ _ := by
      intro x _
      constructor
      · intro y; norm_num [G]
      · norm_num [G, CausalObservationTrace, Fintype.card_fun]
    apply finiteDeficiency_le_of_decoder _ _ G hG
    intro θ
    rw [decodeErr_diracExp _ _ hG θ]
    norm_num [G]

/-- The root query's actual native observation experiment has deficiency
one half at every finite collection time. -/
theorem waitingQuery_nativeQuery_deficiency_eq_half (t : ℕ) :
    finiteDeficiency (waitingQueryExperiment t)
      (CausalObservationPlan.behaviorPlanExperiment waitingQueryRootPlan waitingQueryBehavior) =
        (1 / 2 : ℝ) := by
  apply le_antisymm (waitingQuery_nativePlan_deficiency_le_half t 1 le_rfl _)
  rw [waitingQueryExperiment_eq_dirac, waitingQueryRootPlan_experiment]
  apply half_le_finiteDeficiency_diracExp_of_merge
  refine ⟨some t, none, waitingQueryTrace_undetected t t (by omega), ?_⟩
  intro h
  have h0 := congrFun h 0
  simp at h0

/-- **The actual native audit remains one half at every finite time.** This
is the full countable controlled-behavior class, with literal acquired logs
and all deterministic native interventions through depth one. -/
theorem waitingQuery_nativeAudit_eq_half (t : ℕ) :
    causalBehaviorNativeDeficiencyUpTo (waitingQueryExperiment t) waitingQueryBehavior 1 =
      (1 / 2 : ℝ) := by
  have hbdd : BddAbove (causalBehaviorNativeDeficiencyValuesUpTo
      (waitingQueryExperiment t) waitingQueryBehavior 1) := by
    refine ⟨1 / 2, ?_⟩
    rintro d ⟨m, hm, σ, rfl⟩
    exact waitingQuery_nativePlan_deficiency_le_half t m hm σ
  have hmem : (1 / 2 : ℝ) ∈ causalBehaviorNativeDeficiencyValuesUpTo
      (waitingQueryExperiment t) waitingQueryBehavior 1 :=
    ⟨1, le_rfl, waitingQueryRootPlan, (waitingQuery_nativeQuery_deficiency_eq_half t).symm⟩
  apply le_antisymm
  · apply csSup_le ⟨_, hmem⟩
    rintro d ⟨m, hm, σ, rfl⟩
    exact waitingQuery_nativePlan_deficiency_le_half t m hm σ
  · exact le_csSup hbdd hmem

end IdExp
