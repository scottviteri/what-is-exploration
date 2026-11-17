import Formal.MOPFiniteMDP

/-! # Complete MOP return in the Separate terminals MDP
The source-admissible stationary policies have one available absorbing-state
action. Every expected stage reward after time zero vanishes. Consequently the
undiscounted series is genuinely summable and agrees with every discounted
return, world by world, before taking the worst-world criterion.
-/
namespace IdExp.MOPFiniteMDP
noncomputable section
open Filter Topology

def completeObjective (P : Policy) (θ : World) : ℝ := ∑' t, stage P θ t

theorem source_stage_hasSum (P : Policy) (hp : SourceAdmissible P) (θ : World) :
    HasSum (stage P θ) (splitBinaryEntropy ((P none).1 0)) := by
  have hs : HasSum (stage P θ) (stage P θ 0) := hasSum_single 0 (by
    intro t ht
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht
    exact source_stage_succ P hp θ k)
  simpa only [stage_zero] using hs

theorem completeObjective_eq (P : Policy) (hp : SourceAdmissible P) (θ : World) :
    completeObjective P θ = splitBinaryEntropy ((P none).1 0) :=
  (source_stage_hasSum P hp θ).tsum_eq

theorem completeObjective_eq_discounted (γ : ℝ) (P : Policy)
    (hp : SourceAdmissible P) (θ : World) : completeObjective P θ = objective γ P θ := by
  rw [completeObjective_eq P hp θ, source_objective γ P hp θ]

theorem completeObjective_world_independent (P : Policy) (hp : SourceAdmissible P)
    (θ η : World) : completeObjective P θ = completeObjective P η := by
  rw [completeObjective_eq P hp θ, completeObjective_eq P hp η]

def worstCompleteObjective (P : Policy) : ℝ :=
  min (completeObjective P 0) (completeObjective P 1)

theorem worstCompleteObjective_eq (P : Policy) (hp : SourceAdmissible P) (θ : World) :
    worstCompleteObjective P = completeObjective P θ := by
  simp only [worstCompleteObjective, completeObjective_eq P hp, min_self]

theorem complete_maximizer_iff (P : Policy) (hp : SourceAdmissible P) (θ : World) :
    (∀ R, SourceAdmissible R → completeObjective R θ ≤ completeObjective P θ) ↔
      (P none).1 0 = 1/3 := by
  constructor
  · intro hmax
    apply source_maximizing_root 1 θ P hp
    intro R hR
    simpa only [← completeObjective_eq_discounted 1 R hR θ,
      ← completeObjective_eq_discounted 1 P hp θ] using hmax R hR
  · intro hroot R hR
    rw [completeObjective_eq R hR θ, completeObjective_eq P hp θ, hroot]
    rw [(splitBinaryEntropy_eq_iff (by norm_num : (0:ℝ) ≤ 1/3)
      (by norm_num : (1/3:ℝ) ≤ 1)).mpr rfl]
    have h := sourceOptimizer_maximizes 1 θ R hR
    simpa only [source_objective 1 R hR θ, sourceOptimizer_value] using h

theorem worst_complete_maximizer_iff (P : Policy) (hp : SourceAdmissible P) :
    (∀ R, SourceAdmissible R → worstCompleteObjective R ≤ worstCompleteObjective P) ↔
      (P none).1 0 = 1/3 := by
  have hiff := complete_maximizer_iff P hp (0 : World)
  simp_rw [worstCompleteObjective_eq P hp 0]
  constructor
  · intro hm
    exact hiff.mp (fun R hR => by simpa [worstCompleteObjective_eq R hR 0] using hm R hR)
  · intro hr R hR
    rw [worstCompleteObjective_eq R hR 0]
    exact hiff.mpr hr R hR

theorem complete_optimizer_attained :
    SourceAdmissible sourceOptimizer ∧
      (∀ θ R, SourceAdmissible R → completeObjective R θ ≤ completeObjective sourceOptimizer θ) ∧
      (∀ R, SourceAdmissible R → worstCompleteObjective R ≤ worstCompleteObjective sourceOptimizer) := by
  refine ⟨sourceOptimizer_admissible, ?_, ?_⟩
  · intro θ
    exact (complete_maximizer_iff sourceOptimizer sourceOptimizer_admissible θ).mpr rfl
  · exact (worst_complete_maximizer_iff sourceOptimizer sourceOptimizer_admissible).mpr rfl

theorem complete_maximizing_native_loss (P : Policy) (hp : SourceAdmissible P) (θ : World)
    (hm : ∀ R, SourceAdmissible R → completeObjective R θ ≤ completeObjective P θ) :
    (∀ t, finiteDeficiency
      (causalFiniteExperiment (causalPolicy P).1 PhysicalEntropyControl.response (t+1))
      (causalPlanObservationExperiment 1 PhysicalEntropyControl.readPlan
        PhysicalEntropyControl.response) = 1/3) ∧
    finiteMeasureDeficiency
      (causalPathExperiment PhysicalEntropyControl.response
        PhysicalEntropyControl.response_valid (causalPolicy P))
      (rowExperiment (causalPlanObservationExperiment 1 PhysicalEntropyControl.readPlan
        PhysicalEntropyControl.response)) = 1/3 := by
  apply source_maximizing_native_loss 1 θ P hp
  intro R hR
  simpa only [← completeObjective_eq_discounted 1 R hR θ,
    ← completeObjective_eq_discounted 1 P hp θ] using hm R hR

theorem worst_complete_maximizing_strictly_dominated (P : Policy) (hp : SourceAdmissible P)
    (hm : ∀ R, SourceAdmissible R → worstCompleteObjective R ≤ worstCompleteObjective P) :
    CausalFinitaryDominates PhysicalEntropyControl.response
      (causalPolicy (sourcePolicy 1 (by norm_num) (by norm_num))) (causalPolicy P) ∧
    ¬ CausalFinitaryDominates PhysicalEntropyControl.response (causalPolicy P)
      (causalPolicy (sourcePolicy 1 (by norm_num) (by norm_num))) := by
  apply source_maximizing_strictly_dominated 1 0 P hp
  intro R hR
  rw [← completeObjective_eq_discounted 1 R hR 0,
    ← completeObjective_eq_discounted 1 P hp 0,
    ← worstCompleteObjective_eq R hR 0, ← worstCompleteObjective_eq P hp 0]
  exact hm R hR

end
end IdExp.MOPFiniteMDP
