import Formal.FiniteCommonObjectiveMaximizers
import Formal.MOPFiniteMDP
import Formal.StateOccupancyEntropyNative
import Formal.DIAYNStateCounterexample

/-! Worst-case selection for the three prior-free MDP comparisons.
The infimum is over the actual world index AFTER evaluating the original
objective in that world. Policies never receive that index. MOP retains its
single legal terminal action, state entropy allows all valid history policies,
and DIAYN retains the fixed fair skill distribution and stationary skill family.
These results verify the proposed scalar selection rule; they do not modify the
source rewards, their temporal aggregation, or the prior-based examples. -/

namespace IdExp.MOPFiniteMDP
open IntrinsicRewardComparison
noncomputable section

abbrev LegalPolicy := {P : Policy // SourceAdmissible P}

def worstCaseValue (γ : ℝ) (P : LegalPolicy) : ℝ :=
  worstCaseObjective (fun θ (R : LegalPolicy) => objective γ R.1 θ) P

theorem worstCase_maximizer_iff (γ : ℝ) (P : LegalPolicy) :
    (∀ R, worstCaseValue γ R ≤ worstCaseValue γ P) ↔
      ∀ θ R, SourceAdmissible R → objective γ R θ ≤ objective γ P.1 θ := by
  unfold worstCaseValue
  rw [worstCase_maximizer_iff_common
    (fun θ (R : LegalPolicy) => objective γ R.1 θ) (Real.log 3)
    (fun θ R => (sourceOptimizer_maximizes γ θ R.1 R.2).trans_eq
      (sourceOptimizer_value γ θ))
    (⟨sourceOptimizer, sourceOptimizer_admissible⟩ : LegalPolicy)
    (sourceOptimizer_value γ)]
  constructor
  · intro h θ R hR
    exact h θ ⟨R, hR⟩
  · intro h θ R
    exact h θ R.1 R.2

theorem worstCase_attained (γ : ℝ) :
    ∀ P, worstCaseValue γ P ≤
      worstCaseValue γ ⟨sourceOptimizer, sourceOptimizer_admissible⟩ :=
  (worstCase_maximizer_iff γ _).2 (sourceOptimizer_maximizes γ)

theorem worstCase_maximizer_iff_root (γ : ℝ) (P : LegalPolicy) :
    (∀ R, worstCaseValue γ R ≤ worstCaseValue γ P) ↔ (P.1 none).1 0 = 1/3 := by
  rw [worstCase_maximizer_iff]
  constructor
  · intro h
    exact source_maximizing_root γ 0 P.1 P.2 (h 0)
  · intro hp θ R hR
    have he : objective γ P.1 θ = objective γ sourceOptimizer θ := by
      rw [source_objective γ P.1 P.2 θ,
        source_objective γ sourceOptimizer sourceOptimizer_admissible θ]
      change splitBinaryEntropy ((P.1 none).1 0) = splitBinaryEntropy (1/3)
      rw [hp]
    exact (sourceOptimizer_maximizes γ θ R hR).trans_eq he.symm

/-- Actual finite-prefix, infinite-record, and eventual deficiency, together
with strict native domination, for every legal worst-case optimizer. -/
theorem worstCase_all_optima_failure (γ : ℝ) (P : LegalPolicy)
    (hP : ∀ R, worstCaseValue γ R ≤ worstCaseValue γ P) :
    (P.1 none).1 0 = 1/3 ∧
    (∀ t, finiteDeficiency
      (causalFiniteExperiment (causalPolicy P.1).1 PhysicalEntropyControl.response (t+1))
      (causalPlanObservationExperiment 1 PhysicalEntropyControl.readPlan
        PhysicalEntropyControl.response) = 1/3) ∧
    finiteMeasureDeficiency
      (causalPathExperiment PhysicalEntropyControl.response
        PhysicalEntropyControl.response_valid (causalPolicy P.1))
      (rowExperiment (causalPlanObservationExperiment 1 PhysicalEntropyControl.readPlan
        PhysicalEntropyControl.response)) = 1/3 ∧
    eventualDeficiency P.1 = 1/3 ∧
    CausalFinitaryDominates PhysicalEntropyControl.response
      (causalPolicy (sourcePolicy 1 (by norm_num) (by norm_num))) (causalPolicy P.1) ∧
    ¬ CausalFinitaryDominates PhysicalEntropyControl.response (causalPolicy P.1)
      (causalPolicy (sourcePolicy 1 (by norm_num) (by norm_num))) := by
  have h := (worstCase_maximizer_iff γ P).1 hP 0
  have hl := source_maximizing_native_loss γ 0 P.1 P.2 h
  exact ⟨(worstCase_maximizer_iff_root γ P).1 hP, hl.1, hl.2,
    source_maximizing_eventualDeficiency γ 0 P.1 P.2 h,
    source_maximizing_strictly_dominated γ 0 P.1 P.2 h⟩

end
end IdExp.MOPFiniteMDP

namespace IdExp.StateOccupancyEntropy
open IntrinsicRewardComparison
noncomputable section

def worstCaseValue (γ : ℝ) (π : ValidCausalPolicy Action State) : ℝ :=
  worstCaseObjective (fun θ ρ => objective ρ θ γ) π

theorem worstCase_maximizer_iff (π : ValidCausalPolicy Action State)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    (∀ ρ, worstCaseValue γ ρ ≤ worstCaseValue γ π) ↔ π.1 [] 0 = 0 := by
  unfold worstCaseValue
  rw [worstCase_maximizer_iff_attains
    (fun θ ρ => objective ρ θ γ) (binaryEntropy γ + γ * Real.log 2)
    (fun θ ρ => objective_le ρ θ γ hγ0.le hγ1) (purePolicy 1)
    (fun θ => (objective_eq_max_iff _ θ γ hγ0 hγ1).2 (by simp [purePolicy]))]
  constructor
  · intro h
    exact (objective_eq_max_iff π 0 γ hγ0 hγ1).1 (h 0)
  · intro h θ
    exact (objective_eq_max_iff π θ γ hγ0 hγ1).2 h

theorem worstCase_attained (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∀ π, worstCaseValue γ π ≤ worstCaseValue γ (purePolicy 1) :=
  (worstCase_maximizer_iff _ γ hγ0 hγ1).2 (by simp [purePolicy])

theorem worstCase_all_optima_failure (π : ValidCausalPolicy Action State)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hπ : ∀ ρ, worstCaseValue γ ρ ≤ worstCaseValue γ π) :
    (∀ t, finiteDeficiency (causalFiniteExperiment π.1 response t)
      (causalFiniteExperiment (purePolicy 0).1 response 1) = 1/2) ∧
    eventualTestDeficiency π = 1/2 ∧
    CausalFinitaryDominates response (purePolicy 0) π ∧
    ¬ CausalFinitaryDominates response π (purePolicy 0) := by
  have hp := (worstCase_maximizer_iff π γ hγ0 hγ1).1 hπ
  exact ⟨random_deficiency π hp, random_eventualDeficiency π hp,
    random_strictly_dominated π hp⟩

end
end IdExp.StateOccupancyEntropy

namespace IdExp.DIAYNState
open IntrinsicRewardComparison
noncomputable section

/-- The world infimum leaves the uniform distribution over skills unchanged. -/
def worstCaseValue (α : ℝ) (P : Policy) : ℝ :=
  worstCaseObjective (fun θ R => objective R θ α) P

theorem worstCase_maximizer_iff (P : Policy) {α : ℝ} (hα : 0 ≤ α) :
    (∀ R, worstCaseValue α R ≤ worstCaseValue α P) ↔
      ∀ θ, Maximizes P θ α := by
  exact worstCase_maximizer_iff_common (fun θ R => objective R θ α)
    (Real.log 2 + α * Real.log 3) (fun θ R => objective_le R θ hα)
    (witness 0 (by norm_num) (by norm_num))
    (fun θ => witness_objective 0 (by norm_num) (by norm_num) θ α) P

theorem worstCase_witness_attained (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1/2)
    {α : ℝ} (hα : 0 ≤ α) :
    ∀ P, worstCaseValue α P ≤ worstCaseValue α (witness s hs0 hs1) :=
  (worstCase_maximizer_iff _ hα).2 (fun θ => witness_maximizes s hs0 hs1 θ hα)

theorem worstCase_all_optima_failure (P : Policy) {α : ℝ} (hα : 0 < α)
    (hP : ∀ R, worstCaseValue α R ≤ worstCaseValue α P) :
    0 ≤ readProbability P ∧ readProbability P ≤ 1/2 ∧
    (∀ t : ℕ, finiteDeficiency (causalFiniteExperiment (collector P).1 response (t+1))
      (causalPlanObservationExperiment 1 readPlan response) = (1-readProbability P)/2) ∧
    eventualReadDeficiency P = (1-readProbability P)/2 ∧
    1/4 ≤ eventualReadDeficiency P ∧ eventualReadDeficiency P ≤ 1/2 ∧
    CausalFinitaryDominates response readPolicy (collector P) ∧
    ¬ CausalFinitaryDominates response (collector P) readPolicy :=
  (all_optima_failure P 0 hα ((worstCase_maximizer_iff P hα.le).1 hP 0)).2

/-- The exact whole deficiency interval survives worst-case selection. -/
theorem worstCase_optimizer_deficiency_range {α d : ℝ} (hα : 0 < α) :
    (∃ P : Policy, (∀ R, worstCaseValue α R ≤ worstCaseValue α P) ∧
      eventualReadDeficiency P = d) ↔ 1/4 ≤ d ∧ d ≤ 1/2 := by
  constructor
  · rintro ⟨P, hP, hd⟩
    exact (optimizer_deficiency_range 0 hα).1
      ⟨P, (worstCase_maximizer_iff P hα.le).1 hP 0, hd⟩
  · rintro ⟨hd0, hd1⟩
    obtain ⟨P, hP, hs, he⟩ := every_readProbability_attained (1-2*d)
      (by linarith) (by linarith) hα
    exact ⟨P, (worstCase_maximizer_iff P hα.le).2 hP, by linarith⟩

end
end IdExp.DIAYNState
