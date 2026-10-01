import Formal.DIAYNStateObjective
import Formal.DIAYNStateNative
import Formal.CausalProfile

/-! Every exact stationary DIAYN optimizer permanently misses the native READ
experiment. The entire deficiency interval is attained by actual skill families. -/
namespace IdExp.DIAYNState
open Finset
noncomputable section

theorem readProbability_nonneg (P : Policy) : 0 ≤ readProbability P := by
  rw [← collector_readProbability]
  exact (native_root_bounds (collector P)).1

theorem maximizer_readProbability_le (P : Policy) (θ : World) {α : ℝ}
    (hα : 0 < α) (hP : Maximizes P θ α) : readProbability P ≤ 1/2 := by
  have h := maximizer_root_read_bound P θ hα hP
  simp only [readProbability, Fin.sum_univ_two, uniformPrior,
    Fintype.card_fin, Nat.cast_ofNat]
  linarith

theorem witness_readProbability (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1/2) :
    readProbability (witness s hs0 hs1) = s := by
  simp [readProbability, witness_root, witnessRoot, uniformPrior, Fin.sum_univ_two]

/-- The infimum uses all collection times, including the empty record. -/
def eventualReadDeficiency (P : Policy) : ℝ :=
  sInf (Set.range (causalPolicyTestDeficiency (collector P) response ⟨1, readPlan⟩))

theorem eventualReadDeficiency_eq (P : Policy) :
    eventualReadDeficiency P = (1-readProbability P)/2 := by
  let f := causalPolicyTestDeficiency (collector P) response ⟨1, readPlan⟩
  have hf (t : ℕ) : f (t+1) = (1-readProbability P)/2 :=
    collector_nativeRead_deficiency P t
  have hanti : Antitone f :=
    causalPolicyTestDeficiency_antitone (collector P) response response_valid _
  have hlow (t : ℕ) : (1-readProbability P)/2 ≤ f t := by
    rw [← hf t]
    exact hanti (by omega)
  change sInf (Set.range f) = _
  apply le_antisymm
  · rw [← hf 0]
    exact csInf_le ⟨(1-readProbability P)/2, by rintro _ ⟨t, rfl⟩; exact hlow t⟩ ⟨1, rfl⟩
  · exact le_csInf (Set.range_nonempty _) (by rintro _ ⟨t, rfl⟩; exact hlow t)

/-- Full end-to-end all-optima statement for the actual MDP and source objective. -/
theorem all_optima_failure (P : Policy) (θ : World) {α : ℝ}
    (hα : 0 < α) (hP : Maximizes P θ α) :
    objective P θ α = Real.log 2 + α * Real.log 3 ∧
    0 ≤ readProbability P ∧ readProbability P ≤ 1/2 ∧
    (∀ t : ℕ, finiteDeficiency (causalFiniteExperiment (collector P).1 response (t+1))
      (causalPlanObservationExperiment 1 readPlan response) = (1-readProbability P)/2) ∧
    eventualReadDeficiency P = (1-readProbability P)/2 ∧
    1/4 ≤ eventualReadDeficiency P ∧ eventualReadDeficiency P ≤ 1/2 ∧
    CausalFinitaryDominates response readPolicy (collector P) ∧
    ¬ CausalFinitaryDominates response (collector P) readPolicy := by
  have hs0 := readProbability_nonneg P
  have hs1 := maximizer_readProbability_le P θ hα hP
  have he := eventualReadDeficiency_eq P
  have hd := collector_strictly_dominated P (by linarith)
  exact ⟨(maximizes_iff P θ hα.le).1 hP, hs0, hs1,
    collector_nativeRead_deficiency P, he, by linarith, by linarith, hd.1, hd.2⟩

/-- Every proposed reading probability is attained by a common optimum in both models. -/
theorem every_readProbability_attained (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1/2)
    {α : ℝ} (hα : 0 < α) :
    ∃ P : Policy, (∀ θ : World, Maximizes P θ α) ∧ readProbability P = s ∧
      eventualReadDeficiency P = (1-s)/2 := by
  refine ⟨witness s hs0 hs1, fun θ => witness_maximizes s hs0 hs1 θ hα.le,
    witness_readProbability s hs0 hs1, ?_⟩
  rw [eventualReadDeficiency_eq, witness_readProbability]

/-- The complete interval in the manuscript row, rather than only its endpoints. -/
theorem optimizer_deficiency_range (θ : World) {α d : ℝ} (hα : 0 < α) :
    (∃ P : Policy, Maximizes P θ α ∧ eventualReadDeficiency P = d) ↔
      1/4 ≤ d ∧ d ≤ 1/2 := by
  constructor
  · rintro ⟨P, hP, rfl⟩
    rw [eventualReadDeficiency_eq]
    have hs0 := readProbability_nonneg P
    have hs1 := maximizer_readProbability_le P θ hα hP
    constructor <;> linarith
  · rintro ⟨hd0, hd1⟩
    obtain ⟨P, hP, hs, he⟩ := every_readProbability_attained (1-2*d)
      (by linarith) (by linarith) hα
    exact ⟨P, hP θ, by linarith⟩

end
end IdExp.DIAYNState
