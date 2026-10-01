import Formal.StrictFinitaryObjective
import Formal.WeightedObjectiveRegularity
import Formal.CausalBehaviorCapability

/-!
# Policy-topology regularity of a strictly finitary objective

The topology is the actual product/subtype topology on valid behavioral
policies. Finite-time deficiency factors through the continuous restriction
to finitely many policy rows, uniformly over an arbitrary nonempty world
class. Summable weights then give continuous finite-time scores converging
increasingly to the lower semicontinuous complete objective.
-/

namespace IdExp

open Filter Topology

/-- The product topology on all history-indexed action probabilities. -/
instance causalPolicyTopologicalSpace (A O : Type*) : TopologicalSpace (CausalPolicy A O) :=
  inferInstanceAs (TopologicalSpace (CausalHistory A O → A → ℝ))

noncomputable section

variable {A O Θ : Type*} [Fintype A] [Fintype O]
  [Nonempty A] [Nonempty O] [Nonempty Θ]

omit [Fintype O] [Nonempty A] [Nonempty O] in
/-- Restriction to a finite policy table is continuous in the product topology. -/
theorem continuous_silentHorizonRowsOfPolicy (H : ℕ) :
    Continuous (silentHorizonRowsOfPolicy (A := A) (O := O) H) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun d =>
    (continuous_apply (causalDecisionHistory d)).comp continuous_subtype_val

/-- A fixed finite target gives a continuous deficiency coordinate on full policies. -/
theorem continuous_causalPrefixDeficiency {Y : Type*} [Fintype Y]
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (H : ℕ) (F : FiniteExperiment Θ Y) (hF : IsFiniteExperiment F) :
    Continuous (fun π : ValidCausalPolicy A O =>
      finiteDeficiency (causalFiniteExperiment π.1 Qs H) F) := by
  have := nonempty_of_isFiniteExperiment F hF
  have h := (continuous_finiteDeficiency_silentHorizonPolicyOfRows Qs hQ H F hF).comp
    (continuous_silentHorizonRowsOfPolicy H)
  change Continuous (fun π : ValidCausalPolicy A O =>
    finiteDeficiency (policyRowExperiment Qs H (silentHorizonRowsOfPolicy H π)) F) at h
  simpa only [policyRowExperiment_rowsOfPolicy] using h

/-- The finite-time weighted score, with the entire summable target family retained. -/
def weightedFinitaryPrefixObjective (Qs : Θ → CausalResponse A O)
    (T : ∀ n : ℕ, ℕ → FiniteExperiment Θ (CausalFiniteTrace A O n))
    (w : ℕ × ℕ → ℝ) (t : ℕ) (π : ValidCausalPolicy A O) : ℝ :=
  weightedScore w (fun p π => finiteDeficiency (causalFiniteExperiment π.1 Qs t) (T p.1 p.2)) π

omit [Nonempty A] [Nonempty O] in
theorem causalPrefixDeficiency_mem_unitInterval {Y : Type*} [Fintype Y]
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (H : ℕ) (F : FiniteExperiment Θ Y) (hF : IsFiniteExperiment F)
    (π : ValidCausalPolicy A O) :
    0 ≤ finiteDeficiency (causalFiniteExperiment π.1 Qs H) F ∧
      finiteDeficiency (causalFiniteExperiment π.1 Qs H) F ≤ 1 := by
  have := nonempty_of_isFiniteExperiment F hF
  exact ⟨finiteDeficiency_nonneg_of_valid _ _ (causalFiniteExperiment_valid π.1 π.2 Qs hQ H) hF,
    finiteDeficiency_le_one_of_valid _ _ (causalFiniteExperiment_valid π.1 π.2 Qs hQ H) hF⟩

variable (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (T : ∀ n : ℕ, ℕ → FiniteExperiment Θ (CausalFiniteTrace A O n))
    (hT : ∀ n k, IsFiniteExperiment (T n k))
    (w : ℕ × ℕ → ℝ) (hw0 : ∀ p, 0 ≤ w p) (hw : Summable w)

include hQ hT hw0 hw in
theorem continuous_weightedFinitaryPrefixObjective (t : ℕ) :
    Continuous (weightedFinitaryPrefixObjective Qs T w t) :=
  continuous_weightedScore hw0 hw
    (fun p π => causalPrefixDeficiency_mem_unitInterval Qs hQ t _ (hT p.1 p.2) π)
    (fun p => continuous_causalPrefixDeficiency Qs hQ t _ (hT p.1 p.2))

include hQ hT hw0 hw in
theorem monotone_weightedFinitaryPrefixObjective (π : ValidCausalPolicy A O) :
    Monotone (fun t => weightedFinitaryPrefixObjective Qs T w t π) :=
  monotone_weightedScore_of_antitone hw0 hw
    (fun t p π => causalPrefixDeficiency_mem_unitInterval Qs hQ t _ (hT p.1 p.2) π)
    (fun p π => deficiency_record_antitone Qs hQ π _ (hT p.1 p.2)) π

include hQ hT hw0 hw in
theorem tendsto_weightedFinitaryPrefixObjective (π : ValidCausalPolicy A O) :
    Tendsto (fun t => weightedFinitaryPrefixObjective Qs T w t π) atTop
      (𝓝 (weightedFinitaryObjective Qs T w π)) :=
  tendsto_weightedScore hw0 hw
    (fun t p π => causalPrefixDeficiency_mem_unitInterval Qs hQ t _ (hT p.1 p.2) π)
    (fun p π => tendsto_eventualLoss Qs hQ π _ (hT p.1 p.2)) π

include hQ hT hw0 hw in
theorem weightedFinitaryObjective_eq_iSup (π : ValidCausalPolicy A O) :
    weightedFinitaryObjective Qs T w π = ⨆ t, weightedFinitaryPrefixObjective Qs T w t π :=
  weightedScore_eq_iSup hw0 hw
    (fun t p π => causalPrefixDeficiency_mem_unitInterval Qs hQ t _ (hT p.1 p.2) π)
    (fun p π => deficiency_record_antitone Qs hQ π _ (hT p.1 p.2))
    (fun p π => tendsto_eventualLoss Qs hQ π _ (hT p.1 p.2)) π

include hQ hT hw0 hw in
theorem lowerSemicontinuous_weightedFinitaryObjective :
    LowerSemicontinuous (weightedFinitaryObjective Qs T w) :=
  lowerSemicontinuous_weightedScore hw0 hw
    (fun t p π => causalPrefixDeficiency_mem_unitInterval Qs hQ t _ (hT p.1 p.2) π)
    (fun t p => continuous_causalPrefixDeficiency Qs hQ t _ (hT p.1 p.2))
    (fun p π => deficiency_record_antitone Qs hQ π _ (hT p.1 p.2))
    (fun p π => tendsto_eventualLoss Qs hQ π _ (hT p.1 p.2))

include hQ hw in
/-- Full causal assembly for `thm:strict-finitary-objective`, including native
policy witnesses, order representation, and product-topology regularity. -/
theorem exists_regular_strictly_finitary_objective
    (hpos : ∀ p, 0 < w p) (hw1 : ∑' p, w p = 1) :
    ∃ ρ : ℕ → ℕ → ValidCausalPolicy A O,
      let targets := fun n k => causalFiniteExperiment (ρ n k).1 Qs n
      (∀ π σ : ValidCausalPolicy A O, CausalFinitaryDominates Qs π σ ↔
        ∀ n k, eventualLoss Qs π (targets n k) ≤ eventualLoss Qs σ (targets n k)) ∧
      (∀ π, weightedFinitaryObjective Qs targets w π ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ π σ, CausalFinitaryDominates Qs π σ →
        weightedFinitaryObjective Qs targets w σ ≤ weightedFinitaryObjective Qs targets w π) ∧
      (∀ π σ, CausalFinitaryDominates Qs π σ → ¬ CausalFinitaryDominates Qs σ π →
        weightedFinitaryObjective Qs targets w σ < weightedFinitaryObjective Qs targets w π) ∧
      (∀ t, Continuous (weightedFinitaryPrefixObjective Qs targets w t)) ∧
      (∀ π, Monotone (fun t => weightedFinitaryPrefixObjective Qs targets w t π)) ∧
      (∀ π, Tendsto (fun t => weightedFinitaryPrefixObjective Qs targets w t π) atTop
        (𝓝 (weightedFinitaryObjective Qs targets w π))) ∧
      (∀ π, weightedFinitaryObjective Qs targets w π =
        ⨆ t, weightedFinitaryPrefixObjective Qs targets w t π) ∧
      LowerSemicontinuous (weightedFinitaryObjective Qs targets w) := by
  obtain ⟨ρ, hρ⟩ := exists_densePolicyRecordFamily Qs hQ
  let targets := fun n k => causalFiniteExperiment (ρ n k).1 Qs n
  have hn : ∀ p, 0 ≤ w p := fun p => (hpos p).le
  exact ⟨ρ,
    causalFinitaryDominates_iff_eventualLoss Qs hQ targets hρ,
    weightedFinitaryObjective_mem_unitInterval Qs hQ targets hρ.1 w hn hw hw1,
    fun π σ hdom => weightedFinitaryObjective_mono Qs hQ targets hρ w hn hw hdom,
    fun π σ hdom hnot => weightedFinitaryObjective_strict Qs hQ targets hρ w hpos hw hdom hnot,
    continuous_weightedFinitaryPrefixObjective Qs hQ targets hρ.1 w hn hw,
    monotone_weightedFinitaryPrefixObjective Qs hQ targets hρ.1 w hn hw,
    tendsto_weightedFinitaryPrefixObjective Qs hQ targets hρ.1 w hn hw,
    weightedFinitaryObjective_eq_iSup Qs hQ targets hρ.1 w hn hw,
    lowerSemicontinuous_weightedFinitaryObjective Qs hQ targets hρ.1 w hn hw⟩

include hw in
/-- The complete theorem for controlled-prefix behaviors. All response validity
assumptions are discharged by the canonical presentation; the statement itself
uses only behavior-induced records and the native finitary order. -/
theorem exists_causalBehavior_regular_strictly_finitary_objective
    (ps : Θ → CausalBehavior A O) (hpos : ∀ p, 0 < w p) (hw1 : ∑' p, w p = 1) :
    ∃ ρ : ℕ → ℕ → ValidCausalPolicy A O,
      let targets := fun n k => causalBehaviorFiniteExperiment (ρ n k).1 ps n
      let loss := fun n k (π : ValidCausalPolicy A O) =>
        ⨅ t : ℕ, finiteDeficiency (causalBehaviorFiniteExperiment π.1 ps t) (targets n k)
      let score := weightedScore w (fun p π => loss p.1 p.2 π)
      let prefixScore := fun t => weightedScore w (fun p (π : ValidCausalPolicy A O) =>
        finiteDeficiency (causalBehaviorFiniteExperiment π.1 ps t) (targets p.1 p.2))
      (∀ π σ : ValidCausalPolicy A O, CausalBehaviorFinitaryDominates ps π σ ↔
        ∀ n k, loss n k π ≤ loss n k σ) ∧
      (∀ π, score π ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ π σ, CausalBehaviorFinitaryDominates ps π σ → score σ ≤ score π) ∧
      (∀ π σ, CausalBehaviorFinitaryDominates ps π σ →
        ¬ CausalBehaviorFinitaryDominates ps σ π → score σ < score π) ∧
      (∀ t, Continuous (prefixScore t)) ∧
      (∀ π, Monotone (fun t => prefixScore t π)) ∧
      (∀ π, Tendsto (fun t => prefixScore t π) atTop (𝓝 (score π))) ∧
      (∀ π, score π = ⨆ t, prefixScore t π) ∧
      LowerSemicontinuous score := by
  have h := exists_regular_strictly_finitary_objective (causalBehaviorResponsePresentation ps)
    (causalBehaviorResponsePresentation_valid ps) w hw hpos hw1
  dsimp only at h ⊢
  unfold weightedFinitaryObjective weightedFinitaryPrefixObjective weightedScore eventualLoss at h
  unfold weightedScore
  simpa only [causalBehaviorFiniteExperiment_eq_toResponse,
    causalBehaviorFinitaryDominates_iff_raw] using h

end
end IdExp
