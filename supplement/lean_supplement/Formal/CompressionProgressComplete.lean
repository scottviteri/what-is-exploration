import Formal.CompressionProgressCompleteFinite
import Formal.CompressionProgressCompleteUnbounded

/-!
# Complete-return dominated optima of ideal full-history compression

The exact learner and its background are fixed before the revealing-button
wiring. Complete returns are extended nonnegative values. The bounded branch
has a finite attained value; the unbounded branch constructs an actual
randomized history policy attaining infinity. Neither branch assumes a
complete maximizer exists.
-/
namespace IdExp.CompressionProgressIdeal
open CompressionProgressSwap
open scoped ENNReal
noncomputable section

/-- Every exact natural-cost learner has a complete global maximizer that
permanently misses an available native target in one of the two fixed wirings.
The maximum need not be finite. -/
theorem exact_learner_complete_dominated_maximizer (S : HistoryCompressor) :
    ∃ (e : Bool) (π : Policy),
      π.1 [] e = 0 ∧
      (∀ ρ : Policy, completeObjective S e ρ ≤ completeObjective S e π) ∧
      CausalFinitarilyGreatest (response e) (policy e) ∧
      CausalFinitaryDominates (response e) (policy e) π ∧
      ¬ CausalFinitaryDominates (response e) π (policy e) ∧
      (∀ t : ℕ, finiteDeficiency (causalFiniteExperiment π.1 (response e) t)
        (causalFiniteExperiment (policy e).1 (response e) 1) = 1 / 2) := by
  classical
  by_cases hb : ∃ B : ℝ, ∀ (π : Policy) (n : ℕ), prefixObjective S false π n ≤ B
  · obtain ⟨B, hB⟩ := hb
    obtain ⟨e, π, hroot, _, hmax, hgreat, hdom, hnot, hdef⟩ :=
      CompressionProgressCompleteFinite.exists_complete_dominated_maximizer_of_prefix_bound
        S B hB
    exact ⟨e, π, hroot, hmax, hgreat, hdom, hnot, hdef⟩
  · push Not at hb
    obtain ⟨e, π, hroot, _, hmax, hgreat, hdom, hnot, hdef⟩ :=
      exists_complete_dominated_maximizer_of_unbounded S hb
    exact ⟨e, π, hroot, hmax, hgreat, hdom, hnot, hdef⟩

/-- Literal shortest-program model and residual costs, every finite binary
model, the complete action-observation archive, and the full undiscounted score. -/
theorem kolmogorov_complete_dominated_maximizer
    (U : KolmogorovHistoryCompressor.Machine)
    (initial : KolmogorovHistoryCompressor.Bits) :
    ∃ (e : Bool) (π : Policy),
      π.1 [] e = 0 ∧
      (∀ ρ : Policy,
        completeObjective (KolmogorovHistoryCompressor.specification U initial) e ρ ≤
        completeObjective (KolmogorovHistoryCompressor.specification U initial) e π) ∧
      CausalFinitarilyGreatest (response e) (policy e) ∧
      CausalFinitaryDominates (response e) (policy e) π ∧
      ¬ CausalFinitaryDominates (response e) π (policy e) ∧
      (∀ t : ℕ, finiteDeficiency (causalFiniteExperiment π.1 (response e) t)
        (causalFiniteExperiment (policy e).1 (response e) 1) = 1 / 2) :=
  exact_learner_complete_dominated_maximizer
    (KolmogorovHistoryCompressor.specification U initial)

/-- The literal shortest-program result for every fixed archive-dependent
minimizer selection, with no restriction to the default classical choice. -/
theorem kolmogorov_selected_complete_dominated_maximizer
    (U : KolmogorovHistoryCompressor.Machine)
    (initial : KolmogorovHistoryCompressor.Bits)
    (select : (h : History) → {m : KolmogorovHistoryCompressor.Bits //
      ∀ other : KolmogorovHistoryCompressor.Bits,
        KolmogorovHistoryCompressor.twoPartCost U m h ≤
          KolmogorovHistoryCompressor.twoPartCost U other h}) :
    ∃ (e : Bool) (π : Policy),
      π.1 [] e = 0 ∧
      (∀ ρ : Policy,
        completeObjective
          (KolmogorovHistoryCompressor.specificationWithSelection U initial select) e ρ ≤
        completeObjective
          (KolmogorovHistoryCompressor.specificationWithSelection U initial select) e π) ∧
      CausalFinitarilyGreatest (response e) (policy e) ∧
      CausalFinitaryDominates (response e) (policy e) π ∧
      ¬ CausalFinitaryDominates (response e) π (policy e) ∧
      (∀ t : ℕ, finiteDeficiency (causalFiniteExperiment π.1 (response e) t)
        (causalFiniteExperiment (policy e).1 (response e) 1) = 1 / 2) :=
  exact_learner_complete_dominated_maximizer
    (KolmogorovHistoryCompressor.specificationWithSelection U initial select)

/-- The complete obstruction permits any supplied optimal prefix interpreter;
optimality does not imply that its lifetime return is finite. -/
theorem optimal_prefix_machine_complete_dominated_maximizer
    (U : KolmogorovHistoryCompressor.Machine)
    (_hprefix : U.PrefixFree) (_hoptimal : U.Optimal)
    (initial : KolmogorovHistoryCompressor.Bits) :
    ∃ (e : Bool) (π : Policy),
      π.1 [] e = 0 ∧
      (∀ ρ : Policy,
        completeObjective (KolmogorovHistoryCompressor.specification U initial) e ρ ≤
        completeObjective (KolmogorovHistoryCompressor.specification U initial) e π) ∧
      CausalFinitarilyGreatest (response e) (policy e) ∧
      CausalFinitaryDominates (response e) (policy e) π ∧
      ¬ CausalFinitaryDominates (response e) π (policy e) ∧
      (∀ t : ℕ, finiteDeficiency (causalFiniteExperiment π.1 (response e) t)
        (causalFiniteExperiment (policy e).1 (response e) 1) = 1 / 2) :=
  kolmogorov_complete_dominated_maximizer U initial

end
end IdExp.CompressionProgressIdeal
