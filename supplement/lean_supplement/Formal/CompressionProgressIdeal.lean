import Formal.CompressionProgressSwapOptimal
import Formal.KolmogorovHistoryCompressor

/-!
# Dominated optima of exact oracle compression progress on full histories

The compressor, its initial model, and its description language are fixed
before the two candidate world classes are compared. No class-specific advice
is supplied. Both actions and observations are encoded losslessly; the model
and residual are charged; every update globally minimizes over all finite
model strings. No universal-machine invariance approximation is used.
-/
namespace IdExp.CompressionProgressIdeal
open CompressionProgressSwap
open scoped ENNReal
noncomputable section

abbrev HistoryCompressor := IdealHistoryCompressor.Specification (Bool × World)

def prefixObjective (S : HistoryCompressor) (e : Bool) (π : Policy) (n : ℕ) : ℝ :=
  objective e π n (fun w => S.score (List.ofFn w))

theorem prefixObjective_eq (S : HistoryCompressor) (e f : Bool) (π : Policy) (n : ℕ) :
    prefixObjective S e π n = prefixObjective S f π n :=
  objective_eq e f π n _

/-- No finite-codebook, computability, or approximate-fitting premise. -/
theorem exact_learner_dominated_maximizer (S : HistoryCompressor) (n : ℕ) :
    ∃ (e : Bool) (π : Policy),
      (∀ ρ : Policy, prefixObjective S e ρ (n+1) ≤ prefixObjective S e π (n+1)) ∧
      CausalFinitarilyGreatest (response e) (policy e) ∧
      CausalFinitaryDominates (response e) (policy e) π ∧
      ¬ CausalFinitaryDominates (response e) π (policy e) :=
  exists_dominated_global_maximizer n (fun w => S.score (List.ofFn w))

/-- The cost is literal shortest-program complexity, including the model
charge and a conditional residual, over the full action-observation archive. -/
theorem kolmogorov_dominated_maximizer (U : KolmogorovHistoryCompressor.Machine)
    (initial : KolmogorovHistoryCompressor.Bits) (n : ℕ) :
    ∃ (e : Bool) (π : Policy),
      (∀ ρ : Policy,
        prefixObjective (KolmogorovHistoryCompressor.specification U initial) e ρ (n+1) ≤
        prefixObjective (KolmogorovHistoryCompressor.specification U initial) e π (n+1)) ∧
      CausalFinitarilyGreatest (response e) (policy e) ∧
      CausalFinitaryDominates (response e) (policy e) π ∧
      ¬ CausalFinitaryDominates (response e) π (policy e) :=
  exact_learner_dominated_maximizer (KolmogorovHistoryCompressor.specification U initial) n

/-- Prefix freedom and additive optimality are allowed, not excluded.
The stronger theorem above works for every complete partial-recursive interpreter. -/
theorem optimal_prefix_machine_dominated_maximizer (U : KolmogorovHistoryCompressor.Machine)
    (_hprefix : U.PrefixFree) (_hoptimal : U.Optimal)
    (initial : KolmogorovHistoryCompressor.Bits) (n : ℕ) :
    ∃ (e : Bool) (π : Policy),
      (∀ ρ : Policy,
        prefixObjective (KolmogorovHistoryCompressor.specification U initial) e ρ (n+1) ≤
        prefixObjective (KolmogorovHistoryCompressor.specification U initial) e π (n+1)) ∧
      CausalFinitarilyGreatest (response e) (policy e) ∧
      CausalFinitaryDominates (response e) (policy e) π ∧
      ¬ CausalFinitaryDominates (response e) π (policy e) :=
  kolmogorov_dominated_maximizer U initial n

/-- Undiscounted complete score as an extended nonnegative supremum.
This definition does not assert finiteness or an attained global maximum. -/
def completeObjective (S : HistoryCompressor) (e : Bool) (π : Policy) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (prefixObjective S e π n)

theorem completeObjective_eq (S : HistoryCompressor) (e f : Bool) (π : Policy) :
    completeObjective S e π = completeObjective S f π := by
  simp only [completeObjective, prefixObjective_eq S e f]

/-- Complete-score strictness fails too, without a convergence assumption;
finite-valued complete maximizing-policy claims require separate hypotheses. -/
theorem complete_score_order_failure (S : HistoryCompressor) :
    ∃ e : Bool, completeObjective S e (policy e) ≤ completeObjective S e (policy (!e)) ∧
      CausalFinitaryDominates (response e) (policy e) (policy (!e)) ∧
      ¬ CausalFinitaryDominates (response e) (policy (!e)) (policy e) :=
  class_independent_score_failure (completeObjective S) (completeObjective_eq S)

end
end IdExp.CompressionProgressIdeal
