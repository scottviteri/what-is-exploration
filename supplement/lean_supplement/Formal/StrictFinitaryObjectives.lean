import Formal.FinitaryObjectiveCore
import Formal.TerminalFinitaryReduction

/-!
# Terminal scores as strictly finitary objectives

The abstract objective API is re-exported from `FinitaryObjectiveCore`.
This module supplies the additional terminal-experiment specialization.
-/

namespace IdExp

section Abstract

variable {P X : Type*} {K : P → ℕ → X} {δ : X → X → ℝ}

/-- A strictly simulation-monotone terminal score is a strictly finitarily
monotone objective, connecting the two modules. -/
theorem terminalScore_strictlyFinitaryMonotone (T : P → X)
    (hδ : ∀ x y, 0 ≤ δ x y) (htri : ∀ x y z, δ x z ≤ δ x y + δ y z)
    (hT : IsTerminalFor K δ T) {S : X → ℝ} (hS : IsStrictSimulationScore δ S) :
    IsStrictlyFinitaryMonotone K δ (terminalScore T S) :=
  ⟨fun _ _ hdom => terminalScore_le_of_finitaryDominates K δ T hδ htri hT hS hdom,
   fun _ _ hdom hnot => terminalScore_lt_of_strict_finitaryDominates K δ T hδ htri hT hS hdom hnot⟩

end Abstract

end IdExp
