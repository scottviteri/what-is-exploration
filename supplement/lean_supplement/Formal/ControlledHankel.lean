import Formal.CausalKernel
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Controlled Hankel matrices on the behavioral quotient

The entry at a past history and future open-loop test is the joint controlled
likelihood of their concatenation. In particular this is not a conditional
response row chosen at an impossible history. The matrix may have infinitely
many rows and columns; its rank is `Matrix.cRank`, the cardinal dimension of
its actual column span.
-/

namespace IdExp

set_option linter.unusedSectionVars false

variable {A O : Type*} [Fintype A] [Fintype O]

/-- The joint controlled-trace Hankel matrix, including null histories. -/
noncomputable def controlledHankel (Q : CausalResponse A O) :
    Matrix (CausalHistory A O) (CausalHistory A O) ℝ :=
  fun h τ => causalResponseProb Q (h ++ τ)

/-- Concatenation factors through the unnormalized prefix mass. -/
theorem causalResponseProbFrom_append (Q : CausalResponse A O)
    (pre h τ : CausalHistory A O) :
    causalResponseProbFrom Q pre (h ++ τ) =
      causalResponseProbFrom Q pre h * causalResponseProbFrom Q (pre ++ h) τ := by
  induction h generalizing pre with
  | nil => simp [causalResponseProbFrom]
  | cons ao h ih =>
      simp only [List.cons_append, causalResponseProbFrom]
      rw [ih]
      simp only [List.append_assoc, List.singleton_append]
      ring

theorem controlledHankel_eq_prefix_mul (Q : CausalResponse A O)
    (h τ : CausalHistory A O) :
    controlledHankel Q h τ =
      causalResponseProb Q h * causalResponseProbFrom Q h τ := by
  simpa [controlledHankel, causalResponseProb] using
    causalResponseProbFrom_append Q [] h τ

/-- An impossible controlled prefix has the zero joint Hankel row, regardless
of arbitrary raw-kernel coordinates at that prefix. -/
theorem controlledHankel_zero_of_null (Q : CausalResponse A O)
    {h : CausalHistory A O} (hh : causalResponseProb Q h = 0) :
    controlledHankel Q h = 0 := by
  funext τ
  simp [controlledHankel_eq_prefix_mul, hh]

/-- Behavioral equivalence preserves every matrix entry, hence also rank. -/
theorem controlledHankel_eq_of_causalBehEq {Q Q' : CausalResponse A O}
    (h : CausalBehEq Q Q') : controlledHankel Q = controlledHankel Q' := by
  funext pre τ
  exact h (pre ++ τ)

/-- The same matrix on an actual quotient world, without selecting a raw
continuation at a null history. -/
noncomputable def causalWorldControlledHankel (q : CausalWorld A O) :
    Matrix (CausalHistory A O) (CausalHistory A O) ℝ :=
  Quotient.liftOn q (fun Q => controlledHankel Q.val)
    (fun _ _ h => controlledHankel_eq_of_causalBehEq h)

@[simp] theorem causalWorldControlledHankel_mk (Q : CausalResponse A O)
    (hQ : IsCausalResponse Q) :
    causalWorldControlledHankel
      (Quotient.mk (validCausalBehEqSetoid A O) ⟨Q, hQ⟩) =
        controlledHankel Q := rfl

end IdExp
