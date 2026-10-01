import Mathlib

/-!
# Finite probability primitives

Probability vectors, full support, and entropy shared by the general causal
and experiment theory and the retained finite-POMDP specialization. This
foundation deliberately has no dependency on a model of the environment.
-/

namespace IdExp

variable {C : Type*} [Fintype C]

/-- A finite probability vector. -/
def IsDist (p : C → ℝ) : Prop := (∀ c, 0 ≤ p c) ∧ ∑ c, p c = 1

/-- Full support (PDF: "full-support prior"). -/
def FullSupport (p : C → ℝ) : Prop := ∀ c, 0 < p c

/-- Shannon entropy in nats; `Real.log 0 = 0` gives the `0 log 0 = 0` convention. -/
noncomputable def ent (p : C → ℝ) : ℝ := ∑ c, Real.negMulLog (p c)

end IdExp
