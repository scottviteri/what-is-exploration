import Formal.CausalKernel

/-!
# Controlled-prefix behavior: the canonical causal world

The raw response-kernel presentation stores a probability row after every
history, including histories that have probability zero under every
intervention reaching them.  Those off-support rows are operationally
invisible and are removed by `CausalBehEq`.

This file gives the quotient a concrete, choice-free semantic presentation.
A `CausalBehavior` assigns a mass to every finite controlled history.  Actions
are inputs rather than random branches, so consistency sums only over the next
observation:

`sum_o p (h ++ [(a,o)]) = p h`.

Thus this is not one probability measure on action--observation paths.  It is
the compatible family of finite observation laws for every adaptive action
tree.  Raw valid response kernels and controlled-prefix behaviors determine
one another up to `CausalBehEq`; at a null prefix, reconstructing a response
kernel may fill the invisible row arbitrarily.
-/

namespace IdExp

open Finset

set_option linter.unusedSectionVars false

variable {A O : Type*} [Fintype A] [Fintype O]

/-- A causal world represented directly by its controlled finite-prefix
probabilities.  The action coordinate is intervened on, so the branching law
normalizes separately for every proposed action. -/
structure CausalBehavior (A O : Type*) [Fintype O] where
  /-- Probability of the observation part of a controlled history. -/
  mass : CausalHistory A O → ℝ
  /-- The empty controlled history has unit mass. -/
  root : mass [] = 1
  /-- Controlled-prefix masses are nonnegative. -/
  nonneg : ∀ h, 0 ≤ mass h
  /-- For each intervention, its possible next observations partition the
  parent event. -/
  consistent : ∀ (h : CausalHistory A O) (a : A),
    ∑ o, mass (h ++ [(a, o)]) = mass h

namespace CausalBehavior

@[ext]
theorem ext {p q : CausalBehavior A O} (h : p.mass = q.mass) : p = q := by
  cases p
  cases q
  cases h
  rfl

@[simp]
theorem mass_nil (p : CausalBehavior A O) : p.mass [] = 1 :=
  p.root

/-- A one-step controlled extension is a subevent of its prefix. -/
theorem child_le (p : CausalBehavior A O) (h : CausalHistory A O) (a : A) (o : O) :
    p.mass (h ++ [(a, o)]) ≤ p.mass h := by
  rw [← p.consistent h a]
  exact Finset.single_le_sum
    (fun y _ => p.nonneg (h ++ [(a, y)])) (Finset.mem_univ o)

/-- Every controlled-prefix mass is at most one. -/
theorem mass_le_one (p : CausalBehavior A O) (h : CausalHistory A O) :
    p.mass h ≤ 1 := by
  induction h using List.reverseRecOn with
  | nil => rw [p.root]
  | append_singleton h ao ih => exact (p.child_le h ao.1 ao.2).trans ih

/-- Hence every controlled-prefix mass lies in the unit interval. -/
theorem mass_mem_unitInterval (p : CausalBehavior A O) (h : CausalHistory A O) :
    p.mass h ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨p.nonneg h, p.mass_le_one h⟩

/-- A null prefix has only null children.  This is the key fact that makes a
canonical behavior insensitive to arbitrary response rows below impossible
histories. -/
theorem child_eq_zero_of_eq_zero (p : CausalBehavior A O)
    (h : CausalHistory A O) (a : A) (o : O) (hh : p.mass h = 0) :
    p.mass (h ++ [(a, o)]) = 0 := by
  apply le_antisymm
  · simpa [hh] using p.child_le h a o
  · exact p.nonneg _

/-- The direct behavior induced by a valid raw response kernel. -/
noncomputable def ofResponse (Q : CausalResponse A O) (hQ : IsCausalResponse Q) :
    CausalBehavior A O where
  mass := causalResponseProb Q
  root := by simp [causalResponseProb, causalResponseProbFrom]
  nonneg := fun h => causalResponseProbFrom_nonneg Q hQ [] h
  consistent := by
    intro h a
    simp_rw [causalResponseProb_append_singleton]
    rw [← Finset.mul_sum]
    simp [(hQ h a).2]

@[simp]
theorem ofResponse_mass (Q : CausalResponse A O) (hQ : IsCausalResponse Q)
    (h : CausalHistory A O) :
    (ofResponse Q hQ).mass h = causalResponseProb Q h :=
  rfl

/-- A response-kernel presentation recovered from a direct behavior.  At a
positive-mass prefix it is the conditional child/parent ratio.  At a null
prefix no conditional law is determined, so we insert an arbitrary Dirac row;
the resulting choice is behaviorally invisible. -/
noncomputable def toResponse [Nonempty O] (p : CausalBehavior A O) :
    CausalResponse A O := by
  classical
  let o0 : O := Classical.choice inferInstance
  exact fun h a o =>
    if hp : p.mass h = 0 then
      if o = o0 then 1 else 0
    else
      p.mass (h ++ [(a, o)]) / p.mass h

/-- The recovered response presentation has stochastic rows, including the
arbitrarily filled rows at null prefixes. -/
theorem toResponse_valid [Nonempty O] (p : CausalBehavior A O) :
    IsCausalResponse p.toResponse := by
  classical
  intro h a
  constructor
  · intro o
    by_cases hp : p.mass h = 0
    · simp only [toResponse, dif_pos hp]
      split <;> norm_num
    · simp only [toResponse, dif_neg hp]
      exact div_nonneg (p.nonneg _) (p.nonneg h)
  · by_cases hp : p.mass h = 0
    · simp [toResponse, hp]
    · simp only [toResponse, dif_neg hp]
      rw [← Finset.sum_div, p.consistent h a, div_self hp]

/-- Reconstructing a response presentation recovers every controlled-prefix
mass exactly. -/
@[simp]
theorem responseProb_toResponse [Nonempty O] (p : CausalBehavior A O)
    (h : CausalHistory A O) :
    causalResponseProb p.toResponse h = p.mass h := by
  induction h using List.reverseRecOn with
  | nil => simp [causalResponseProb, causalResponseProbFrom, p.root]
  | append_singleton h ao ih =>
      rw [causalResponseProb_append_singleton, ih]
      by_cases hp : p.mass h = 0
      · rw [hp, zero_mul]
        exact (p.child_eq_zero_of_eq_zero h ao.1 ao.2 hp).symm
      · simp only [toResponse, dif_neg hp]
        field_simp

/-- Passing from a behavior to any reconstructed raw presentation and back
does not change the behavior. -/
@[simp]
theorem ofResponse_toResponse [Nonempty O] (p : CausalBehavior A O) :
    ofResponse p.toResponse p.toResponse_valid = p := by
  apply CausalBehavior.ext
  funext h
  exact responseProb_toResponse p h

/-- The direct behavior is exactly the invariant classified by
`CausalBehEq`. -/
theorem ofResponse_eq_iff_causalBehEq
    {Q Q' : CausalResponse A O} (hQ : IsCausalResponse Q)
    (hQ' : IsCausalResponse Q') :
    ofResponse Q hQ = ofResponse Q' hQ' ↔ CausalBehEq Q Q' := by
  constructor
  · intro hEq h
    exact congrFun (congrArg CausalBehavior.mass hEq) h
  · intro hBeh
    apply CausalBehavior.ext
    funext h
    exact hBeh h

end CausalBehavior

/-! ## Identification of the behavioral quotient -/

/-- Forget the raw representative of a quotient world and retain just its
controlled-prefix behavior. -/
noncomputable def causalWorldToBehavior :
    CausalWorld A O → CausalBehavior A O :=
  Quotient.lift
    (fun Q : ValidCausalWorld A O => CausalBehavior.ofResponse Q.val Q.property)
    (by
      intro Q Q' hQQ'
      exact (CausalBehavior.ofResponse_eq_iff_causalBehEq Q.property Q'.property).2 hQQ')

@[simp]
theorem causalWorldToBehavior_mk (Q : CausalResponse A O) (hQ : IsCausalResponse Q) :
    causalWorldToBehavior (Quotient.mk _ ⟨Q, hQ⟩) = CausalBehavior.ofResponse Q hQ :=
  rfl

/-- Present a direct behavior as a quotient world.  The null-prefix filler in
`toResponse` disappears immediately in the quotient. -/
noncomputable def behaviorToCausalWorld [Nonempty O] (p : CausalBehavior A O) :
    CausalWorld A O :=
  Quotient.mk _ ⟨p.toResponse, p.toResponse_valid⟩

@[simp]
theorem causalWorldToBehavior_behaviorToCausalWorld [Nonempty O]
    (p : CausalBehavior A O) :
    causalWorldToBehavior (behaviorToCausalWorld p) = p :=
  CausalBehavior.ofResponse_toResponse p

@[simp]
theorem behaviorToCausalWorld_causalWorldToBehavior [Nonempty O]
    (q : CausalWorld A O) :
    behaviorToCausalWorld (causalWorldToBehavior q) = q := by
  induction q using Quotient.inductionOn with
  | _ Q =>
      apply Quotient.sound
      intro h
      exact CausalBehavior.responseProb_toResponse
        (CausalBehavior.ofResponse Q.val Q.property) h

/-- The existing behavioral quotient and direct controlled-prefix behaviors
are equivalent types.  This is the precise sense in which the latter is a
concrete normal form for the former. -/
noncomputable def causalWorldEquivBehavior [Nonempty O] :
    CausalWorld A O ≃ CausalBehavior A O where
  toFun := causalWorldToBehavior
  invFun := behaviorToCausalWorld
  left_inv := behaviorToCausalWorld_causalWorldToBehavior
  right_inv := causalWorldToBehavior_behaviorToCausalWorld

end IdExp
