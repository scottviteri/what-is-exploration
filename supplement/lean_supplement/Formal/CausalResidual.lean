import Formal.CausalSubbehavior

/-!
# Residual behaviors and controlled predictive states

**Relevance:** the environment-side causal state used by the coupled
pair-process notes (`Paper/research/coupled_causal_trajectories_2026-09-19`,
`TheoryDocs/COUPLED_CAUSAL_STATES.md`) and by the class-extension note
(`Paper/research/causal_state_extensions_2026-09-19`, eq. `residual`).

For a controlled-prefix behavior `p` and a history `h` of positive mass, the
*residual* `p / h` is the normalized continuation behavior

`(p / h) u = p (h ++ u) / p h`.

It is exactly `CausalBehavior.reachableContinuation`, repackaged under the
name the notes use, with the algebra the pair process needs: the
multiplicative factorization `p (h ++ u) = p h * (p / h) u`, positivity
transfer, composition `(p / h) / u = p / (h ++ u)`, and the one-step
marginal row.  Two positive-mass histories have the same *controlled
predictive state* when their residuals agree.  `PredictiveEq` states that
relation without division, as a cross-multiplied identity of joint masses,
so it also makes sense at null histories; on positive-mass histories it is
equivalent to equality of residuals and is an equivalence relation.

**Scope.**  Everything here is finite-alphabet controlled-prefix algebra.
Nothing is claimed about the policy side (see `PolicyBehavior.lean`), about
the coupled process, or about sufficiency of any policy.  A residual at a
null prefix is *not* defined: the positivity hypothesis is an explicit
argument, matching the notes' remark that the unnormalized shift is the only
canonical object there.
-/

namespace IdExp

open Finset

set_option linter.unusedSectionVars false

variable {A O : Type*} [Fintype A] [Fintype O]

namespace CausalBehavior

/-- The residual (normalized continuation) behavior `p / h` at a
positive-mass controlled history `h`.  Definitionally the normalization of
the total prefix shift of `p` viewed as a subbehavior. -/
noncomputable def residual (p : CausalBehavior A O) (h : CausalHistory A O)
    (hp : 0 < p.mass h) : CausalBehavior A O :=
  (p.toSubbehavior.shift h).normalize (by simpa using hp)

/-- `residual` is the existing reachable continuation, by definition. -/
theorem residual_eq_reachableContinuation (p : CausalBehavior A O)
    (h : CausalHistory A O) (hp : 0 < p.mass h) :
    p.residual h hp = p.reachableContinuation h hp :=
  rfl

/-- Residual mass is the joint mass of the concatenation divided by the
prefix mass. -/
@[simp]
theorem residual_mass (p : CausalBehavior A O) (h : CausalHistory A O)
    (hp : 0 < p.mass h) (u : CausalHistory A O) :
    (p.residual h hp).mass u = p.mass (h ++ u) / p.mass h := by
  change (p.toSubbehavior.shift h).mass u /
      (p.toSubbehavior.shift h).mass [] = _
  simp

/-- The one-step marginal of a residual is the response row at `h`:
`(p / h) [(a, o)] = p (h ++ [(a, o)]) / p h`. -/
theorem residual_mass_singleton (p : CausalBehavior A O)
    (h : CausalHistory A O) (hp : 0 < p.mass h) (a : A) (o : O) :
    (p.residual h hp).mass [(a, o)] = p.mass (h ++ [(a, o)]) / p.mass h :=
  residual_mass p h hp [(a, o)]

/-- Exact multiplicative factorization of a joint controlled mass into its
prefix mass and residual mass. -/
theorem mass_append_eq_mul_residual (p : CausalBehavior A O)
    (h : CausalHistory A O) (hp : 0 < p.mass h) (u : CausalHistory A O) :
    p.mass (h ++ u) = p.mass h * (p.residual h hp).mass u := by
  rw [residual_mass]
  field_simp

/-- The residual at the empty history is the behavior itself. -/
@[simp]
theorem residual_nil (p : CausalBehavior A O) (h1 : 0 < p.mass []) :
    p.residual [] h1 = p := by
  apply CausalBehavior.ext
  funext u
  simp

/-- A residual mass is positive exactly when the concatenated joint mass is
positive. -/
theorem residual_mass_pos_iff (p : CausalBehavior A O)
    (h : CausalHistory A O) (hp : 0 < p.mass h) (u : CausalHistory A O) :
    0 < (p.residual h hp).mass u ↔ 0 < p.mass (h ++ u) := by
  rw [residual_mass]
  constructor
  · intro hd
    rcases (p.nonneg (h ++ u)).lt_or_eq with hlt | heq
    · exact hlt
    · rw [← heq, zero_div] at hd
      exact absurd hd (lt_irrefl 0)
  · intro hpos
    exact div_pos hpos hp

/-- A residual mass is null exactly when the concatenated joint mass is
null. -/
theorem residual_mass_eq_zero_iff (p : CausalBehavior A O)
    (h : CausalHistory A O) (hp : 0 < p.mass h) (u : CausalHistory A O) :
    (p.residual h hp).mass u = 0 ↔ p.mass (h ++ u) = 0 := by
  rw [residual_mass]
  exact div_eq_zero_iff.trans (or_iff_left hp.ne')

/-- Residuals compose: `(p / h) / u = p / (h ++ u)` whenever the
concatenation has positive mass. -/
theorem residual_residual (p : CausalBehavior A O)
    (h u : CausalHistory A O) (hp : 0 < p.mass h)
    (hu : 0 < p.mass (h ++ u)) :
    (p.residual h hp).residual u ((p.residual_mass_pos_iff h hp u).2 hu) =
      p.residual (h ++ u) hu := by
  apply CausalBehavior.ext
  funext v
  simp only [residual_mass, List.append_assoc]
  exact div_div_div_cancel_right₀ hp.ne' _ _

/-! ## Controlled predictive-state equivalence -/

/-- Two histories have the same controlled predictive state when their joint
continuation masses are proportional: `p (h ++ u) * p h' = p (h' ++ u) * p h`
for every future word `u`.  Stated without division so that it is meaningful
at every history; at positive-mass histories it is equality of residuals
(`predictiveEq_iff_residual_eq`). -/
def PredictiveEq (p : CausalBehavior A O) (h h' : CausalHistory A O) : Prop :=
  ∀ u, p.mass (h ++ u) * p.mass h' = p.mass (h' ++ u) * p.mass h

/-- At positive-mass histories, predictive equivalence is exactly equality of
the two residual behaviors. -/
theorem predictiveEq_iff_residual_eq (p : CausalBehavior A O)
    {h h' : CausalHistory A O} (hp : 0 < p.mass h) (hp' : 0 < p.mass h') :
    p.PredictiveEq h h' ↔ p.residual h hp = p.residual h' hp' := by
  constructor
  · intro hEq
    apply CausalBehavior.ext
    funext u
    simp only [residual_mass]
    rw [div_eq_div_iff hp.ne' hp'.ne']
    exact hEq u
  · intro hEq u
    have hu := congrFun (congrArg CausalBehavior.mass hEq) u
    simp only [residual_mass] at hu
    rwa [div_eq_div_iff hp.ne' hp'.ne'] at hu

/-- Predictive equivalence is reflexive. -/
theorem predictiveEq_refl (p : CausalBehavior A O) (h : CausalHistory A O) :
    p.PredictiveEq h h :=
  fun _ => rfl

/-- Predictive equivalence is symmetric. -/
theorem predictiveEq_symm (p : CausalBehavior A O)
    {h h' : CausalHistory A O} (H : p.PredictiveEq h h') :
    p.PredictiveEq h' h :=
  fun u => (H u).symm

/-- Predictive equivalence is transitive through a positive-mass middle
history. -/
theorem predictiveEq_trans (p : CausalBehavior A O)
    {h h' h'' : CausalHistory A O} (hp' : 0 < p.mass h')
    (H₁ : p.PredictiveEq h h') (H₂ : p.PredictiveEq h' h'') :
    p.PredictiveEq h h'' := by
  intro u
  apply mul_right_cancel₀ hp'.ne'
  calc
    p.mass (h ++ u) * p.mass h'' * p.mass h'
        = (p.mass (h ++ u) * p.mass h') * p.mass h'' := by ring
    _ = (p.mass (h' ++ u) * p.mass h) * p.mass h'' := by rw [H₁ u]
    _ = (p.mass (h' ++ u) * p.mass h'') * p.mass h := by ring
    _ = (p.mass (h'' ++ u) * p.mass h') * p.mass h := by rw [H₂ u]
    _ = p.mass (h'' ++ u) * p.mass h * p.mass h' := by ring

/-- Predictive equivalence is an equivalence relation on the positive-mass
histories of a behavior. -/
def predictiveSetoid (p : CausalBehavior A O) :
    Setoid {h : CausalHistory A O // 0 < p.mass h} where
  r h h' := p.PredictiveEq h.1 h'.1
  iseqv :=
    ⟨fun h => p.predictiveEq_refl h.1,
     fun H => p.predictiveEq_symm H,
     fun {_ h' _} H₁ H₂ => p.predictiveEq_trans h'.2 H₁ H₂⟩

/-- Under the setoid, two positive-mass histories are related exactly when
their residuals agree. -/
theorem predictiveSetoid_iff (p : CausalBehavior A O)
    (h h' : {h : CausalHistory A O // 0 < p.mass h}) :
    (p.predictiveSetoid).r h h' ↔ p.residual h.1 h.2 = p.residual h'.1 h'.2 :=
  p.predictiveEq_iff_residual_eq h.2 h'.2

end CausalBehavior

end IdExp
