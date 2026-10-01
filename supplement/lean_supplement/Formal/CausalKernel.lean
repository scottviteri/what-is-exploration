import Formal.FiniteProbability

/-!
# Causal response kernels: executable presentations of causal behavior

**Relevance:** compatibility and construction layer for the current paper.  A valid response
kernel is a convenient history-indexed presentation of a world, but rows below controlled-null
histories are arbitrary presentation data.  `CausalBehavior.lean` gives the canonical
finite-alphabet semantic carrier as globally consistent controlled-prefix masses and proves it
equivalent to the behavioral quotient defined here.

A response presentation is a history-indexed next-observation distribution.  A policy is a
history-indexed action distribution.  Histories contain exactly the action--observation pairs
produced so far; there is no distinguished initial observation and no hidden-state or Markov
assumption. In particular, a time-zero record is empty. The older `Hist` in `Basic.lean`
includes an initial observation before action zero; the marginalization in
`POMDPCausalBehavior.lean` is not an information-preserving reindexing of policies.
See the interface-convention table in `Formal/README.md`.
-/

namespace IdExp

open Finset

variable {A O : Type*} [Fintype A] [Fintype O]

/-- A finite causal history, in chronological order. -/
abbrev CausalHistory (A O : Type*) := List (A × O)

/-- A causal action--observation response law. -/
def CausalResponse (A O : Type*) := CausalHistory A O → A → O → ℝ

/-- Every response row is a probability vector. -/
def IsCausalResponse (Q : CausalResponse A O) : Prop :=
  ∀ h a, IsDist (Q h a)

/-- A randomized, history-dependent policy for the causal interface. -/
def CausalPolicy (A O : Type*) := CausalHistory A O → A → ℝ

/-- Every policy row is a probability vector. -/
def IsCausalPolicy (π : CausalPolicy A O) : Prop :=
  ∀ h, IsDist (π h)

/-- Probability of a continuation, starting from an already realized prefix. -/
noncomputable def causalTraceProbFrom (π : CausalPolicy A O) (Q : CausalResponse A O) :
    CausalHistory A O → CausalHistory A O → ℝ
  | _, [] => 1
  | h, ao :: rest =>
      π h ao.1 * Q h ao.1 ao.2 * causalTraceProbFrom π Q (h ++ [ao]) rest

/-- Probability of a finite controlled history under a policy and causal response law. -/
noncomputable def causalTraceProb (π : CausalPolicy A O) (Q : CausalResponse A O)
    (h : CausalHistory A O) : ℝ :=
  causalTraceProbFrom π Q [] h

/-- Appending a continuation factors the causal trace likelihood at the
prefix boundary. Shared by single-run block extraction and wait/proxy traces. -/
theorem causalTraceProbFrom_append
    {Act Obs : Type*} [Fintype Act] [Fintype Obs]
    (π : CausalPolicy Act Obs) (Q : CausalResponse Act Obs)
    (pre left right : CausalHistory Act Obs) :
    causalTraceProbFrom π Q pre (left ++ right) =
      causalTraceProbFrom π Q pre left *
        causalTraceProbFrom π Q (pre ++ left) right := by
  induction left generalizing pre with
  | nil => simp [causalTraceProbFrom]
  | cons ao left ih =>
      simp only [List.cons_append, causalTraceProbFrom]
      rw [ih]
      simp only [List.append_assoc, List.singleton_append]
      ring

theorem causalTraceProb_append
    {Act Obs : Type*} [Fintype Act] [Fintype Obs]
    (π : CausalPolicy Act Obs) (Q : CausalResponse Act Obs)
    (pre rest : CausalHistory Act Obs) :
    causalTraceProb π Q (pre ++ rest) =
      causalTraceProb π Q pre * causalTraceProbFrom π Q pre rest := by
  simpa [causalTraceProb] using
    causalTraceProbFrom_append π Q [] pre rest

theorem causalTraceProbFrom_append_singleton (π : CausalPolicy A O)
    (Q : CausalResponse A O) (pre l : CausalHistory A O) (ao : A × O) :
    causalTraceProbFrom π Q pre (l ++ [ao]) =
      causalTraceProbFrom π Q pre l *
        π (pre ++ l) ao.1 * Q (pre ++ l) ao.1 ao.2 := by
  induction l generalizing pre with
  | nil => simp [causalTraceProbFrom]
  | cons x xs ih =>
      simp only [List.cons_append, causalTraceProbFrom]
      rw [ih]
      simp only [List.append_assoc, List.singleton_append]
      ring

/-- Appending one action--observation pair multiplies by the policy and response probabilities at
the preceding history. -/
theorem causalTraceProb_append_singleton (π : CausalPolicy A O)
    (Q : CausalResponse A O) (h : CausalHistory A O) (ao : A × O) :
    causalTraceProb π Q (h ++ [ao]) =
      causalTraceProb π Q h * π h ao.1 * Q h ao.1 ao.2 := by
  simpa [causalTraceProb] using causalTraceProbFrom_append_singleton π Q [] h ao

theorem causalTraceProbFrom_nonneg (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Q : CausalResponse A O) (hQ : IsCausalResponse Q)
    (pre rest : CausalHistory A O) :
    0 ≤ causalTraceProbFrom π Q pre rest := by
  induction rest generalizing pre with
  | nil => simp [causalTraceProbFrom]
  | cons ao rest ih =>
      exact mul_nonneg
        (mul_nonneg ((hπ pre).1 ao.1) ((hQ pre ao.1).1 ao.2))
        (ih (pre ++ [ao]))

theorem causalTraceProb_nonneg (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Q : CausalResponse A O) (hQ : IsCausalResponse Q) (h : CausalHistory A O) :
    0 ≤ causalTraceProb π Q h :=
  causalTraceProbFrom_nonneg π hπ Q hQ [] h

/-- Controlled trace likelihood with the action word intervened on: only response probabilities
remain. -/
noncomputable def causalResponseProbFrom (Q : CausalResponse A O) :
    CausalHistory A O → CausalHistory A O → ℝ
  | _, [] => 1
  | h, ao :: rest => Q h ao.1 ao.2 * causalResponseProbFrom Q (h ++ [ao]) rest

noncomputable def causalResponseProb (Q : CausalResponse A O) (h : CausalHistory A O) : ℝ :=
  causalResponseProbFrom Q [] h

theorem causalResponseProbFrom_nonneg (Q : CausalResponse A O) (hQ : IsCausalResponse Q)
    (pre rest : CausalHistory A O) : 0 ≤ causalResponseProbFrom Q pre rest := by
  induction rest generalizing pre with
  | nil => exact zero_le_one
  | cons ao rest ih =>
      exact mul_nonneg ((hQ pre ao.1).1 ao.2) (ih (pre ++ [ao]))

theorem causalResponseProbFrom_append_singleton (Q : CausalResponse A O)
    (pre l : CausalHistory A O) (ao : A × O) :
    causalResponseProbFrom Q pre (l ++ [ao]) =
      causalResponseProbFrom Q pre l * Q (pre ++ l) ao.1 ao.2 := by
  induction l generalizing pre with
  | nil => simp [causalResponseProbFrom]
  | cons x xs ih =>
      simp only [List.cons_append, causalResponseProbFrom]
      rw [ih]
      simp only [List.append_assoc, List.singleton_append]
      ring

theorem causalResponseProb_append_singleton (Q : CausalResponse A O)
    (h : CausalHistory A O) (ao : A × O) :
    causalResponseProb Q (h ++ [ao]) = causalResponseProb Q h * Q h ao.1 ao.2 := by
  simpa [causalResponseProb] using causalResponseProbFrom_append_singleton Q [] h ao

/-- Behavioral equivalence in the current ontology: equality of every controlled finite-history
likelihood.  This quotients null-history coordinates exactly as the paper requires. -/
def CausalBehEq (Q Q' : CausalResponse A O) : Prop :=
  ∀ h, causalResponseProb Q h = causalResponseProb Q' h

@[refl]
theorem causalBehEq_refl (Q : CausalResponse A O) : CausalBehEq Q Q :=
  fun _ => rfl

@[symm]
theorem causalBehEq_symm {Q Q' : CausalResponse A O}
    (h : CausalBehEq Q Q') : CausalBehEq Q' Q :=
  fun w => (h w).symm

@[trans]
theorem causalBehEq_trans {Q Q' Q'' : CausalResponse A O}
    (h₁ : CausalBehEq Q Q') (h₂ : CausalBehEq Q' Q'') : CausalBehEq Q Q'' :=
  fun w => (h₁ w).trans (h₂ w)

/-- Controlled-trace equivalence is a genuine quotient relation on raw causal
response laws. Validity can be imposed separately by restricting to the
subtype satisfying `IsCausalResponse`. -/
instance causalBehEqSetoid : Setoid (CausalResponse A O) where
  r := CausalBehEq
  iseqv := ⟨causalBehEq_refl, causalBehEq_symm, causalBehEq_trans⟩

/-- A valid response kernel, before identifying behaviorally equivalent
representations. The validity proof excludes non-stochastic raw functions. -/
abbrev ValidCausalWorld (A O : Type*) [Fintype O] :=
  {Q : CausalResponse A O // IsCausalResponse Q}

/-- Behavioral equivalence restricted to valid worlds. -/
def validCausalBehEqSetoid (A O : Type*) [Fintype A] [Fintype O] :
    Setoid (ValidCausalWorld A O) :=
  Setoid.comap Subtype.val causalBehEqSetoid

/-- The paper's full behavioral quotient. No topology is asserted here. -/
abbrev CausalWorld (A O : Type*) [Fintype A] [Fintype O] :=
  Quotient (validCausalBehEqSetoid A O)

/-- A chosen valid representative is an interface for evaluating experiments
on the quotient; controlled-trace invariance makes the choice immaterial. -/
noncomputable def causalWorldRepresentative (q : CausalWorld A O) :
    CausalResponse A O :=
  (Quotient.out q).val

theorem causalWorldRepresentative_valid (q : CausalWorld A O) :
    IsCausalResponse (causalWorldRepresentative q) :=
  (Quotient.out q).property

/-- The quotient representatives contain every valid response behavior.
This is the exact completeness interface used by unrestricted-class results. -/
theorem causalWorldRepresentative_complete
    (Q : CausalResponse A O) (hQ : IsCausalResponse Q) :
    ∃ q : CausalWorld A O, CausalBehEq (causalWorldRepresentative q) Q := by
  let q : CausalWorld A O := Quotient.mk _ ⟨Q, hQ⟩
  refine ⟨q, ?_⟩
  exact Quotient.exact (Quotient.out_eq q)

noncomputable instance causalWorld_nonempty [Nonempty O] :
    Nonempty (CausalWorld A O) := by
  classical
  let o0 : O := Classical.choice inferInstance
  let Q : CausalResponse A O := fun _ _ o => if o = o0 then 1 else 0
  have hQ : IsCausalResponse Q := by
    intro h a
    constructor
    · intro o
      by_cases ho : o = o0 <;> simp [Q, ho]
    · simp [Q]
  exact ⟨Quotient.mk _ ⟨Q, hQ⟩⟩

/-! ## Deterministic causal responses and policies -/

/-- The deterministic response kernel with next-observation map `g`. -/
noncomputable def detResponse (g : CausalHistory A O → A → O) : CausalResponse A O := by
  classical
  exact fun h a o => if o = g h a then 1 else 0

/-- The deterministic policy with action map `p`. -/
noncomputable def detPolicy (p : CausalHistory A O → A) : CausalPolicy A O := by
  classical
  exact fun h a => if a = p h then 1 else 0

theorem detResponse_self (g : CausalHistory A O → A → O) (h : CausalHistory A O) (a : A) :
    detResponse g h a (g h a) = 1 := by
  simp [detResponse]

theorem detResponse_of_ne (g : CausalHistory A O → A → O) (h : CausalHistory A O) (a : A)
    {o : O} (ho : o ≠ g h a) : detResponse g h a o = 0 := by
  simp [detResponse, ho]

theorem detPolicy_self (p : CausalHistory A O → A) (h : CausalHistory A O) :
    detPolicy p h (p h) = 1 := by
  simp [detPolicy]

theorem detPolicy_of_ne (p : CausalHistory A O → A) (h : CausalHistory A O)
    {a : A} (ha : a ≠ p h) : detPolicy p h a = 0 := by
  simp [detPolicy, ha]

theorem isCausalResponse_detResponse (g : CausalHistory A O → A → O) :
    IsCausalResponse (detResponse g) := by
  classical
  intro h a
  constructor
  · intro o
    by_cases ho : o = g h a
    · rw [ho, detResponse_self]; norm_num
    · rw [detResponse_of_ne g h a ho]
  · simp [detResponse]

theorem isCausalPolicy_detPolicy (p : CausalHistory A O → A) :
    IsCausalPolicy (detPolicy p) := by
  classical
  intro h
  constructor
  · intro a
    by_cases ha : a = p h
    · rw [ha, detPolicy_self]; norm_num
    · rw [detPolicy_of_ne p h ha]
  · simp [detPolicy]

end IdExp
