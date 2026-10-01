import Formal.CausalKernel
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Finite contingency-plan decomposition (Kuhn weights)

**Relevance:** direct current-paper support for the combinatorial core of
`thm:finite-universality` in `Paper/draft/main.tex`.

At a fixed horizon there are finitely many decision histories.  Independently sample one action
from the behavioral policy at every such history.  The resulting random function is a deterministic
contingency plan.  This file proves that its product weights form a probability distribution and
that every finite collection of prescribed decisions has exactly the behavioral-policy product
probability.  Applied to the distinct prefixes of one realized trace, this is the Kuhn mixture
identity used in the paper. `MixtureDecoder.lean` proves the complementary decoder-convexity
step, and `CausalUniversality.lean` assembles both into the arbitrary-kernel finite-horizon theorem.
-/

set_option linter.unusedSectionVars false

namespace IdExp

open Finset

variable {H A O : Type*} [Fintype H] [Fintype A] [Fintype O]
  [DecidableEq H] [DecidableEq A] [DecidableEq O]

/-- Product probability of a deterministic plan `τ` when each decision row is sampled
independently from `p`. -/
noncomputable def contingencyWeight (p : H → A → ℝ) (τ : H → A) : ℝ :=
  ∏ h, p h (τ h)

theorem contingencyWeight_nonneg (p : H → A → ℝ) (hp : ∀ h a, 0 ≤ p h a)
    (τ : H → A) : 0 ≤ contingencyWeight p τ :=
  Finset.prod_nonneg fun h _ => hp h (τ h)

/-- Product weights over all deterministic contingency plans sum to one. -/
theorem sum_contingencyWeight (p : H → A → ℝ) (hp : ∀ h, ∑ a, p h a = 1) :
    ∑ τ : H → A, contingencyWeight p τ = 1 := by
  simp only [contingencyWeight]
  rw [← Fintype.prod_sum]
  simp [hp]

/-- Exact finite-dimensional marginal of the contingency-plan distribution.  Requiring a plan to
take prescribed actions on `S` has probability equal to the product of those behavioral action
probabilities; all off-path decisions integrate out to one. -/
theorem sum_contingencyWeight_event (p : H → A → ℝ) (hp : ∀ h, ∑ a, p h a = 1)
    (S : Finset H) (target : H → A) :
    (∑ τ : H → A,
        if ∀ h ∈ S, τ h = target h then contingencyWeight p τ else 0) =
      ∏ h ∈ S, p h (target h) := by
  classical
  let q : H → A → ℝ := fun h a =>
    if h ∈ S then if a = target h then p h a else 0 else p h a
  calc
    (∑ τ : H → A,
        if ∀ h ∈ S, τ h = target h then contingencyWeight p τ else 0) =
        ∑ τ : H → A, ∏ h, q h (τ h) := by
      apply Finset.sum_congr rfl
      intro τ _
      by_cases he : ∀ h ∈ S, τ h = target h
      · rw [if_pos he]
        simp only [contingencyWeight, q]
        apply Finset.prod_congr rfl
        intro h _
        by_cases hs : h ∈ S
        · simp [hs, he h hs]
        · simp [hs]
      · rw [if_neg he]
        push Not at he
        obtain ⟨h, hs, hne⟩ := he
        apply (Finset.prod_eq_zero (Finset.mem_univ h) ?_).symm
        simp [q, hs, hne]
    _ = ∏ h, ∑ a, q h a := (Fintype.prod_sum q).symm
    _ = ∏ h ∈ S, p h (target h) := by
      simp only [q]
      calc
        (∏ h, ∑ a, if h ∈ S then (if a = target h then p h a else 0) else p h a) =
            ∏ h ∈ S, ∑ a,
              if h ∈ S then (if a = target h then p h a else 0) else p h a := by
          symm
          apply Finset.prod_subset (Finset.subset_univ S)
          intro h _ hnot
          simp [hnot, hp]
        _ = ∏ h ∈ S, p h (target h) := by
          apply Finset.prod_congr rfl
          intro h hs
          simp [hs]

/-! ## Current causal-history instantiation -/

/-- All decision histories of lengths strictly below `n`. -/
abbrev CausalDecisionPoint (A O : Type*) (n : ℕ) :=
  Σ k : Fin n, Fin k.1 → A × O

/-- Convert a bounded vector history to the paper's chronological list convention. -/
def causalDecisionHistory {n : ℕ} (x : CausalDecisionPoint A O n) : CausalHistory A O :=
  List.ofFn x.2

/-- A deterministic depth-`n` contingency plan. -/
abbrev CausalPlan (A O : Type*) (n : ℕ) := CausalDecisionPoint A O n → A

/-- Kuhn's world-independent product weight on deterministic depth-`n` plans. -/
noncomputable def kuhnWeight (π : CausalPolicy A O) (n : ℕ) (τ : CausalPlan A O n) : ℝ :=
  contingencyWeight (fun x => π (causalDecisionHistory x)) τ

theorem kuhnWeight_nonneg (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (n : ℕ) (τ : CausalPlan A O n) : 0 ≤ kuhnWeight π n τ :=
  contingencyWeight_nonneg _ (fun x a => (hπ (causalDecisionHistory x)).1 a) τ

/-- The Kuhn weights are a probability distribution over deterministic contingency plans. -/
theorem kuhnWeight_isDist (π : CausalPolicy A O) (hπ : IsCausalPolicy π) (n : ℕ) :
    IsDist (kuhnWeight π n) := by
  constructor
  · exact kuhnWeight_nonneg π hπ n
  · exact sum_contingencyWeight _ (fun x => (hπ (causalDecisionHistory x)).2)

/-- Exact marginal identity for any chosen finite collection of depth-`n` causal decision points.
In the paper, take `S` to be the prefixes visited by a fixed length-`n` history and `target` to be
the actions in that history. -/
theorem kuhnWeight_event (π : CausalPolicy A O) (hπ : IsCausalPolicy π) (n : ℕ)
    (S : Finset (CausalDecisionPoint A O n))
    (target : CausalDecisionPoint A O n → A) :
    (∑ τ : CausalPlan A O n,
        if ∀ x ∈ S, τ x = target x then kuhnWeight π n τ else 0) =
      ∏ x ∈ S, π (causalDecisionHistory x) (target x) :=
  sum_contingencyWeight_event _ (fun x => (hπ (causalDecisionHistory x)).2) S target

end IdExp
