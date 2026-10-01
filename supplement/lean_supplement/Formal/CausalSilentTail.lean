import Formal.CausalExperiment

/-!
# World-independent silent continuations

The causal response emits one fixed symbol forever. Given a recorded root
action-observation pair, the tail decoder samples the policy's later actions
and inserts those silent observations. Its historical public name
`unrestrictedSymbolTailRule` is preserved for compatibility; the construction
does not assume anything about the root experiment or world class.
-/

namespace IdExp

open Finset Set

set_option linter.unusedSectionVars false

variable {A O : Type*} [Fintype A] [Fintype O]
  [DecidableEq A] [DecidableEq O] [Nonempty A] [Nonempty O]
  (o0 : O)

/-- The silent causal response used after a recorded root signal. -/
noncomputable def silentSymbolResponse : CausalResponse A O :=
  fun _ _ o => if o = o0 then 1 else 0

theorem silentSymbolResponse_valid :
    IsCausalResponse ((silentSymbolResponse (A := A) o0)) := by
  intro h a
  constructor
  · intro o
    by_cases ho : o = o0 <;> simp [silentSymbolResponse, ho]
  · simp [silentSymbolResponse]

/-- Given a recorded root pair, sample the remaining policy actions while
inserting deterministic silent observations. -/
noncomputable def unrestrictedSymbolTailRule
    (π : CausalPolicy A O) (n : ℕ) :
    (A × O) → CausalFiniteTrace A O (n + 1) → ℝ :=
  fun ao w =>
    if w 0 = ao then
      causalTraceProbFrom π (silentSymbolResponse o0) [ao]
        (List.ofFn (Fin.tail w))
    else 0

theorem unrestrictedSymbolTailRule_mem_stochasticRules
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π) (n : ℕ) :
    unrestrictedSymbolTailRule o0 π n ∈
      stochasticRules (A × O) (CausalFiniteTrace A O (n + 1)) := by
  classical
  intro ao _
  constructor
  · intro w
    by_cases hw : w 0 = ao
    · simp only [unrestrictedSymbolTailRule, hw, if_true]
      exact causalTraceProbFrom_nonneg π hπ (silentSymbolResponse o0)
        (silentSymbolResponse_valid o0) [ao] (List.ofFn (Fin.tail w))
    · simp [unrestrictedSymbolTailRule, hw]
  · rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => A × O)).sum_comp]
    rw [Fintype.sum_prod_type]
    simp only [unrestrictedSymbolTailRule, List.ofFn]
    calc
      ∑ first : A × O, ∑ rest : CausalFiniteTrace A O n,
          (if first = ao then
            causalTraceProbFrom π (silentSymbolResponse o0) [ao]
              (List.ofFn rest)
          else 0) =
          ∑ rest : CausalFiniteTrace A O n,
            causalTraceProbFrom π (silentSymbolResponse o0) [ao]
              (List.ofFn rest) := by
        simp
      _ = 1 :=
        sum_causalTraceProbFrom π hπ (silentSymbolResponse o0)
          (silentSymbolResponse_valid o0) [ao] n

end IdExp
