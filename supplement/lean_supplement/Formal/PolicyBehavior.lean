import Formal.CausalResidual
import Formal.CausalExperiment
import Formal.ContinuationInstrument

/-!
# Policy behaviors: the policy-side controlled carrier

**Relevance:** the policy-side causal state of the coupled pair-process note
(`Paper/research/coupled_causal_trajectories_2026-09-19/note.tex`, §1) and of
`TheoryDocs/COUPLED_CAUSAL_STATES.md`.

A *policy behavior* assigns to every finite action–observation history `h`
the action-propensity mass `c h`, subject to

* `c [] = 1` and `c ≥ 0`;
* observation independence `c (h ++ [(a, o)]) = c (h ++ [(a, o')])`: the
  action at each step is chosen before that step's observation, so the mass
  of a one-step extension cannot depend on the observation that follows;
* consistency `∑ a, c (h ++ [(a, o)]) = c h` for every `h` and every
  supplied observation `o`.

This is the exact mirror image of `CausalBehavior`: there the action is
intervened on and the observation is summed; here the observation is a
supplied input and the action is summed.  Neither carrier is one joint law
over action–observation histories.  Under a valid history policy `π`, the
policy propensity `causalPolicyProb π` is a policy behavior (`ofPolicy`), and
every policy behavior arises this way (`ofPolicy_toPolicy`): policy
behaviors are exactly history policies modulo their rows below their own
null histories.  Residuals `c / h`, the fixed-observation normalization
`sum_fixed_obs`, and the policy-side predictive-state relation complete the
mirror of `CausalResidual.lean`.

**Not claimed.**  Nothing here couples the policy to an environment; the
labelled pair process is `CoupledPairProcess.lean`.  No exploration,
sufficiency, or decoding statement is made.
-/

namespace IdExp

open Finset

set_option linter.unusedSectionVars false

variable {A O : Type*} [Fintype A] [Fintype O]

/-- A controlled action-propensity family.  The observation coordinate is a
supplied input, so the branching law normalizes separately for every
supplied observation, and the mass of a one-step extension is independent of
the observation it ends with (action-first timing). -/
structure PolicyBehavior (A O : Type*) [Fintype A] where
  /-- Propensity mass of the action part of a controlled history. -/
  mass : CausalHistory A O → ℝ
  /-- The empty history has unit mass. -/
  root : mass [] = 1
  /-- Masses are nonnegative. -/
  nonneg : ∀ h, 0 ≤ mass h
  /-- The action is chosen before the observation: a one-step extension's
  mass does not depend on its observation coordinate. -/
  obs_indep : ∀ (h : CausalHistory A O) (a : A) (o o' : O),
    mass (h ++ [(a, o)]) = mass (h ++ [(a, o')])
  /-- For each supplied observation, the possible next actions partition the
  parent event. -/
  consistent : ∀ (h : CausalHistory A O) (o : O),
    ∑ a, mass (h ++ [(a, o)]) = mass h

namespace PolicyBehavior

@[ext]
theorem ext {c d : PolicyBehavior A O} (h : c.mass = d.mass) : c = d := by
  cases c
  cases d
  cases h
  rfl

@[simp]
theorem mass_nil (c : PolicyBehavior A O) : c.mass [] = 1 :=
  c.root

/-- A one-step extension has no more mass than its parent. -/
theorem child_le (c : PolicyBehavior A O) (h : CausalHistory A O) (a : A) (o : O) :
    c.mass (h ++ [(a, o)]) ≤ c.mass h := by
  rw [← c.consistent h o]
  exact Finset.single_le_sum
    (fun b _ => c.nonneg (h ++ [(b, o)])) (Finset.mem_univ a)

/-- Every policy-behavior mass is at most one. -/
theorem mass_le_one (c : PolicyBehavior A O) (h : CausalHistory A O) :
    c.mass h ≤ 1 := by
  induction h using List.reverseRecOn with
  | nil => rw [c.root]
  | append_singleton h ao ih => exact (c.child_le h ao.1 ao.2).trans ih

/-- Every child of a null history is null. -/
theorem child_eq_zero_of_eq_zero (c : PolicyBehavior A O)
    (h : CausalHistory A O) (a : A) (o : O) (hh : c.mass h = 0) :
    c.mass (h ++ [(a, o)]) = 0 := by
  apply le_antisymm
  · simpa [hh] using c.child_le h a o
  · exact c.nonneg _

/-- Every descendant of a null history is null. -/
theorem mass_append_eq_zero_of_eq_zero (c : PolicyBehavior A O)
    (pre rest : CausalHistory A O) (hpre : c.mass pre = 0) :
    c.mass (pre ++ rest) = 0 := by
  induction rest using List.reverseRecOn with
  | nil => simpa using hpre
  | append_singleton rest ao ih =>
      simpa only [List.append_assoc] using
        c.child_eq_zero_of_eq_zero (pre ++ rest) ao.1 ao.2 ih

/-- Appending any continuation cannot increase mass. -/
theorem mass_append_le (c : PolicyBehavior A O) (pre rest : CausalHistory A O) :
    c.mass (pre ++ rest) ≤ c.mass pre := by
  induction rest using List.reverseRecOn with
  | nil => simp
  | append_singleton rest ao ih =>
      calc c.mass (pre ++ (rest ++ [ao]))
          = c.mass ((pre ++ rest) ++ [ao]) := by rw [List.append_assoc]
        _ ≤ c.mass (pre ++ rest) := c.child_le _ ao.1 ao.2
        _ ≤ c.mass pre := ih

/-- Positive mass of a descendant forces positive mass of its prefix. -/
theorem mass_pos_of_append_pos (c : PolicyBehavior A O)
    (pre rest : CausalHistory A O) (happend : 0 < c.mass (pre ++ rest)) :
    0 < c.mass pre :=
  happend.trans_le (c.mass_append_le pre rest)

/-! ## Policies as policy behaviors -/

/-- The policy behavior of a valid history policy: its propensity
`causalPolicyProb π`. -/
noncomputable def ofPolicy (π : CausalPolicy A O) (hπ : IsCausalPolicy π) :
    PolicyBehavior A O where
  mass := causalPolicyProb π
  root := by simp [causalPolicyProb, causalPolicyProbFrom]
  nonneg := causalPolicyProb_nonneg_of_valid π hπ
  obs_indep := by
    intro h a o o'
    rw [causalPolicyProb_append_singleton, causalPolicyProb_append_singleton]
  consistent := by
    intro h o
    simp_rw [causalPolicyProb_append_singleton]
    rw [← Finset.mul_sum, (hπ h).2, mul_one]

@[simp]
theorem ofPolicy_mass (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (h : CausalHistory A O) :
    (ofPolicy π hπ).mass h = causalPolicyProb π h :=
  rfl

/-- A history policy recovered from a policy behavior.  At a positive-mass
history the row is the child/parent ratio, read at an arbitrary observation
(well defined by `obs_indep`).  At a null history no row is determined, so an
arbitrary Dirac row is inserted; that choice is behaviorally invisible. -/
noncomputable def toPolicy [Nonempty A] [Nonempty O] (c : PolicyBehavior A O) :
    CausalPolicy A O := by
  classical
  exact fun h a =>
    if c.mass h = 0 then
      if a = Classical.arbitrary A then 1 else 0
    else
      c.mass (h ++ [(a, Classical.arbitrary O)]) / c.mass h

/-- The recovered policy has stochastic rows everywhere. -/
theorem toPolicy_valid [Nonempty A] [Nonempty O] (c : PolicyBehavior A O) :
    IsCausalPolicy c.toPolicy := by
  classical
  intro h
  constructor
  · intro a
    by_cases hc : c.mass h = 0
    · simp only [toPolicy, if_pos hc]
      split <;> norm_num
    · simp only [toPolicy, if_neg hc]
      exact div_nonneg (c.nonneg _) (c.nonneg h)
  · by_cases hc : c.mass h = 0
    · simp [toPolicy, hc]
    · simp only [toPolicy, if_neg hc]
      rw [← Finset.sum_div, c.consistent h _, div_self hc]

/-- At a positive-mass history the recovered policy row is the child/parent
ratio at any observation. -/
theorem toPolicy_of_pos [Nonempty A] [Nonempty O] (c : PolicyBehavior A O)
    {h : CausalHistory A O} (hc : 0 < c.mass h) (a : A) (o : O) :
    c.toPolicy h a = c.mass (h ++ [(a, o)]) / c.mass h := by
  classical
  simp only [toPolicy, if_neg hc.ne']
  rw [c.obs_indep h a (Classical.arbitrary O) o]

/-- **Identification.**  Passing from a policy behavior to any recovered
history policy and back recovers every mass exactly.  Hence policy behaviors
are exactly history policies modulo their rows below their own null
histories. -/
@[simp]
theorem ofPolicy_toPolicy [Nonempty A] [Nonempty O] (c : PolicyBehavior A O) :
    ofPolicy c.toPolicy c.toPolicy_valid = c := by
  classical
  apply PolicyBehavior.ext
  funext h
  induction h using List.reverseRecOn with
  | nil => simp [causalPolicyProb, causalPolicyProbFrom]
  | append_singleton h ao ih =>
      obtain ⟨a, o⟩ := ao
      rw [ofPolicy_mass, causalPolicyProb_append_singleton, ← ofPolicy_mass _ c.toPolicy_valid, ih]
      by_cases hc : c.mass h = 0
      · rw [hc, zero_mul]
        exact (c.child_eq_zero_of_eq_zero h a o hc).symm
      · rw [c.toPolicy_of_pos (lt_of_le_of_ne (c.nonneg h) (Ne.symm hc)) a o]
        field_simp

/-- At a positive-propensity history, recovering a policy from its own
policy behavior reproduces its row. -/
theorem toPolicy_ofPolicy_of_pos [Nonempty A] [Nonempty O]
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    {h : CausalHistory A O} (hpos : 0 < causalPolicyProb π h) (a : A) :
    (ofPolicy π hπ).toPolicy h a = π h a := by
  rw [(ofPolicy π hπ).toPolicy_of_pos hpos a (Classical.arbitrary O),
    ofPolicy_mass, ofPolicy_mass, causalPolicyProb_append_singleton]
  exact mul_div_cancel_left₀ _ hpos.ne'

/-! ## Residual policy behaviors -/

/-- The residual policy behavior `c / h` at a positive-mass history:
`(c / h) u = c (h ++ u) / c h`. -/
noncomputable def residual (c : PolicyBehavior A O) (h : CausalHistory A O)
    (hc : 0 < c.mass h) : PolicyBehavior A O where
  mass := fun u => c.mass (h ++ u) / c.mass h
  root := by simp [div_self hc.ne']
  nonneg := fun u => div_nonneg (c.nonneg _) hc.le
  obs_indep := by
    intro u a o o'
    simp only [← List.append_assoc]
    rw [c.obs_indep (h ++ u) a o o']
  consistent := by
    intro u o
    rw [← Finset.sum_div]
    simp only [← List.append_assoc]
    rw [c.consistent (h ++ u) o]

@[simp]
theorem residual_mass (c : PolicyBehavior A O) (h : CausalHistory A O)
    (hc : 0 < c.mass h) (u : CausalHistory A O) :
    (c.residual h hc).mass u = c.mass (h ++ u) / c.mass h :=
  rfl

/-- The one-step marginal of a residual is the policy row at `h`. -/
theorem residual_mass_singleton (c : PolicyBehavior A O)
    (h : CausalHistory A O) (hc : 0 < c.mass h) (a : A) (o : O) :
    (c.residual h hc).mass [(a, o)] = c.mass (h ++ [(a, o)]) / c.mass h :=
  rfl

/-- Exact multiplicative factorization of a propensity mass into its prefix
mass and residual mass. -/
theorem mass_append_eq_mul_residual (c : PolicyBehavior A O)
    (h : CausalHistory A O) (hc : 0 < c.mass h) (u : CausalHistory A O) :
    c.mass (h ++ u) = c.mass h * (c.residual h hc).mass u := by
  rw [residual_mass]
  field_simp

/-- The residual at the empty history is the policy behavior itself. -/
@[simp]
theorem residual_nil (c : PolicyBehavior A O) (h1 : 0 < c.mass []) :
    c.residual [] h1 = c := by
  apply PolicyBehavior.ext
  funext u
  simp

/-- A residual mass is positive exactly when the concatenated mass is
positive. -/
theorem residual_mass_pos_iff (c : PolicyBehavior A O)
    (h : CausalHistory A O) (hc : 0 < c.mass h) (u : CausalHistory A O) :
    0 < (c.residual h hc).mass u ↔ 0 < c.mass (h ++ u) := by
  rw [residual_mass]
  constructor
  · intro hd
    rcases (c.nonneg (h ++ u)).lt_or_eq with hlt | heq
    · exact hlt
    · rw [← heq, zero_div] at hd
      exact absurd hd (lt_irrefl 0)
  · intro hpos
    exact div_pos hpos hc

/-- Residuals compose: `(c / h) / u = c / (h ++ u)` whenever the
concatenation has positive mass. -/
theorem residual_residual (c : PolicyBehavior A O)
    (h u : CausalHistory A O) (hc : 0 < c.mass h)
    (hu : 0 < c.mass (h ++ u)) :
    (c.residual h hc).residual u ((c.residual_mass_pos_iff h hc u).2 hu) =
      c.residual (h ++ u) hu := by
  apply PolicyBehavior.ext
  funext v
  simp only [residual_mass, List.append_assoc]
  exact div_div_div_cancel_right₀ hc.ne' _ _

/-- The residual of a policy's behavior at a positive-propensity history is
the behavior of the policy shifted to that history. -/
theorem ofPolicy_residual_mass (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    {h : CausalHistory A O} (hpos : 0 < causalPolicyProb π h)
    (u : CausalHistory A O) :
    ((ofPolicy π hπ).residual h hpos).mass u =
      causalPolicyProb π (h ++ u) / causalPolicyProb π h :=
  rfl

/-! ## Normalization along a supplied observation word -/

/-- **Policy normalization along any supplied observation word.**  Fixing
the observations `obs` and summing the propensity over all action words of
the same length gives one.  This is the policy-side analogue of a behavior
summing to one over observation words for a fixed action word. -/
theorem sum_fixed_obs (c : PolicyBehavior A O) (n : ℕ) (obs : Fin n → O) :
    ∑ acts : Fin n → A, c.mass (List.ofFn fun i => (acts i, obs i)) = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => A)).sum_comp,
        Fintype.sum_prod_type]
      have hsnoc (a : A) (rest : Fin n → A) :
          (Fin.snocEquiv (fun _ : Fin (n + 1) => A)) (a, rest) =
            Fin.snoc rest a := by
        funext i
        exact Fin.snocEquiv_apply _ _ i
      calc
        ∑ a : A, ∑ rest : Fin n → A,
            c.mass (List.ofFn fun i =>
              ((Fin.snocEquiv (fun _ : Fin (n + 1) => A)) (a, rest) i, obs i))
            = ∑ a : A, ∑ rest : Fin n → A,
                c.mass ((List.ofFn fun i : Fin n => (rest i, obs i.castSucc)) ++
                  [(a, obs (Fin.last n))]) := by
              apply Finset.sum_congr rfl
              intro a _
              apply Finset.sum_congr rfl
              intro rest _
              rw [hsnoc a rest, List.ofFn_succ_last]
              simp
        _ = ∑ rest : Fin n → A, ∑ a : A,
                c.mass ((List.ofFn fun i : Fin n => (rest i, obs i.castSucc)) ++
                  [(a, obs (Fin.last n))]) := Finset.sum_comm
        _ = ∑ rest : Fin n → A,
                c.mass (List.ofFn fun i : Fin n => (rest i, obs i.castSucc)) := by
              apply Finset.sum_congr rfl
              intro rest _
              exact c.consistent _ _
        _ = 1 := ih (fun i => obs i.castSucc)

/-! ## Policy-side predictive-state equivalence -/

/-- Two histories have the same policy predictive state when their
propensity continuations are proportional:
`c (h ++ u) * c h' = c (h' ++ u) * c h` for every future word `u`.  Stated
without division; at positive-mass histories it is equality of residuals. -/
def PredictiveEq (c : PolicyBehavior A O) (h h' : CausalHistory A O) : Prop :=
  ∀ u, c.mass (h ++ u) * c.mass h' = c.mass (h' ++ u) * c.mass h

/-- At positive-mass histories, policy predictive equivalence is exactly
equality of the two residual policy behaviors. -/
theorem predictiveEq_iff_residual_eq (c : PolicyBehavior A O)
    {h h' : CausalHistory A O} (hc : 0 < c.mass h) (hc' : 0 < c.mass h') :
    c.PredictiveEq h h' ↔ c.residual h hc = c.residual h' hc' := by
  constructor
  · intro hEq
    apply PolicyBehavior.ext
    funext u
    simp only [residual_mass]
    rw [div_eq_div_iff hc.ne' hc'.ne']
    exact hEq u
  · intro hEq u
    have hu := congrFun (congrArg PolicyBehavior.mass hEq) u
    simp only [residual_mass] at hu
    rwa [div_eq_div_iff hc.ne' hc'.ne'] at hu

/-- Policy predictive equivalence is reflexive. -/
theorem predictiveEq_refl (c : PolicyBehavior A O) (h : CausalHistory A O) :
    c.PredictiveEq h h :=
  fun _ => rfl

/-- Policy predictive equivalence is symmetric. -/
theorem predictiveEq_symm (c : PolicyBehavior A O)
    {h h' : CausalHistory A O} (H : c.PredictiveEq h h') :
    c.PredictiveEq h' h :=
  fun u => (H u).symm

/-- Policy predictive equivalence is transitive through a positive-mass
middle history. -/
theorem predictiveEq_trans (c : PolicyBehavior A O)
    {h h' h'' : CausalHistory A O} (hc' : 0 < c.mass h')
    (H₁ : c.PredictiveEq h h') (H₂ : c.PredictiveEq h' h'') :
    c.PredictiveEq h h'' := by
  intro u
  apply mul_right_cancel₀ hc'.ne'
  calc
    c.mass (h ++ u) * c.mass h'' * c.mass h'
        = (c.mass (h ++ u) * c.mass h') * c.mass h'' := by ring
    _ = (c.mass (h' ++ u) * c.mass h) * c.mass h'' := by rw [H₁ u]
    _ = (c.mass (h' ++ u) * c.mass h'') * c.mass h := by ring
    _ = (c.mass (h'' ++ u) * c.mass h') * c.mass h := by rw [H₂ u]
    _ = c.mass (h'' ++ u) * c.mass h * c.mass h' := by ring

/-- Policy predictive equivalence is an equivalence relation on the
positive-mass histories of a policy behavior. -/
def predictiveSetoid (c : PolicyBehavior A O) :
    Setoid {h : CausalHistory A O // 0 < c.mass h} where
  r h h' := c.PredictiveEq h.1 h'.1
  iseqv :=
    ⟨fun h => c.predictiveEq_refl h.1,
     fun H => c.predictiveEq_symm H,
     fun {_ h' _} H₁ H₂ => c.predictiveEq_trans h'.2 H₁ H₂⟩

end PolicyBehavior

end IdExp
