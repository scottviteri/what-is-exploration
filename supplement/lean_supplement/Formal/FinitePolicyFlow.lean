import Formal.BoundedApproachCertificate
import Formal.CausalPolicyMixture
import Formal.CausalBehaviorExperiment

/-!
# Exact finite realization flows for behavioral collectors

Variables range over the finite full history tree: prefix weights through H
and action weights strictly before H. Observation children share the same
action weight. Every feasible flow reconstructs a valid behavioral policy,
with a fixed probability row at zero weights and after the horizon.
Pruning impossible observations and numerical solver encodings are separate.
-/

namespace IdExp
open Finset
noncomputable section
set_option linter.unusedSectionVars false
variable {A O Θ : Type*} [Fintype A] [Fintype O] [Nonempty A] [Nonempty O]

abbrev PolicyFlowNode (A O : Type*) (H : ℕ) := CausalDecisionPoint A O (H + 1)

def policyFlowNode (H : ℕ) (h : CausalHistory A O) (hh : h.length ≤ H) :
    PolicyFlowNode A O H :=
  causalDecisionPointOfHistory (H + 1) h (by omega)

def policyFlowParent {H : ℕ} (d : CausalDecisionPoint A O H) : PolicyFlowNode A O H :=
  policyFlowNode H (causalDecisionHistory d) (by simp [causalDecisionHistory])

def policyFlowChild {H : ℕ} (d : CausalDecisionPoint A O H) (a : A) (o : O) :
    PolicyFlowNode A O H :=
  policyFlowNode H (causalDecisionHistory d ++ [(a,o)]) (by
    simp [causalDecisionHistory])

@[simp] theorem causalDecisionHistory_policyFlowNode (H : ℕ)
    (h : CausalHistory A O) (hh : h.length ≤ H) :
    causalDecisionHistory (policyFlowNode H h hh) = h := by
  simp only [policyFlowNode, causalDecisionHistory, causalDecisionPointOfHistory, List.ofFn_get]

/-- Literal finite linear root, conservation, and observation-child constraints. -/
structure IsFinitePolicyFlow (H : ℕ) (w : PolicyFlowNode A O H → ℝ)
    (x : CausalDecisionPoint A O H → A → ℝ) : Prop where
  weight_nonneg : ∀ d, 0 ≤ w d
  action_nonneg : ∀ d a, 0 ≤ x d a
  root : w (policyFlowNode H [] (by simp)) = 1
  conservation : ∀ d, ∑ a, x d a = w (policyFlowParent d)
  child : ∀ d a o, w (policyFlowChild d a o) = x d a

/-- Normalize at positive weights; use a uniform row at zero weights. -/
def policyFlowRows (H : ℕ) (w : PolicyFlowNode A O H → ℝ)
    (x : CausalDecisionPoint A O H → A → ℝ) (d : CausalDecisionPoint A O H) (a : A) : ℝ :=
  if w (policyFlowParent d) = 0 then (Fintype.card A : ℝ)⁻¹
  else x d a / w (policyFlowParent d)

theorem policyFlowRows_valid (H : ℕ) (w : PolicyFlowNode A O H → ℝ)
    (x : CausalDecisionPoint A O H → A → ℝ) (hf : IsFinitePolicyFlow H w x)
    (d : CausalDecisionPoint A O H) : IsDist (policyFlowRows H w x d) := by
  classical
  by_cases hz : w (policyFlowParent d) = 0
  · have hc : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    constructor
    · intro a; simp only [policyFlowRows, if_pos hz]; positivity
    · simp [policyFlowRows, hz, hc]
  · constructor
    · intro a
      simp only [policyFlowRows, if_neg hz]
      exact div_nonneg (hf.action_nonneg d a) (hf.weight_nonneg _)
    · simp only [policyFlowRows, if_neg hz, ← Finset.sum_div,
        hf.conservation, div_self hz]

/-- Recover every action allocation, including at null nodes. -/
theorem policyFlowRows_mul (H : ℕ) (w : PolicyFlowNode A O H → ℝ)
    (x : CausalDecisionPoint A O H → A → ℝ) (hf : IsFinitePolicyFlow H w x)
    (d : CausalDecisionPoint A O H) (a : A) :
    w (policyFlowParent d) * policyFlowRows H w x d a = x d a := by
  classical
  by_cases hz : w (policyFlowParent d) = 0
  · have hle : x d a ≤ w (policyFlowParent d) := by
      rw [← hf.conservation]
      exact Finset.single_le_sum (fun b _ => hf.action_nonneg d b) (Finset.mem_univ a)
    have hx : x d a = 0 := le_antisymm (by simpa [hz] using hle) (hf.action_nonneg d a)
    simp [hz, hx]
  · simp only [policyFlowRows, if_neg hz]
    exact mul_div_cancel₀ _ hz

def policyOfFiniteFlow (H : ℕ) (w : PolicyFlowNode A O H → ℝ)
    (x : CausalDecisionPoint A O H → A → ℝ) (hf : IsFinitePolicyFlow H w x) :
    ValidCausalPolicy A O :=
  boundedCausalPolicy H (policyFlowRows H w x) (policyFlowRows_valid H w x hf)

theorem policyOfFiniteFlow_before (H : ℕ) (w : PolicyFlowNode A O H → ℝ)
    (x : CausalDecisionPoint A O H → A → ℝ) (hf : IsFinitePolicyFlow H w x)
    (h : CausalHistory A O) (hh : h.length < H) (a : A) :
    (policyOfFiniteFlow H w x hf).1 h a =
      policyFlowRows H w x (causalDecisionPointOfHistory H h hh) a := by
  simp [policyOfFiniteFlow, boundedCausalPolicy, hh]

/-- Every prefix weight is exactly the policy action likelihood. The statement
includes null histories and horizon zero. -/
theorem causalPolicyProb_policyOfFiniteFlow (H : ℕ) (w : PolicyFlowNode A O H → ℝ)
    (x : CausalDecisionPoint A O H → A → ℝ) (hf : IsFinitePolicyFlow H w x)
    (h : CausalHistory A O) (hh : h.length ≤ H) :
    causalPolicyProb (policyOfFiniteFlow H w x hf).1 h = w (policyFlowNode H h hh) := by
  induction h using List.reverseRecOn with
  | nil => simpa [causalPolicyProb, causalPolicyProbFrom] using hf.root.symm
  | append_singleton h ao ih =>
      have hlt : h.length < H := by simp only [List.length_append, List.length_singleton] at hh; omega
      have hle : h.length ≤ H := hlt.le
      let d := causalDecisionPointOfHistory H h hlt
      have hp : policyFlowParent d = policyFlowNode H h hle := by
        simp [d, policyFlowParent, causalDecisionHistory, causalDecisionPointOfHistory]
      have hc : policyFlowChild d ao.1 ao.2 = policyFlowNode H (h ++ [ao]) hh := by
        simp [d, policyFlowChild, causalDecisionHistory, causalDecisionPointOfHistory]
      rw [causalPolicyProb_append_singleton, ih hle, policyOfFiniteFlow_before H w x hf h hlt]
      change w (policyFlowNode H h hle) * policyFlowRows H w x d ao.1 = _
      rw [← hp, policyFlowRows_mul H w x hf]
      exact (hf.child d ao.1 ao.2).symm.trans (congrArg w hc)

def policyFlowWeights (H : ℕ) (π : ValidCausalPolicy A O) : PolicyFlowNode A O H → ℝ :=
  fun d => causalPolicyProb π.1 (causalDecisionHistory d)

def policyFlowActions (H : ℕ) (π : ValidCausalPolicy A O) :
    CausalDecisionPoint A O H → A → ℝ :=
  fun d a => causalPolicyProb π.1 (causalDecisionHistory d) * π.1 (causalDecisionHistory d) a

/-- Every unrestricted behavioral collector supplies a feasible finite flow. -/
theorem isFinitePolicyFlow_of_policy (H : ℕ) (π : ValidCausalPolicy A O) :
    IsFinitePolicyFlow H (policyFlowWeights H π) (policyFlowActions H π) := by
  constructor
  · intro d; exact causalPolicyProb_nonneg π.1 π.2 _
  · intro d a; exact mul_nonneg (causalPolicyProb_nonneg π.1 π.2 _) ((π.2 _).1 a)
  · simp [policyFlowWeights, policyFlowNode, causalDecisionPointOfHistory,
      causalDecisionHistory, causalPolicyProb, causalPolicyProbFrom]
  · intro d
    simp only [policyFlowActions, policyFlowWeights, policyFlowParent,
      causalDecisionHistory_policyFlowNode, ← Finset.mul_sum, (π.2 _).2, mul_one]
  · intro d a o
    simp only [policyFlowActions, policyFlowWeights, policyFlowChild,
      causalDecisionHistory_policyFlowNode, causalPolicyProb_append_singleton]

/-- Exact converse: finite linear flows are precisely behavioral-policy weights. -/
theorem isFinitePolicyFlow_iff_exists_policy (H : ℕ) (w : PolicyFlowNode A O H → ℝ)
    (x : CausalDecisionPoint A O H → A → ℝ) :
    IsFinitePolicyFlow H w x ↔ ∃ π : ValidCausalPolicy A O,
      policyFlowWeights H π = w ∧ policyFlowActions H π = x := by
  constructor
  · intro hf
    let π := policyOfFiniteFlow H w x hf
    have hw : policyFlowWeights H π = w := by
      funext d
      have hlen : (causalDecisionHistory d).length ≤ H := by
        simp [causalDecisionHistory]; omega
      have hi : policyFlowNode H (causalDecisionHistory d) hlen = d := by
        rcases d with ⟨k, v⟩
        simp only [policyFlowNode, causalDecisionPointOfHistory, causalDecisionHistory]
        apply Sigma.ext
        · exact Fin.ext List.length_ofFn
        · exact (Sigma.mk.inj (List.equivSigmaTuple.right_inv ⟨k.val, v⟩)).2
      simpa only [policyFlowWeights, π, hi] using
        causalPolicyProb_policyOfFiniteFlow H w x hf (causalDecisionHistory d) hlen
    refine ⟨π, hw, ?_⟩
    funext d a
    have hlt : (causalDecisionHistory d).length < H := by
      simpa [causalDecisionHistory] using d.1.isLt
    have hi : causalDecisionPointOfHistory H (causalDecisionHistory d) hlt = d := by
      rcases d with ⟨k, v⟩
      simp only [causalDecisionPointOfHistory, causalDecisionHistory]
      apply Sigma.ext
      · exact Fin.ext List.length_ofFn
      · exact (Sigma.mk.inj (List.equivSigmaTuple.right_inv ⟨k.val, v⟩)).2
    change causalPolicyProb π.1 (causalDecisionHistory d) * π.1 (causalDecisionHistory d) a = _
    rw [show causalPolicyProb π.1 (causalDecisionHistory d) = w (policyFlowParent d) from
      causalPolicyProb_policyOfFiniteFlow H w x hf _ _]
    rw [policyOfFiniteFlow_before H w x hf _ hlt, hi]
    exact policyFlowRows_mul H w x hf d a
  · rintro ⟨π, rfl, rfl⟩
    exact isFinitePolicyFlow_of_policy H π

/-- The terminal experiment is linear in the realization-weight variables. -/
def finiteFlowExperiment (ps : Θ → CausalBehavior A O) (H : ℕ)
    (w : PolicyFlowNode A O H → ℝ) : FiniteExperiment Θ (CausalFiniteTrace A O H) :=
  fun θ h => w (policyFlowNode H (List.ofFn h) (by simp)) * (ps θ).mass (List.ofFn h)

/-- Literal full-record controlled-behavior interpretation of a feasible flow. -/
theorem causalBehaviorFiniteExperiment_policyOfFiniteFlow
    (ps : Θ → CausalBehavior A O) (H : ℕ) (w : PolicyFlowNode A O H → ℝ)
    (x : CausalDecisionPoint A O H → A → ℝ) (hf : IsFinitePolicyFlow H w x) :
    causalBehaviorFiniteExperiment (policyOfFiniteFlow H w x hf).1 ps H =
      finiteFlowExperiment ps H w := by
  funext θ h
  change causalPolicyProb _ (List.ofFn h) * _ = _
  rw [causalPolicyProb_policyOfFiniteFlow H w x hf _ (by simp)]
  rfl

theorem finiteFlowExperiment_valid (ps : Θ → CausalBehavior A O)
    (H : ℕ) (w : PolicyFlowNode A O H → ℝ)
    (x : CausalDecisionPoint A O H → A → ℝ) (hf : IsFinitePolicyFlow H w x) :
    IsFiniteExperiment (finiteFlowExperiment ps H w) := by
  rw [← causalBehaviorFiniteExperiment_policyOfFiniteFlow ps H w x hf]
  exact causalBehaviorFiniteExperiment_valid _ (policyOfFiniteFlow H w x hf).2 ps H

end
end IdExp
