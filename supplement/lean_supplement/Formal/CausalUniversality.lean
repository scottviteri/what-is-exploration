import Formal.CausalExperiment
import Formal.FiniteTV
import Formal.Kuhn
import Formal.MixtureDecoder

/-!
# Finite-horizon universality for arbitrary causal response kernels

This module closes the causal wrapper connecting behavioral-policy Kuhn weights,
deterministic causal plans, induced finite experiments, and mixture decoders.
-/

namespace IdExp

open Finset

set_option linter.unusedSectionVars false

variable {A O Θ X : Type*} [Fintype A] [Fintype O]

/-! ## Deterministic plans as valid causal policies -/

/-- Package a chronological history as the corresponding bounded decision point. -/
noncomputable def causalDecisionPointOfHistory (n : ℕ) (h : CausalHistory A O)
    (hh : h.length < n) : CausalDecisionPoint A O n :=
  ⟨⟨h.length, hh⟩, h.get⟩

/-- A finite contingency plan induces a deterministic causal policy through its horizon.
After the horizon, an arbitrary fixed action completes it to an infinite policy; those rows
cannot affect the horizon-n experiment. -/
noncomputable def causalPolicyOfPlan [Nonempty A] (n : ℕ) (τ : CausalPlan A O n) :
    CausalPolicy A O := by
  classical
  exact fun h a =>
    if hh : h.length < n then
      if a = τ (causalDecisionPointOfHistory n h hh) then 1 else 0
    else
      if a = Classical.choice (inferInstance : Nonempty A) then 1 else 0

theorem isCausalPolicy_causalPolicyOfPlan [Nonempty A]
    (n : ℕ) (τ : CausalPlan A O n) :
    IsCausalPolicy (causalPolicyOfPlan n τ) := by
  classical
  intro h
  constructor
  · intro a
    by_cases hh : h.length < n
    · by_cases ha : a = τ (causalDecisionPointOfHistory n h hh) <;>
        simp [causalPolicyOfPlan, hh, ha]
    · by_cases ha : a = Classical.choice (inferInstance : Nonempty A) <;>
        simp [causalPolicyOfPlan, hh, ha]
  · by_cases hh : h.length < n
    · simp [causalPolicyOfPlan, hh]
    · simp [causalPolicyOfPlan, hh]

/-! ## Decision points visited by one finite trace -/

/-- The strict prefix preceding coordinate k of a finite trace. -/
noncomputable def causalTracePrefix {n : ℕ}
    (w : CausalFiniteTrace A O n) (k : Fin n) : CausalHistory A O :=
  List.ofFn fun j => w (Fin.castLT j (lt_trans j.isLt k.isLt))

/-- The decision point at which coordinate k of a finite trace is chosen. -/
noncomputable def causalTraceDecisionPoint {n : ℕ}
    (w : CausalFiniteTrace A O n) (k : Fin n) : CausalDecisionPoint A O n :=
  causalDecisionPointOfHistory n (causalTracePrefix w k)
    (by simp [causalTracePrefix, k.isLt])

theorem causalTraceDecisionPoint_injective {n : ℕ}
    (w : CausalFiniteTrace A O n) :
    Function.Injective (causalTraceDecisionPoint w) := by
  intro k l h
  have hv := congrArg (fun x : CausalDecisionPoint A O n => x.1.val) h
  apply Fin.ext
  simpa [causalTraceDecisionPoint, causalDecisionPointOfHistory, causalTracePrefix] using hv

theorem causalDecisionHistory_traceDecisionPoint {n : ℕ}
    (w : CausalFiniteTrace A O n) (k : Fin n) :
    causalDecisionHistory (causalTraceDecisionPoint w k) = causalTracePrefix w k := by
  unfold causalTraceDecisionPoint causalDecisionPointOfHistory causalDecisionHistory
  exact List.ofFn_get _

/-- A plan agrees with a full trace when it chooses every action recorded by that trace. -/
def CausalPlanAgreesTrace {n : ℕ} (τ : CausalPlan A O n)
    (w : CausalFiniteTrace A O n) : Prop :=
  ∀ k, τ (causalTraceDecisionPoint w k) = (w k).1

/-- The zero-one indicator that a deterministic plan agrees with a trace. -/
noncomputable def causalPlanTraceIndicator {n : ℕ} (τ : CausalPlan A O n)
    (w : CausalFiniteTrace A O n) : ℝ := by
  classical
  exact if CausalPlanAgreesTrace τ w then 1 else 0

/-- The zero-one contribution of one deterministic decision along a trace. -/
noncomputable def causalPlanStepIndicator {n : ℕ} (τ : CausalPlan A O n)
    (w : CausalFiniteTrace A O n) (k : Fin n) : ℝ := by
  classical
  exact if (w k).1 = τ (causalTraceDecisionPoint w k) then 1 else 0


/-! ## Policy likelihood along a finite trace -/

theorem causalPolicyProbFrom_append_singleton (π : CausalPolicy A O)
    (pre l : CausalHistory A O) (ao : A × O) :
    causalPolicyProbFrom π pre (l ++ [ao]) =
      causalPolicyProbFrom π pre l * π (pre ++ l) ao.1 := by
  induction l generalizing pre with
  | nil => simp [causalPolicyProbFrom]
  | cons x xs ih =>
      simp only [List.cons_append, causalPolicyProbFrom]
      rw [ih]
      simp only [List.append_assoc, List.singleton_append]
      ring

theorem causalPolicyProb_append_singleton (π : CausalPolicy A O)
    (h : CausalHistory A O) (ao : A × O) :
    causalPolicyProb π (h ++ [ao]) = causalPolicyProb π h * π h ao.1 := by
  simpa [causalPolicyProb] using causalPolicyProbFrom_append_singleton π [] h ao

/-- Policy likelihood is the product of its action probabilities at the visited prefixes. -/
theorem causalPolicyProb_ofFn (π : CausalPolicy A O) {n : ℕ}
    (w : CausalFiniteTrace A O n) :
    causalPolicyProb π (List.ofFn w) =
      ∏ k : Fin n, π (causalTracePrefix w k) (w k).1 := by
  induction n with
  | zero => simp [causalPolicyProb, causalPolicyProbFrom]
  | succ n ih =>
      rw [List.ofFn_succ_last, causalPolicyProb_append_singleton,
        Fin.prod_univ_castSucc, ih (fun i => w i.castSucc)]
      apply congrArg₂ (· * ·)
      · apply Finset.prod_congr rfl
        intro k _
        have hpref :
            causalTracePrefix (fun i => w i.castSucc) k =
              causalTracePrefix w k.castSucc := by
          unfold causalTracePrefix
          congr 1
        rw [hpref]
      · have hlast :
            causalTracePrefix w (Fin.last n) =
              List.ofFn (fun i => w i.castSucc) := by
          unfold causalTracePrefix
          congr 1
        rw [hlast]

theorem causalPolicyOfPlan_at_tracePrefix [Nonempty A] {n : ℕ}
    (τ : CausalPlan A O n) (w : CausalFiniteTrace A O n) (k : Fin n) :
    causalPolicyOfPlan n τ (causalTracePrefix w k) (w k).1 =
      causalPlanStepIndicator τ w k := by
  classical
  have hh : (causalTracePrefix w k).length < n := by
    simp [causalTracePrefix, k.isLt]
  have hd :
      causalDecisionPointOfHistory n (causalTracePrefix w k) hh =
        causalTraceDecisionPoint w k := by
    unfold causalTraceDecisionPoint
    congr
  rw [show causalPolicyOfPlan n τ (causalTracePrefix w k) (w k).1 =
      if (w k).1 =
          τ (causalDecisionPointOfHistory n (causalTracePrefix w k) hh)
        then 1 else 0 by
      simp [causalPolicyOfPlan, hh]]
  rw [hd]
  rfl

/-- A deterministic plan assigns policy likelihood one to its consistent traces and zero to
all other traces. -/
theorem causalPolicyProb_plan_eq_indicator [Nonempty A] {n : ℕ}
    (τ : CausalPlan A O n) (w : CausalFiniteTrace A O n) :
    causalPolicyProb (causalPolicyOfPlan n τ) (List.ofFn w) =
      causalPlanTraceIndicator τ w := by
  classical
  rw [causalPolicyProb_ofFn]
  unfold causalPlanTraceIndicator
  by_cases h : CausalPlanAgreesTrace τ w
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro k _
    rw [causalPolicyOfPlan_at_tracePrefix]
    simp [causalPlanStepIndicator, (h k).symm]
  · rw [if_neg h]
    have h' : ¬ ∀ k, τ (causalTraceDecisionPoint w k) = (w k).1 := by
      simpa [CausalPlanAgreesTrace] using h
    obtain ⟨k, hk⟩ := not_forall.mp h'
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    rw [causalPolicyOfPlan_at_tracePrefix]
    simp [causalPlanStepIndicator, Ne.symm hk]


/-! ## Exact Kuhn decomposition on causal traces -/

/-- The finite set of decision points visited by one full trace. -/
noncomputable def causalTraceDecisionSet {n : ℕ}
    (w : CausalFiniteTrace A O n) : Finset (CausalDecisionPoint A O n) := by
  classical
  exact Finset.univ.image (causalTraceDecisionPoint w)

/-- The action recorded by a trace at an arbitrary bounded decision point's depth. -/
def causalTraceTargetAction {n : ℕ} (w : CausalFiniteTrace A O n)
    (x : CausalDecisionPoint A O n) : A :=
  (w x.1).1

theorem causalTraceDecisionPoint_fst {n : ℕ}
    (w : CausalFiniteTrace A O n) (k : Fin n) :
    (causalTraceDecisionPoint w k).1 = k := by
  apply Fin.ext
  simp [causalTraceDecisionPoint, causalDecisionPointOfHistory, causalTracePrefix]

theorem causalTraceTargetAction_decisionPoint {n : ℕ}
    (w : CausalFiniteTrace A O n) (k : Fin n) :
    causalTraceTargetAction w (causalTraceDecisionPoint w k) = (w k).1 := by
  unfold causalTraceTargetAction
  rw [causalTraceDecisionPoint_fst]

theorem causalPlan_event_iff_agreesTrace {n : ℕ}
    (τ : CausalPlan A O n) (w : CausalFiniteTrace A O n) :
    (∀ x ∈ causalTraceDecisionSet w, τ x = causalTraceTargetAction w x) ↔
      CausalPlanAgreesTrace τ w := by
  classical
  constructor
  · intro h k
    have hmem :
        causalTraceDecisionPoint w k ∈ causalTraceDecisionSet w := by
      simp [causalTraceDecisionSet]
    rw [h _ hmem, causalTraceTargetAction_decisionPoint]
  · intro h x hx
    rw [causalTraceDecisionSet, Finset.mem_image] at hx
    obtain ⟨k, _, rfl⟩ := hx
    rw [h k, causalTraceTargetAction_decisionPoint]

theorem prod_causalTraceDecisionSet (π : CausalPolicy A O) {n : ℕ}
    (w : CausalFiniteTrace A O n) :
    ∏ x ∈ causalTraceDecisionSet w,
        π (causalDecisionHistory x) (causalTraceTargetAction w x) =
      ∏ k : Fin n, π (causalTracePrefix w k) (w k).1 := by
  classical
  unfold causalTraceDecisionSet
  rw [Finset.prod_image]
  · simp_rw [causalDecisionHistory_traceDecisionPoint,
      causalTraceTargetAction_decisionPoint]
  · exact (causalTraceDecisionPoint_injective w).injOn

/-- Kuhn weights assign a trace exactly its behavioral-policy action likelihood. -/
theorem sum_kuhnWeight_mul_traceIndicator
    [DecidableEq A] [DecidableEq O]
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    {n : ℕ} (w : CausalFiniteTrace A O n) :
    ∑ τ : CausalPlan A O n,
        kuhnWeight π n τ * causalPlanTraceIndicator τ w =
      causalPolicyProb π (List.ofFn w) := by
  classical
  rw [causalPolicyProb_ofFn]
  calc
    ∑ τ : CausalPlan A O n,
        kuhnWeight π n τ * causalPlanTraceIndicator τ w =
        ∑ τ : CausalPlan A O n,
          if ∀ x ∈ causalTraceDecisionSet w,
              τ x = causalTraceTargetAction w x
            then kuhnWeight π n τ else 0 := by
      apply Finset.sum_congr rfl
      intro τ _
      by_cases h : CausalPlanAgreesTrace τ w
      · have he := (causalPlan_event_iff_agreesTrace τ w).2 h
        rw [show causalPlanTraceIndicator τ w = 1 by
          simp [causalPlanTraceIndicator, h]]
        rw [if_pos he]
        ring
      · have he :
            ¬ ∀ x ∈ causalTraceDecisionSet w,
                τ x = causalTraceTargetAction w x :=
          fun he => h ((causalPlan_event_iff_agreesTrace τ w).1 he)
        rw [show causalPlanTraceIndicator τ w = 0 by
          simp [causalPlanTraceIndicator, h]]
        rw [if_neg he]
        ring
    _ = ∏ x ∈ causalTraceDecisionSet w,
        π (causalDecisionHistory x) (causalTraceTargetAction w x) :=
      kuhnWeight_event π hπ n (causalTraceDecisionSet w)
        (causalTraceTargetAction w)
    _ = ∏ k : Fin n, π (causalTracePrefix w k) (w k).1 :=
      prod_causalTraceDecisionSet π w


/-! ## Lossless observation-only representation for deterministic plans -/

/-- Controlled response likelihood factors over the visited prefixes. -/
theorem causalResponseProb_ofFn (Q : CausalResponse A O) {n : ℕ}
    (w : CausalFiniteTrace A O n) :
    causalResponseProb Q (List.ofFn w) =
      ∏ k : Fin n, Q (causalTracePrefix w k) (w k).1 (w k).2 := by
  induction n with
  | zero => simp [causalResponseProb, causalResponseProbFrom]
  | succ n ih =>
      rw [List.ofFn_succ_last, causalResponseProb_append_singleton,
        Fin.prod_univ_castSucc, ih (fun i => w i.castSucc)]
      apply congrArg₂ (· * ·)
      · apply Finset.prod_congr rfl
        intro k _
        have hpref :
            causalTracePrefix (fun i => w i.castSucc) k =
              causalTracePrefix w k.castSucc := by
          unfold causalTracePrefix
          congr 1
        rw [hpref]
      · have hlast :
            causalTracePrefix w (Fin.last n) =
              List.ofFn (fun i => w i.castSucc) := by
          unfold causalTracePrefix
          congr 1
        rw [hlast]

/-- Observation words produced through an exact finite horizon. -/
abbrev CausalObservationTrace (O : Type*) (n : ℕ) := Fin n → O

/-- Forget the controlled action labels in a full causal trace. -/
def causalTraceObservations {n : ℕ} (w : CausalFiniteTrace A O n) :
    CausalObservationTrace O n :=
  fun k => (w k).2

/-- Recursively reattach the unique action labels prescribed by a deterministic
contingency plan to an observation word. -/
noncomputable def causalTraceOfObservationsAt {n : ℕ}
    (τ : CausalPlan A O n) (o : CausalObservationTrace O n) (k : Fin n) : A × O :=
  (τ (causalDecisionPointOfHistory n
      (List.ofFn fun j =>
        causalTraceOfObservationsAt τ o
          (Fin.castLT j (lt_trans j.isLt k.isLt)))
      (by simp [k.isLt])),
    o k)
termination_by k.val

/-- The full trace reconstructed from a plan and its observation word. -/
noncomputable def causalTraceOfObservations {n : ℕ}
    (τ : CausalPlan A O n) (o : CausalObservationTrace O n) :
    CausalFiniteTrace A O n :=
  fun k => causalTraceOfObservationsAt τ o k

/-- Reattaching plan actions does not change the observation word. -/
theorem causalTraceObservations_traceOfObservations {n : ℕ}
    (τ : CausalPlan A O n) (o : CausalObservationTrace O n) :
    causalTraceObservations (causalTraceOfObservations τ o) = o := by
  funext k
  unfold causalTraceObservations causalTraceOfObservations
  rw [causalTraceOfObservationsAt.eq_1]

/-- The reconstructed trace follows the deterministic plan at every visited
history. -/
theorem causalPlanAgreesTrace_traceOfObservations {n : ℕ}
    (τ : CausalPlan A O n) (o : CausalObservationTrace O n) :
    CausalPlanAgreesTrace τ (causalTraceOfObservations τ o) := by
  intro k
  unfold causalTraceDecisionPoint causalTracePrefix causalTraceOfObservations
  rw [causalTraceOfObservationsAt.eq_1]


/-- Two traces compatible with the same deterministic plan and carrying the
same observations are equal.  Chronology is essential: equality through time
`k - 1` identifies the decision point at time `k`, so the plan identifies the
next action. -/
theorem causalTrace_eq_of_planAgrees_of_observations_eq {n : ℕ}
    (τ : CausalPlan A O n) {u v : CausalFiniteTrace A O n}
    (hu : CausalPlanAgreesTrace τ u) (hv : CausalPlanAgreesTrace τ v)
    (ho : causalTraceObservations u = causalTraceObservations v) :
    u = v := by
  have hcoord : ∀ m : ℕ, ∀ hm : m < n, u ⟨m, hm⟩ = v ⟨m, hm⟩ := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro hm
        let k : Fin n := ⟨m, hm⟩
        have hpref : causalTracePrefix u k = causalTracePrefix v k := by
          unfold causalTracePrefix
          congr 1
          funext j
          exact ih j.val j.isLt (lt_trans j.isLt hm)
        have hdp :
            causalTraceDecisionPoint u k = causalTraceDecisionPoint v k := by
          unfold causalTraceDecisionPoint
          congr 1
        apply Prod.ext
        · rw [← hu k, ← hv k, hdp]
        · exact congrFun ho k
  funext k
  exact hcoord k.val k.isLt

/-- Reconstruction is the unique plan-compatible lift of an observation word. -/
theorem causalTraceOfObservations_observations_eq_of_agrees {n : ℕ}
    (τ : CausalPlan A O n) (w : CausalFiniteTrace A O n)
    (hw : CausalPlanAgreesTrace τ w) :
    causalTraceOfObservations τ (causalTraceObservations w) = w := by
  apply causalTrace_eq_of_planAgrees_of_observations_eq τ
    (causalPlanAgreesTrace_traceOfObservations τ (causalTraceObservations w)) hw
  exact causalTraceObservations_traceOfObservations τ (causalTraceObservations w)

/-- A full trace is the reconstruction of `o` exactly when it follows the plan
and has observation word `o`. -/
theorem eq_causalTraceOfObservations_iff {n : ℕ}
    (τ : CausalPlan A O n) (w : CausalFiniteTrace A O n)
    (o : CausalObservationTrace O n) :
    w = causalTraceOfObservations τ o ↔
      CausalPlanAgreesTrace τ w ∧ causalTraceObservations w = o := by
  constructor
  · rintro rfl
    exact ⟨causalPlanAgreesTrace_traceOfObservations τ o,
      causalTraceObservations_traceOfObservations τ o⟩
  · rintro ⟨hw, ho⟩
    apply causalTrace_eq_of_planAgrees_of_observations_eq τ hw
      (causalPlanAgreesTrace_traceOfObservations τ o)
    exact ho.trans (causalTraceObservations_traceOfObservations τ o).symm

/-- Distinct observation words reconstruct to distinct full traces. -/
theorem causalTraceOfObservations_injective {n : ℕ}
    (τ : CausalPlan A O n) : Function.Injective (causalTraceOfObservations τ) :=
  Function.LeftInverse.injective (causalTraceObservations_traceOfObservations τ)


/-- Deterministic garbling from a full trace to its observation word. -/
noncomputable def causalForgetActionsRule {n : ℕ} :
    CausalFiniteTrace A O n → CausalObservationTrace O n → ℝ := by
  classical
  exact fun w o => if causalTraceObservations w = o then 1 else 0

theorem causalForgetActionsRule_mem_stochasticRules {n : ℕ} :
    causalForgetActionsRule (A := A) (O := O) (n := n) ∈
      stochasticRules (CausalFiniteTrace A O n) (CausalObservationTrace O n) := by
  classical
  intro w _
  constructor
  · intro o
    by_cases h : causalTraceObservations w = o <;>
      simp [causalForgetActionsRule, h]
  · simp [causalForgetActionsRule]

/-- Deterministic garbling that reattaches the action labels prescribed by a
fixed contingency plan. -/
noncomputable def causalAttachPlanActionsRule {n : ℕ} (τ : CausalPlan A O n) :
    CausalObservationTrace O n → CausalFiniteTrace A O n → ℝ := by
  classical
  exact fun o w => if w = causalTraceOfObservations τ o then 1 else 0

theorem causalAttachPlanActionsRule_mem_stochasticRules {n : ℕ}
    (τ : CausalPlan A O n) :
    causalAttachPlanActionsRule τ ∈
      stochasticRules (CausalObservationTrace O n) (CausalFiniteTrace A O n) := by
  classical
  intro o _
  constructor
  · intro w
    by_cases h : w = causalTraceOfObservations τ o <;>
      simp [causalAttachPlanActionsRule, h]
  · simp [causalAttachPlanActionsRule]

/-- The observation-only experiment induced by a deterministic plan is the
literal marginal of its full action--observation experiment. -/
noncomputable def causalPlanObservationExperiment [Nonempty A]
    (n : ℕ) (τ : CausalPlan A O n) (Qs : Θ → CausalResponse A O) :
    FiniteExperiment Θ (CausalObservationTrace O n) :=
  finiteDecisionLaw
    (causalFiniteExperiment (causalPolicyOfPlan n τ) Qs n)
    causalForgetActionsRule


/-- Normalized causal response kernels make the observation marginal a genuine
finite statistical experiment, with no finiteness assumption on the world
class. -/
theorem causalPlanObservationExperiment_valid [Nonempty A]
    (n : ℕ) (τ : CausalPlan A O n) (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) :
    IsFiniteExperiment (causalPlanObservationExperiment n τ Qs) := by
  exact finiteDecisionLaw_valid _
    (causalFiniteExperiment_valid (causalPolicyOfPlan n τ)
      (isCausalPolicy_causalPolicyOfPlan n τ) Qs hQ n)
    _ causalForgetActionsRule_mem_stochasticRules

/-- A trace inconsistent with a deterministic plan has zero probability in
that plan's induced experiment, independently of the causal response kernel. -/
theorem causalFiniteExperiment_plan_eq_zero_of_not_agrees [Nonempty A]
    {n : ℕ} (τ : CausalPlan A O n) (Qs : Θ → CausalResponse A O)
    (θ : Θ) (w : CausalFiniteTrace A O n)
    (hw : ¬ CausalPlanAgreesTrace τ w) :
    causalFiniteExperiment (causalPolicyOfPlan n τ) Qs n θ w = 0 := by
  unfold causalFiniteExperiment
  rw [causalTraceProb_factor, causalPolicyProb_plan_eq_indicator]
  simp [causalPlanTraceIndicator, hw]

/-- The probability of an observation word is exactly the probability of its
unique plan-compatible full-trace reconstruction. -/
theorem causalPlanObservationExperiment_eq_reconstruction [Nonempty A]
    (n : ℕ) (τ : CausalPlan A O n) (Qs : Θ → CausalResponse A O)
    (θ : Θ) (o : CausalObservationTrace O n) :
    causalPlanObservationExperiment n τ Qs θ o =
      causalFiniteExperiment (causalPolicyOfPlan n τ) Qs n θ
        (causalTraceOfObservations τ o) := by
  classical
  unfold causalPlanObservationExperiment finiteDecisionLaw
  let w₀ := causalTraceOfObservations τ o
  rw [Finset.sum_eq_single w₀]
  · simp [causalForgetActionsRule, w₀,
      causalTraceObservations_traceOfObservations]
  · intro w _ hne
    by_cases hw : CausalPlanAgreesTrace τ w
    · have hobs : causalTraceObservations w ≠ o := by
        intro ho
        exact hne ((eq_causalTraceOfObservations_iff τ w o).2 ⟨hw, ho⟩)
      simp [causalForgetActionsRule, hobs]
    · rw [causalFiniteExperiment_plan_eq_zero_of_not_agrees τ Qs θ w hw]
      simp
  · simp


/-- Reattaching the plan's action labels to its observation marginal recovers
its full trace experiment exactly. -/
theorem causalPlanObservationExperiment_attach [Nonempty A]
    (n : ℕ) (τ : CausalPlan A O n) (Qs : Θ → CausalResponse A O) :
    finiteDecisionLaw (causalPlanObservationExperiment n τ Qs)
        (causalAttachPlanActionsRule τ) =
      causalFiniteExperiment (causalPolicyOfPlan n τ) Qs n := by
  classical
  funext θ w
  unfold finiteDecisionLaw
  by_cases hw : CausalPlanAgreesTrace τ w
  · have hrec :=
      causalTraceOfObservations_observations_eq_of_agrees τ w hw
    rw [Finset.sum_eq_single (causalTraceObservations w)]
    · rw [causalPlanObservationExperiment_eq_reconstruction]
      rw [hrec]
      simp [causalAttachPlanActionsRule, hrec]
    · intro o _ hne
      have hnot : w ≠ causalTraceOfObservations τ o := by
        intro heq
        have hobs := (eq_causalTraceOfObservations_iff τ w o).1 heq
        exact hne hobs.2.symm
      simp [causalAttachPlanActionsRule, hnot]
    · simp
  · rw [causalFiniteExperiment_plan_eq_zero_of_not_agrees τ Qs θ w hw]
    apply Finset.sum_eq_zero
    intro o _
    have hnot : w ≠ causalTraceOfObservations τ o := by
      intro heq
      exact hw ((eq_causalTraceOfObservations_iff τ w o).1 heq).1
    simp [causalAttachPlanActionsRule, hnot]

/-- Under a fixed deterministic plan, the full trace experiment and the
observation-only experiment are exactly Blackwell equivalent.  The equivalence
is uniform in the world family and requires no Markov or latent-state
assumption on its causal response kernels. -/
theorem causalPlan_full_observation_blackwell_equiv [Nonempty A]
    (n : ℕ) (τ : CausalPlan A O n) (Qs : Θ → CausalResponse A O) :
    FiniteBlackwellLE (causalPlanObservationExperiment n τ Qs)
        (causalFiniteExperiment (causalPolicyOfPlan n τ) Qs n) ∧
      FiniteBlackwellLE (causalFiniteExperiment (causalPolicyOfPlan n τ) Qs n)
        (causalPlanObservationExperiment n τ Qs) := by
  constructor
  · exact ⟨causalForgetActionsRule,
      causalForgetActionsRule_mem_stochasticRules, rfl⟩
  · exact ⟨causalAttachPlanActionsRule τ,
      causalAttachPlanActionsRule_mem_stochasticRules τ,
      causalPlanObservationExperiment_attach n τ Qs⟩




/-! ## Experiment-level finite-horizon universality -/

/-- The experiment induced by a randomized causal policy is exactly the world-independent
Kuhn mixture of the experiments induced by deterministic contingency plans. -/
theorem causalFiniteExperiment_kuhn_decomposition
    [DecidableEq A] [DecidableEq O] [Nonempty A]
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (n : ℕ) :
    causalFiniteExperiment π Qs n =
      fun θ w => ∑ τ : CausalPlan A O n,
        kuhnWeight π n τ *
          causalFiniteExperiment (causalPolicyOfPlan n τ) Qs n θ w := by
  funext θ w
  unfold causalFiniteExperiment
  rw [causalTraceProb_factor]
  simp_rw [causalTraceProb_factor, causalPolicyProb_plan_eq_indicator]
  calc
    causalPolicyProb π (List.ofFn w) *
        causalResponseProb (Qs θ) (List.ofFn w) =
        (∑ τ : CausalPlan A O n,
          kuhnWeight π n τ * causalPlanTraceIndicator τ w) *
            causalResponseProb (Qs θ) (List.ofFn w) := by
      rw [sum_kuhnWeight_mul_traceIndicator π hπ w]
    _ = ∑ τ : CausalPlan A O n,
        kuhnWeight π n τ *
          (causalPlanTraceIndicator τ w *
            causalResponseProb (Qs θ) (List.ofFn w)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro τ _
      ring

/-- If one source experiment simulates every deterministic causal-plan experiment through
horizon n with error at most c, a single mixed decoder simulates every randomized policy
experiment through that horizon with the same error. -/
theorem exists_decoder_to_causalPolicy_of_plan_decoders
    [Fintype X] [DecidableEq A] [DecidableEq O] [Nonempty A]
    (E : FiniteExperiment Θ X)
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (n : ℕ) (c : ℝ)
    (h : ∀ τ : CausalPlan A O n,
      ∃ G ∈ stochasticRules X (CausalFiniteTrace A O n),
        ∀ θ,
          decodeErr E
            (causalFiniteExperiment (causalPolicyOfPlan n τ) Qs n) G θ ≤ c) :
    ∃ G ∈ stochasticRules X (CausalFiniteTrace A O n),
      ∀ θ, decodeErr E (causalFiniteExperiment π Qs n) G θ ≤ c := by
  let Fs : CausalPlan A O n →
      FiniteExperiment Θ (CausalFiniteTrace A O n) :=
    fun τ => causalFiniteExperiment (causalPolicyOfPlan n τ) Qs n
  obtain ⟨G, hG, herr⟩ :=
    exists_mixture_decoder E Fs (kuhnWeight_isDist π hπ n) h
  refine ⟨G, hG, ?_⟩
  intro θ
  rw [show causalFiniteExperiment π Qs n =
      fun θ' w => ∑ τ : CausalPlan A O n,
        kuhnWeight π n τ * Fs τ θ' w by
    exact causalFiniteExperiment_kuhn_decomposition π hπ Qs n]
  exact herr θ


/-- **Observation-only finite-horizon causal universality.**  If a source
experiment simulates the observation experiment of every deterministic
contingency plan through horizon `n` with error at most `c`, then one decoder
simulates the full action--observation experiment of every randomized causal
policy through that horizon with the same error.  This theorem combines exact
chronological action reattachment, total-variation data processing, Kuhn's
world-independent plan mixture, and decoder convexity. -/
theorem exists_decoder_to_causalPolicy_of_observation_plan_decoders
    [Fintype X] [DecidableEq A] [DecidableEq O] [Nonempty A]
    (E : FiniteExperiment Θ X)
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (n : ℕ) (c : ℝ)
    (h : ∀ τ : CausalPlan A O n,
      ∃ G ∈ stochasticRules X (CausalObservationTrace O n),
        ∀ θ,
          decodeErr E (causalPlanObservationExperiment n τ Qs) G θ ≤ c) :
    ∃ G ∈ stochasticRules X (CausalFiniteTrace A O n),
      ∀ θ, decodeErr E (causalFiniteExperiment π Qs n) G θ ≤ c := by
  apply exists_decoder_to_causalPolicy_of_plan_decoders E π hπ Qs n c
  intro τ
  obtain ⟨G, hG, herr⟩ := h τ
  refine ⟨stochasticRuleComp G (causalAttachPlanActionsRule τ),
    stochasticRuleComp_mem_stochasticRules hG
      (causalAttachPlanActionsRule_mem_stochasticRules τ), ?_⟩
  intro θ
  have hpost := decodeErr_stochasticRuleComp_le E
    (causalPlanObservationExperiment n τ Qs) G
    (causalAttachPlanActionsRule τ)
    (causalAttachPlanActionsRule_mem_stochasticRules τ) θ
  rw [causalPlanObservationExperiment_attach n τ Qs] at hpost
  exact hpost.trans (herr θ)

/-- The one-step native observation law is the response at the root. -/
theorem causalPlanObservationExperiment_one_constant [Nonempty A]
    {Θ : Type*} (Qs : Θ → CausalResponse A O) (a : A) (θ : Θ)
    (w : CausalObservationTrace O 1) :
    causalPlanObservationExperiment 1 (fun _ => a) Qs θ w = Qs θ [] a (w 0) := by
  rw [causalPlanObservationExperiment_eq_reconstruction]
  simp [causalFiniteExperiment, causalTraceProb, causalTraceProbFrom,
    List.ofFn_succ, causalTraceOfObservations, causalTraceOfObservationsAt,
    causalPolicyOfPlan]

/-! ## Restricting deterministic policies to native prefixes -/

section DeterministicPrefix

variable [Nonempty A]

/-- Restrict a full-history deterministic action map to a finite native plan.
Recorded past actions are permitted in the map, since they are reconstructed
recursively from past observations under the same deterministic plan. -/
def deterministicPrefixPlan (p : CausalHistory A O → A) (n : ℕ) : CausalPlan A O n :=
  fun d => p (causalDecisionHistory d)

/-- A deterministic policy and its finite restriction induce the same full
trace experiment through that horizon, even in stochastic causal worlds. -/
theorem causalFiniteExperiment_deterministicPrefixPlan
    (p : CausalHistory A O → A) (Qs : Θ → CausalResponse A O) (n : ℕ) :
    causalFiniteExperiment (causalPolicyOfPlan n (deterministicPrefixPlan p n)) Qs n =
      causalFiniteExperiment (detPolicy p) Qs n := by
  classical
  funext θ w
  unfold causalFiniteExperiment
  rw [causalTraceProb_factor, causalTraceProb_factor]
  congr 1
  rw [causalPolicyProb_ofFn, causalPolicyProb_ofFn]
  apply Finset.prod_congr rfl
  intro k _
  rw [causalPolicyOfPlan_at_tracePrefix]
  simp [causalPlanStepIndicator, deterministicPrefixPlan,
    causalDecisionHistory_traceDecisionPoint, detPolicy]

end DeterministicPrefix

end IdExp
