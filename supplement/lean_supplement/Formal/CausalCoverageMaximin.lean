import Formal.CausalEpisodicCoverage
import Formal.CausalObservationPlan

/-!
# Prefix-coverage conservation and maximin uniform behavior

The episodic section of the paper uses a finite combinatorial fact that was
previously only proved on paper: at a fixed depth, no causal behavior policy
can make every deterministic native intervention more likely to match than
uniform random actions do.  This module proves that statement on the actual
finite causal transcript.

Writing `K_n` for the number of observation-tree decision nodes, every
realized length-`n` trace fixes exactly `n` of those nodes.  Thus exactly
`|A|^(K_n-n)` observation-only plans agree with that trace, and summing the
match probabilities of an arbitrary valid policy over every observation-only
plan gives the literal conservation law `∑_σ p_σ = |A|^(K_n-n)`.  We also
record the division-free identity `|A|^n ∑_σ p_σ = |A|^K_n`.

The earlier probability-weighted form is retained: averaging coverage against
the Kuhn distribution obtained by independently choosing every full-history
contingency-plan row uniformly gives `|A|⁻ⁿ`, for every world.  Hence some plan
has match probability at most `|A|⁻ⁿ`; uniform behavior attains equality for
every plan and every world.  Canonicalizing that plan gives the same statement
for the observation-only intervention trees used in the reader paper.  The
exact plan count is `|A|^K_n`, where `K 0 = 0` and
`K (n+1) = 1 + |O| K n`.
-/

namespace IdExp

open Finset Set

set_option linter.unusedSectionVars false

variable {A O Θ : Type*} [Fintype A] [Fintype O]
  [DecidableEq A] [DecidableEq O] [Nonempty A] [Nonempty O]

/-- Number of internal nodes in the complete observation tree through depth
`n`.  This recursive form is valid also for a one-symbol observation alphabet
and avoids division by `|O|-1`. -/
def observationTreeNodeCount (O : Type*) [Fintype O] : ℕ → ℕ
  | 0 => 0
  | n + 1 => 1 + Fintype.card O * observationTreeNodeCount O n

/-- The observation histories at which a depth-`n` observation-tree plan
chooses actions. -/
abbrev CausalObservationDecisionPoint (O : Type*) (n : ℕ) :=
  Σ k : Fin n, Fin k.1 → O

namespace CausalObservationDecisionPoint

/-- Prepend one observation to a shorter observation decision point. -/
def cons {n : ℕ} (o : O) (x : CausalObservationDecisionPoint O n) :
    CausalObservationDecisionPoint O (n + 1) :=
  ⟨x.1.succ, Fin.cons o x.2⟩

end CausalObservationDecisionPoint

namespace CausalObservationPlan

/-- Flatten an observation-tree plan to its action at every observation
history of length less than the horizon. -/
def decision : ∀ {n : ℕ}, CausalObservationPlan A O n →
    CausalObservationDecisionPoint O n → A
  | 0, _, x => Fin.elim0 x.1
  | n + 1, σ, ⟨⟨0, _⟩, _⟩ => σ.1
  | n + 1, σ, ⟨⟨k + 1, hk⟩, h⟩ =>
      decision (σ.2 (h 0)) ⟨⟨k, Nat.lt_of_succ_lt_succ hk⟩, Fin.tail h⟩

/-- Rebuild an observation tree from its flattened decision function. -/
def ofDecision : ∀ n : ℕ,
    (CausalObservationDecisionPoint O n → A) → CausalObservationPlan A O n
  | 0, _ => PUnit.unit
  | n + 1, f =>
      (f ⟨0, Fin.elim0⟩,
        fun o => ofDecision n (fun x => f (CausalObservationDecisionPoint.cons o x)))

theorem decision_ofDecision : ∀ n (f : CausalObservationDecisionPoint O n → A),
    decision (ofDecision n f) = f := by
  intro n
  induction n with
  | zero =>
      intro f
      funext x
      exact Fin.elim0 x.1
  | succ n ih =>
      intro f
      funext x
      obtain ⟨⟨k, hk⟩, h⟩ := x
      cases k with
      | zero =>
          change f ⟨0, Fin.elim0⟩ = f ⟨⟨0, hk⟩, h⟩
          congr 1
          apply Sigma.ext
          · apply Fin.ext
            rfl
          · exact heq_of_eq (funext fun i => Fin.elim0 i)
      | succ k =>
          change decision (ofDecision n (fun y =>
              f (CausalObservationDecisionPoint.cons (h 0) y)))
              ⟨⟨k, Nat.lt_of_succ_lt_succ hk⟩, Fin.tail h⟩ =
            f ⟨⟨k + 1, hk⟩, h⟩
          rw [ih]
          congr 1
          apply Sigma.ext
          · apply Fin.ext
            rfl
          · exact heq_of_eq (Fin.cons_self_tail h)

theorem ofDecision_decision : ∀ n (σ : CausalObservationPlan A O n),
    ofDecision n (decision σ) = σ := by
  intro n
  induction n with
  | zero =>
      intro σ
      rcases σ with ⟨⟩
      rfl
  | succ n ih =>
      intro σ
      apply Prod.ext
      · rfl
      · funext o
        exact ih (σ.2 o)

/-- Observation trees are exactly action-valued functions on the finite set
of observation histories shorter than the horizon. -/
def equivDecision (n : ℕ) :
    CausalObservationPlan A O n ≃
      (CausalObservationDecisionPoint O n → A) where
  toFun := decision
  invFun := ofDecision n
  left_inv := ofDecision_decision n
  right_inv := decision_ofDecision n

end CausalObservationPlan

/-- The flattened observation-tree decision set has exactly `K_n` nodes. -/
theorem card_causalObservationDecisionPoint (n : ℕ) :
    Nat.card (CausalObservationDecisionPoint O n) =
      observationTreeNodeCount O n := by
  induction n with
  | zero => simp [CausalObservationDecisionPoint, observationTreeNodeCount]
  | succ n ih =>
      simp only [CausalObservationDecisionPoint, Nat.card_eq_fintype_card,
        Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin]
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, Fin.val_succ, pow_succ']
      rw [← Finset.mul_sum]
      have ih' : (∑ i : Fin n, Fintype.card O ^ i.1) =
          observationTreeNodeCount O n := by
        simpa only [CausalObservationDecisionPoint,
          Nat.card_eq_fintype_card, Fintype.card_sigma,
          Fintype.card_fun, Fintype.card_fin] using ih
      rw [ih']
      rfl

/-- The recursive node count is the literal geometric sum over observation
history depths.  The recursive form remains preferable at `|O| = 1`, where
the usual quotient formula has a zero denominator. -/
theorem observationTreeNodeCount_eq_sum (n : ℕ) :
    observationTreeNodeCount O n =
      ∑ k : Fin n, Nat.card O ^ k.1 := by
  have h := (card_causalObservationDecisionPoint (O := O) n).symm
  simpa only [CausalObservationDecisionPoint, Nat.card_eq_fintype_card,
    Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin] using h

/-- There are at least `n` nodes on a nonempty observation tree of depth
`n`; this makes the paper's exponent `K_n-n` literal. -/
theorem depth_le_observationTreeNodeCount (n : ℕ) :
    n ≤ observationTreeNodeCount O n := by
  induction n with
  | zero => simp [observationTreeNodeCount]
  | succ n ih =>
      simp only [observationTreeNodeCount]
      have hcard : 1 ≤ Fintype.card O := Fintype.card_pos
      have hmul : observationTreeNodeCount O n ≤
          Fintype.card O * observationTreeNodeCount O n := by
        simpa only [one_mul] using
          Nat.mul_le_mul_right (observationTreeNodeCount O n) hcard
      omega

/-- Forget the past-action coordinates of a full causal decision point. -/
def causalDecisionPointObservationPart {n : ℕ}
    (x : CausalDecisionPoint A O n) :
    CausalObservationDecisionPoint O n :=
  ⟨x.1, fun i => (x.2 i).2⟩

/-- Flattening an observation tree agrees pointwise with its existing
full-history embedding after past actions are erased. -/
theorem CausalObservationPlan.decision_eq_toCausalPlan :
    ∀ n (σ : CausalObservationPlan A O n) (x : CausalDecisionPoint A O n),
      σ.decision (causalDecisionPointObservationPart x) = σ.toCausalPlan x := by
  intro n
  induction n with
  | zero =>
      intro σ x
      exact Fin.elim0 x.1
  | succ n ih =>
      intro σ x
      obtain ⟨⟨k, hk⟩, h⟩ := x
      cases k with
      | zero => rfl
      | succ k =>
          exact ih (σ.2 (h 0).2)
            ⟨⟨k, Nat.lt_of_succ_lt_succ hk⟩, Fin.tail h⟩

/-- The observation-history node visited just before step `k` of a full
trace. -/
noncomputable def causalObservationTraceDecisionPoint {n : ℕ}
    (w : CausalFiniteTrace A O n) (k : Fin n) :
    CausalObservationDecisionPoint O n :=
  causalDecisionPointObservationPart (causalTraceDecisionPoint w k)

theorem causalObservationTraceDecisionPoint_fst {n : ℕ}
    (w : CausalFiniteTrace A O n) (k : Fin n) :
    (causalObservationTraceDecisionPoint w k).1 = k := by
  unfold causalObservationTraceDecisionPoint causalDecisionPointObservationPart
  exact causalTraceDecisionPoint_fst w k

theorem causalObservationTraceDecisionPoint_injective {n : ℕ}
    (w : CausalFiniteTrace A O n) :
    Function.Injective (causalObservationTraceDecisionPoint w) := by
  intro k l h
  have hfst := congrArg (fun x : CausalObservationDecisionPoint O n => x.1) h
  rw [causalObservationTraceDecisionPoint_fst,
    causalObservationTraceDecisionPoint_fst] at hfst
  exact hfst

/-- The `n` distinct observation-history nodes visited by a length-`n`
trace. -/
noncomputable def causalObservationTraceDecisionSet {n : ℕ}
    (w : CausalFiniteTrace A O n) :
    Finset (CausalObservationDecisionPoint O n) := by
  classical
  exact Finset.univ.image (causalObservationTraceDecisionPoint w)

theorem card_causalObservationTraceDecisionSet {n : ℕ}
    (w : CausalFiniteTrace A O n) :
    (causalObservationTraceDecisionSet w).card = n := by
  classical
  unfold causalObservationTraceDecisionSet
  rw [Finset.card_image_of_injective _
    (causalObservationTraceDecisionPoint_injective w)]
  simp

/-- The trace action prescribed at the depth of an arbitrary observation
decision point. -/
def causalObservationTraceTargetAction {n : ℕ}
    (w : CausalFiniteTrace A O n)
    (x : CausalObservationDecisionPoint O n) : A :=
  (w x.1).1

theorem causalObservationTraceTargetAction_decisionPoint {n : ℕ}
    (w : CausalFiniteTrace A O n) (k : Fin n) :
    causalObservationTraceTargetAction w
        (causalObservationTraceDecisionPoint w k) = (w k).1 := by
  unfold causalObservationTraceTargetAction
  rw [causalObservationTraceDecisionPoint_fst]

/-- Agreement of an observation tree with a trace is exactly agreement of
its flattened decision function on the `n` visited observation prefixes. -/
theorem causalObservationPlan_event_iff_agreesTrace {n : ℕ}
    (σ : CausalObservationPlan A O n) (w : CausalFiniteTrace A O n) :
    (∀ x ∈ causalObservationTraceDecisionSet w,
        σ.decision x = causalObservationTraceTargetAction w x) ↔
      CausalPlanAgreesTrace σ.toCausalPlan w := by
  classical
  constructor
  · intro h k
    have hmem : causalObservationTraceDecisionPoint w k ∈
        causalObservationTraceDecisionSet w := by
      simp [causalObservationTraceDecisionSet]
    rw [← CausalObservationPlan.decision_eq_toCausalPlan n σ
      (causalTraceDecisionPoint w k)]
    exact (h _ hmem).trans
      (causalObservationTraceTargetAction_decisionPoint w k)
  · intro h x hx
    rw [causalObservationTraceDecisionSet, Finset.mem_image] at hx
    obtain ⟨k, _, rfl⟩ := hx
    change σ.decision
        (causalDecisionPointObservationPart (causalTraceDecisionPoint w k)) =
      causalObservationTraceTargetAction w
        (causalObservationTraceDecisionPoint w k)
    rw [CausalObservationPlan.decision_eq_toCausalPlan n σ
      (causalTraceDecisionPoint w k), h k,
      causalObservationTraceTargetAction_decisionPoint]

/-- A function constrained on a finite set is equivalently an arbitrary
function on the complementary coordinates. -/
noncomputable def constrainedFunctionEquiv
    {H B : Type*} [DecidableEq H] (S : Finset H) (target : H → B) :
    {f : H → B // ∀ x ∈ S, f x = target x} ≃
      ({x : H // x ∉ S} → B) where
  toFun := fun f x => f.1 x.1
  invFun := fun g =>
    ⟨fun x => if hx : x ∈ S then target x else g ⟨x, hx⟩, by
      intro x hx
      simp [hx]⟩
  left_inv := by
    intro f
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ S
    · simp [hx, f.2 x hx]
    · simp [hx]
  right_inv := by
    intro g
    funext x
    simp [x.2]

/-- Exact cardinality of a finite function-space fiber with prescribed
values on `S`. -/
theorem card_constrainedFunction
    {H B : Type*} [Fintype H] [Fintype B] [DecidableEq H]
    (S : Finset H) (target : H → B) :
    Nat.card {f : H → B // ∀ x ∈ S, f x = target x} =
      Nat.card B ^ (Nat.card H - S.card) := by
  classical
  have hfree : Nat.card {x : H // x ∉ S} = Nat.card H - S.card := by
    simp only [Nat.card_eq_fintype_card]
    calc
      Fintype.card {x : H // x ∉ S} =
          Fintype.card H - Fintype.card {x : H // x ∈ S} :=
        Fintype.card_subtype_compl (fun x : H => x ∈ S)
      _ = Fintype.card H - S.card := by
        rw [Fintype.card_subtype]
        simp
  rw [Nat.card_congr (constrainedFunctionEquiv S target), Nat.card_fun,
    hfree]

/-- **Per-realization count.**  Every length-`n` episode is consistent
with exactly `|A|^(K_n-n)` deterministic observation-tree tests. -/
theorem card_causalObservationPlan_agreesTrace {n : ℕ}
    (w : CausalFiniteTrace A O n) :
    Nat.card { σ : CausalObservationPlan A O n //
        CausalPlanAgreesTrace σ.toCausalPlan w } =
      Nat.card A ^ (observationTreeNodeCount O n - n) := by
  classical
  let e :
      { σ : CausalObservationPlan A O n //
          CausalPlanAgreesTrace σ.toCausalPlan w } ≃
        {f : CausalObservationDecisionPoint O n → A //
          ∀ x ∈ causalObservationTraceDecisionSet w,
            f x = causalObservationTraceTargetAction w x} :=
    (CausalObservationPlan.equivDecision (A := A) (O := O) n).subtypeEquiv
      (fun σ => (causalObservationPlan_event_iff_agreesTrace σ w).symm)
  calc
    Nat.card { σ : CausalObservationPlan A O n //
        CausalPlanAgreesTrace σ.toCausalPlan w } =
        Nat.card {f : CausalObservationDecisionPoint O n → A //
          ∀ x ∈ causalObservationTraceDecisionSet w,
            f x = causalObservationTraceTargetAction w x} :=
      Nat.card_congr e
    _ = Nat.card A ^
        (Nat.card (CausalObservationDecisionPoint O n) -
          (causalObservationTraceDecisionSet w).card) :=
      card_constrainedFunction (causalObservationTraceDecisionSet w)
        (causalObservationTraceTargetAction w)
    _ = Nat.card A ^ (observationTreeNodeCount O n - n) := by
      rw [card_causalObservationDecisionPoint,
        card_causalObservationTraceDecisionSet]

/-- Real-valued indicator form of the exact per-realization count. -/
theorem sum_causalObservationPlan_traceIndicator {n : ℕ}
    (w : CausalFiniteTrace A O n) :
    ∑ σ : CausalObservationPlan A O n,
        causalPlanTraceIndicator σ.toCausalPlan w =
      (Nat.card A : ℝ) ^ (observationTreeNodeCount O n - n) := by
  classical
  unfold causalPlanTraceIndicator
  have hfilter :
      (Finset.univ.filter fun σ : CausalObservationPlan A O n =>
        CausalPlanAgreesTrace σ.toCausalPlan w).card =
      Nat.card { σ : CausalObservationPlan A O n //
        CausalPlanAgreesTrace σ.toCausalPlan w } := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [show (∑ σ : CausalObservationPlan A O n,
      if CausalPlanAgreesTrace σ.toCausalPlan w then (1 : ℝ) else 0) =
      ((Finset.univ.filter fun σ : CausalObservationPlan A O n =>
        CausalPlanAgreesTrace σ.toCausalPlan w).card : ℝ) by simp,
    hfilter, card_causalObservationPlan_agreesTrace]
  norm_cast

/-- Exact number of deterministic observation-only native interventions. -/
theorem card_causalObservationPlan (n : ℕ) :
    Nat.card (CausalObservationPlan A O n) =
      Nat.card A ^ observationTreeNodeCount O n := by
  induction n with
  | zero =>
      simp [CausalObservationPlan, observationTreeNodeCount]
  | succ n ih =>
      change Nat.card (A × (O → CausalObservationPlan A O n)) = _
      rw [Nat.card_prod, Nat.card_fun, ih]
      simp only [Nat.card_eq_fintype_card, observationTreeNodeCount]
      rw [pow_add, pow_one, ← pow_mul]
      congr 1
      rw [Nat.mul_comm]

/-- Probability that a recorded depth-`n` episode follows the action choices
of a deterministic full-history contingency plan. -/
noncomputable def causalPlanCoverage
    (π : CausalPolicy A O) (Qs : Θ → CausalResponse A O)
    {n : ℕ} (τ : CausalPlan A O n) (θ : Θ) : ℝ :=
  ∑ w : CausalFiniteTrace A O n,
    causalPlanTraceIndicator τ w * causalFiniteExperiment π Qs n θ w

/-- The full-trace definition of coverage is exactly the sum of the splicing
masses over all observation words. -/
theorem causalPlanCoverage_eq_sum_spliceMass
    (π : CausalPolicy A O) (Qs : Θ → CausalResponse A O)
    {n : ℕ} (τ : CausalPlan A O n) (θ : Θ) :
    causalPlanCoverage π Qs τ θ =
      ∑ o, causalSpliceMass π Qs τ θ o := by
  classical
  unfold causalPlanCoverage causalSpliceMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : CausalPlanAgreesTrace τ w
  · simp [causalPlanTraceIndicator, hw]
  · simp [causalPlanTraceIndicator, hw]

/-- Uniform behavior matches every deterministic intervention with probability
exactly `|A|⁻ⁿ`, simultaneously in every world. -/
theorem causalPlanCoverage_uniform
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {n : ℕ} (τ : CausalPlan A O n) (θ : Θ) :
    causalPlanCoverage (causalUniformPolicy A O) Qs τ θ =
      uniformMatchProb A n := by
  rw [causalPlanCoverage_eq_sum_spliceMass,
    sum_causalSpliceMass_uniform Qs hQ τ θ]
  rfl

/-- Uniform action propensities give the same probability to every prescribed
length-`n` action path. -/
theorem causalPolicyProb_uniform_ofFn
    {n : ℕ} (w : CausalFiniteTrace A O n) :
    causalPolicyProb (causalUniformPolicy A O) (List.ofFn w) =
      uniformMatchProb A n := by
  rw [causalPolicyProb_ofFn]
  simp [causalUniformPolicy, uniformMatchProb]

/-- Uniform behavior gives every full-history Kuhn plan the same weight. -/
theorem kuhnWeight_uniform (n : ℕ) (τ : CausalPlan A O n) :
    kuhnWeight (causalUniformPolicy A O) n τ =
      (Nat.card A : ℝ)⁻¹ ^ Nat.card (CausalDecisionPoint A O n) := by
  classical
  unfold kuhnWeight contingencyWeight causalUniformPolicy
  simp [Nat.card_eq_fintype_card]

/-- **Coverage conservation.**  Average the match probability of an arbitrary
valid behavior policy over independently and uniformly sampled contingency
plans.  The result is the deterministic constant `|A|⁻ⁿ`, independent of the
policy, world, and response law. -/
theorem sum_uniformKuhnWeight_mul_causalPlanCoverage
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (n : ℕ) (θ : Θ) :
    ∑ τ : CausalPlan A O n,
        kuhnWeight (causalUniformPolicy A O) n τ *
          causalPlanCoverage π Qs τ θ =
      uniformMatchProb A n := by
  classical
  unfold causalPlanCoverage
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ w : CausalFiniteTrace A O n,
        ∑ τ : CausalPlan A O n,
          kuhnWeight (causalUniformPolicy A O) n τ *
            (causalPlanTraceIndicator τ w *
              causalFiniteExperiment π Qs n θ w)) =
        ∑ w : CausalFiniteTrace A O n,
          (∑ τ : CausalPlan A O n,
            kuhnWeight (causalUniformPolicy A O) n τ *
              causalPlanTraceIndicator τ w) *
            causalFiniteExperiment π Qs n θ w := by
          apply Finset.sum_congr rfl
          intro w _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro τ _
          ring
    _ = ∑ w : CausalFiniteTrace A O n,
          uniformMatchProb A n * causalFiniteExperiment π Qs n θ w := by
          apply Finset.sum_congr rfl
          intro w _
          rw [sum_kuhnWeight_mul_traceIndicator
            (causalUniformPolicy A O) isCausalPolicy_uniform w,
            causalPolicyProb_uniform_ofFn w]
    _ = uniformMatchProb A n := by
          rw [← Finset.mul_sum,
            (causalFiniteExperiment_valid π hπ Qs hQ n θ).2, mul_one]

/-- Some deterministic contingency plan has coverage no greater than the
uniform benchmark.  This is the maximin upper bound, world by world. -/
theorem exists_causalPlanCoverage_le_uniform
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (n : ℕ) (θ : Θ) :
    ∃ τ : CausalPlan A O n,
      causalPlanCoverage π Qs τ θ ≤ uniformMatchProb A n := by
  classical
  by_contra h
  push Not at h
  have hpos : ∀ τ : CausalPlan A O n,
      0 < kuhnWeight (causalUniformPolicy A O) n τ := by
    intro τ
    unfold kuhnWeight contingencyWeight causalUniformPolicy
    exact Finset.prod_pos fun _ _ =>
      inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  have hlt :
      (∑ τ : CausalPlan A O n,
          kuhnWeight (causalUniformPolicy A O) n τ *
            uniformMatchProb A n) <
        ∑ τ : CausalPlan A O n,
          kuhnWeight (causalUniformPolicy A O) n τ *
            causalPlanCoverage π Qs τ θ := by
    apply Finset.sum_lt_sum
    · intro τ _
      exact mul_le_mul_of_nonneg_left (le_of_lt (h τ))
        (le_of_lt (hpos τ))
    · let τ : CausalPlan A O n := fun _ => Classical.choice inferInstance
      exact ⟨τ, Finset.mem_univ τ,
        mul_lt_mul_of_pos_left (h τ) (hpos τ)⟩
  rw [← Finset.sum_mul] at hlt
  have hsum :
      ∑ τ : CausalPlan A O n,
          kuhnWeight (causalUniformPolicy A O) n τ = 1 :=
    (kuhnWeight_isDist (causalUniformPolicy A O)
      isCausalPolicy_uniform n).2
  have hconserve :=
    sum_uniformKuhnWeight_mul_causalPlanCoverage π hπ Qs hQ n θ
  rw [hsum, one_mul, hconserve] at hlt
  exact (lt_irrefl _ hlt)

/-- Equality case behind prefix-coverage maximin: if every full-history plan
has coverage at least the uniform benchmark, then every one has exactly the
benchmark.  Strict improvement of even one positive-weight plan would violate
the weighted conservation identity. -/
theorem causalPlanCoverage_eq_uniform_of_all_ge
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (n : ℕ) (θ : Θ)
    (hall : ∀ τ : CausalPlan A O n,
      uniformMatchProb A n ≤ causalPlanCoverage π Qs τ θ)
    (τ : CausalPlan A O n) :
    causalPlanCoverage π Qs τ θ = uniformMatchProb A n := by
  apply le_antisymm ?_ (hall τ)
  by_contra hle
  have hstrict : uniformMatchProb A n < causalPlanCoverage π Qs τ θ :=
    lt_of_not_ge hle
  have hpos : ∀ ρ : CausalPlan A O n,
      0 < kuhnWeight (causalUniformPolicy A O) n ρ := by
    intro ρ
    unfold kuhnWeight contingencyWeight causalUniformPolicy
    exact Finset.prod_pos fun _ _ =>
      inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  have hlt :
      (∑ ρ : CausalPlan A O n,
          kuhnWeight (causalUniformPolicy A O) n ρ *
            uniformMatchProb A n) <
        ∑ ρ : CausalPlan A O n,
          kuhnWeight (causalUniformPolicy A O) n ρ *
            causalPlanCoverage π Qs ρ θ := by
    apply Finset.sum_lt_sum
    · intro ρ _
      exact mul_le_mul_of_nonneg_left (hall ρ) (le_of_lt (hpos ρ))
    · exact ⟨τ, Finset.mem_univ τ,
        mul_lt_mul_of_pos_left hstrict (hpos τ)⟩
  rw [← Finset.sum_mul] at hlt
  have hsum :
      ∑ ρ : CausalPlan A O n,
          kuhnWeight (causalUniformPolicy A O) n ρ = 1 :=
    (kuhnWeight_isDist (causalUniformPolicy A O)
      isCausalPolicy_uniform n).2
  have hconserve :=
    sum_uniformKuhnWeight_mul_causalPlanCoverage π hπ Qs hQ n θ
  rw [hsum, one_mul, hconserve] at hlt
  exact (lt_irrefl _ hlt)

/-- Coverage for the canonical observation-only plan is coverage for its
full-history embedding. -/
noncomputable def causalObservationPlanCoverage
    (π : CausalPolicy A O) (Qs : Θ → CausalResponse A O)
    {n : ℕ} (σ : CausalObservationPlan A O n) (θ : Θ) : ℝ :=
  causalPlanCoverage π Qs σ.toCausalPlan θ

/-- Canonicalizing a full-history plan to an observation-only plan preserves
its coverage exactly. -/
theorem causalObservationPlanCoverage_ofCausalPlan
    (π : CausalPolicy A O) (Qs : Θ → CausalResponse A O)
    {n : ℕ} (τ : CausalPlan A O n) (θ : Θ) :
    causalObservationPlanCoverage π Qs
        (CausalObservationPlan.ofCausalPlan τ) θ =
      causalPlanCoverage π Qs τ θ := by
  unfold causalObservationPlanCoverage
  rw [causalPlanCoverage_eq_sum_spliceMass,
    causalPlanCoverage_eq_sum_spliceMass]
  apply Finset.sum_congr rfl
  intro o _
  rw [causalSpliceMass_eq_reconstruction,
    causalSpliceMass_eq_reconstruction,
    CausalObservationPlan.trace_toCausalPlan_ofCausalPlan]

/-- **Literal unweighted coverage conservation.**  For every valid causal
policy and world, summing coverage over all observation-tree tests gives
exactly `|A|^(K_n-n)`.  This is the expectation of the preceding
per-realization count. -/
theorem sum_causalObservationPlanCoverage
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (n : ℕ) (θ : Θ) :
    ∑ σ : CausalObservationPlan A O n,
        causalObservationPlanCoverage π Qs σ θ =
      (Nat.card A : ℝ) ^ (observationTreeNodeCount O n - n) := by
  classical
  unfold causalObservationPlanCoverage causalPlanCoverage
  rw [Finset.sum_comm]
  calc
    (∑ w : CausalFiniteTrace A O n,
        ∑ σ : CausalObservationPlan A O n,
          causalPlanTraceIndicator σ.toCausalPlan w *
            causalFiniteExperiment π Qs n θ w) =
        ∑ w : CausalFiniteTrace A O n,
          (Nat.card A : ℝ) ^ (observationTreeNodeCount O n - n) *
            causalFiniteExperiment π Qs n θ w := by
      apply Finset.sum_congr rfl
      intro w _
      rw [← Finset.sum_mul, sum_causalObservationPlan_traceIndicator]
    _ = (Nat.card A : ℝ) ^ (observationTreeNodeCount O n - n) := by
      rw [← Finset.mul_sum,
        (causalFiniteExperiment_valid π hπ Qs hQ n θ).2, mul_one]

/-- Division-free form of literal coverage conservation:
`|A|^n * ∑_σ p_σ(Q) = |A|^K`. -/
theorem pow_mul_sum_causalObservationPlanCoverage
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (n : ℕ) (θ : Θ) :
    (Nat.card A : ℝ) ^ n *
        ∑ σ : CausalObservationPlan A O n,
          causalObservationPlanCoverage π Qs σ θ =
      (Nat.card A : ℝ) ^ observationTreeNodeCount O n := by
  rw [sum_causalObservationPlanCoverage π hπ Qs hQ n θ, ← pow_add]
  rw [Nat.add_sub_cancel' (depth_le_observationTreeNodeCount (O := O) n)]

/-- The maximin upper bound stated using the reader paper's literal
observation-only intervention trees. -/
theorem exists_causalObservationPlanCoverage_le_uniform
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (n : ℕ) (θ : Θ) :
    ∃ σ : CausalObservationPlan A O n,
      causalObservationPlanCoverage π Qs σ θ ≤ uniformMatchProb A n := by
  obtain ⟨τ, hτ⟩ :=
    exists_causalPlanCoverage_le_uniform π hπ Qs hQ n θ
  refine ⟨CausalObservationPlan.ofCausalPlan τ, ?_⟩
  exact (causalObservationPlanCoverage_ofCausalPlan π Qs τ θ).trans_le hτ

/-- Uniform behavior attains the canonical observation-tree benchmark for
every intervention and every world. -/
theorem causalObservationPlanCoverage_uniform
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {n : ℕ} (σ : CausalObservationPlan A O n) (θ : Θ) :
    causalObservationPlanCoverage (causalUniformPolicy A O) Qs σ θ =
      uniformMatchProb A n :=
  causalPlanCoverage_uniform Qs hQ σ.toCausalPlan θ

/-- Literal equality characterization for the reader paper's observation-only
tests.  The worst coverage reaches the uniform benchmark exactly when every
test has that same coverage. -/
theorem all_causalObservationPlanCoverage_ge_uniform_iff_eq
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (n : ℕ) (θ : Θ) :
    (∀ σ : CausalObservationPlan A O n,
        uniformMatchProb A n ≤ causalObservationPlanCoverage π Qs σ θ) ↔
      ∀ σ : CausalObservationPlan A O n,
        causalObservationPlanCoverage π Qs σ θ = uniformMatchProb A n := by
  constructor
  · intro hall σ
    apply causalPlanCoverage_eq_uniform_of_all_ge π hπ Qs hQ n θ
    intro τ
    simpa only [causalObservationPlanCoverage_ofCausalPlan] using
      hall (CausalObservationPlan.ofCausalPlan τ)
  · intro hall σ
    exact (hall σ).ge

end IdExp
