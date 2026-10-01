import Formal.CausalUniversality

/-!
# Finite controlled-prefix behaviors and plan evaluation

Consistent finite families, evaluation under adaptive plans, and finite mixing
and gluing. These are the shared semantics used by normalized causal behaviors
and coherent reconstruction; binary reconstruction is an application.
-/

namespace IdExp

open Finset Set

variable {A O Θ X : Type*} [Fintype A] [Fintype O] [Fintype X]

/-! ## Consistent families -/

/-- The paper's consistent family of depth `n`: a nonnegative probability
assignment on action--observation histories with `p [] = 1` such that at
every history of length below `n` and every proposed action the
next-observation masses sum back to the history mass.  Histories are the
repo's chronological lists, growing by `h ++ [(a, o)]`. -/
structure ConsistentFamily (A O : Type*) [Fintype O] (n : ℕ) where
  p : CausalHistory A O → ℝ
  root : p [] = 1
  nonneg : ∀ h, 0 ≤ p h
  consistent : ∀ (h : CausalHistory A O) (a : A), h.length < n →
    ∑ o, p (h ++ [(a, o)]) = p h

/-- A child event is contained in its parent in every consistent family. -/
theorem ConsistentFamily.child_le {n : ℕ} (f : ConsistentFamily A O n)
    (h : CausalHistory A O) (a : A) (o : O) (hh : h.length < n) :
    f.p (h ++ [(a, o)]) ≤ f.p h := by
  rw [← f.consistent h a hh]
  exact Finset.single_le_sum (fun y _ => f.nonneg (h ++ [(a, y)])) (Finset.mem_univ o)

/-- Every in-horizon prefix probability of a consistent family is at most one. -/
theorem ConsistentFamily.p_le_one {n : ℕ} (f : ConsistentFamily A O n)
    (h : CausalHistory A O) (hh : h.length ≤ n) : f.p h ≤ 1 := by
  induction h using List.reverseRecOn with
  | nil => rw [f.root]
  | append_singleton h ao ih =>
      have hlt : h.length < n := by simpa using hh
      exact (f.child_le h ao.1 ao.2 hlt).trans (ih (by omega))

/-- The law on observation words obtained by following the deterministic
plan `τ` through a consistent family: the family's probability of the full
history the plan reconstructs from the observation word. -/
noncomputable def familyPlanLaw (n : ℕ) (τ : CausalPlan A O n)
    (f : ConsistentFamily A O n) : CausalObservationTrace O n → ℝ :=
  fun w => f.p (List.ofFn (causalTraceOfObservations τ w))

theorem familyPlanLaw_nonneg (n : ℕ) (τ : CausalPlan A O n)
    (f : ConsistentFamily A O n) (w : CausalObservationTrace O n) :
    0 ≤ familyPlanLaw n τ f w :=
  f.nonneg _

/-! ## Plan-tree recursion -/

/-- The bounded decision point reached after one more action--observation
pair. -/
def CausalDecisionPoint.cons {n : ℕ} (ao : A × O) (x : CausalDecisionPoint A O n) :
    CausalDecisionPoint A O (n + 1) :=
  ⟨x.1.succ, Fin.cons (α := fun _ => A × O) ao x.2⟩

/-- The root action of a depth-`(n+1)` plan: its decision at the empty
history. -/
noncomputable def CausalPlan.root {n : ℕ} (τ : CausalPlan A O (n + 1)) : A :=
  τ (causalDecisionPointOfHistory (n + 1) [] (Nat.succ_pos n))

/-- The depth-`n` continuation of a plan after a first action--observation
pair (any pair, on- or off-path). -/
def CausalPlan.afterFull {n : ℕ} (τ : CausalPlan A O (n + 1)) (ao : A × O) :
    CausalPlan A O n :=
  fun x => τ (CausalDecisionPoint.cons ao x)

/-- The depth-`n` continuation of a plan after its root action produced
observation `o`. -/
noncomputable def CausalPlan.after {n : ℕ} (τ : CausalPlan A O (n + 1)) (o : O) :
    CausalPlan A O n :=
  τ.afterFull (τ.root, o)

/-- Assemble a depth-`(n+1)` plan from a root action and a continuation plan
after every action--observation pair. -/
def CausalPlan.consFull {n : ℕ} (a : A) (σ : A × O → CausalPlan A O n) :
    CausalPlan A O (n + 1) :=
  fun x => match x with
    | ⟨⟨0, _⟩, _⟩ => a
    | ⟨⟨k + 1, hk⟩, h⟩ => σ (h 0) ⟨⟨k, Nat.lt_of_succ_lt_succ hk⟩, Fin.tail h⟩

/-- Assemble a depth-`(n+1)` plan from a root action and one continuation
plan per observation of that action (the paper's tree recursion). -/
def CausalPlan.cons {n : ℕ} (a : A) (σ : O → CausalPlan A O n) :
    CausalPlan A O (n + 1) :=
  CausalPlan.consFull a (fun ao => σ ao.2)

@[simp] theorem CausalPlan.consFull_root {n : ℕ} (a : A)
    (σ : A × O → CausalPlan A O n) : (CausalPlan.consFull a σ).root = a := rfl

@[simp] theorem CausalPlan.consFull_afterFull {n : ℕ} (a : A)
    (σ : A × O → CausalPlan A O n) (ao : A × O) :
    (CausalPlan.consFull a σ).afterFull ao = σ ao := by
  funext x
  obtain ⟨⟨k, hk⟩, h⟩ := x
  rfl

@[simp] theorem CausalPlan.cons_root {n : ℕ} (a : A) (σ : O → CausalPlan A O n) :
    (CausalPlan.cons a σ).root = a := rfl

@[simp] theorem CausalPlan.cons_after {n : ℕ} (a : A) (σ : O → CausalPlan A O n)
    (o : O) : (CausalPlan.cons a σ).after o = σ o := by
  unfold CausalPlan.after CausalPlan.cons
  rw [CausalPlan.consFull_afterFull]

/-- Exact functional decomposition of a plan into its root action and its
continuations after every action--observation pair. -/
theorem CausalPlan.consFull_root_afterFull {n : ℕ} (τ : CausalPlan A O (n + 1)) :
    CausalPlan.consFull τ.root τ.afterFull = τ := by
  funext x
  obtain ⟨⟨k, hk⟩, h⟩ := x
  cases k with
  | zero =>
      show τ (causalDecisionPointOfHistory (n + 1) [] (Nat.succ_pos n)) = τ _
      unfold causalDecisionPointOfHistory
      congr 1
      refine Sigma.ext ?_ ?_
      · rfl
      · exact heq_of_eq (funext fun i => Fin.elim0 i)
  | succ k =>
      show τ (CausalDecisionPoint.cons (h 0) ⟨⟨k, _⟩, Fin.tail h⟩) = τ _
      congr 1
      unfold CausalDecisionPoint.cons
      refine Sigma.ext ?_ ?_
      · rfl
      · exact heq_of_eq (Fin.cons_self_tail h)

/-! ## Decision points along a trace, one step at a time -/

theorem causalDecisionPointOfHistory_congr {n : ℕ} {h h' : CausalHistory A O}
    (e : h = h') (hh : h.length < n) :
    causalDecisionPointOfHistory n h hh =
      causalDecisionPointOfHistory n h' (e ▸ hh) := by
  subst e
  rfl

theorem causalDecisionPointOfHistory_cons {n : ℕ} (ao : A × O)
    (l : CausalHistory A O) (hh : (ao :: l).length < n + 1) :
    causalDecisionPointOfHistory (n + 1) (ao :: l) hh =
      CausalDecisionPoint.cons ao
        (causalDecisionPointOfHistory n l (Nat.lt_of_succ_lt_succ hh)) := by
  unfold causalDecisionPointOfHistory CausalDecisionPoint.cons
  refine Sigma.ext ?_ ?_
  · rfl
  · refine heq_of_eq ?_
    funext j
    refine Fin.cases ?_ ?_ j
    · rfl
    · intro j
      rfl

theorem causalTracePrefix_zero {n : ℕ} (w : CausalFiniteTrace A O (n + 1)) :
    causalTracePrefix w 0 = [] := by
  apply List.eq_nil_of_length_eq_zero
  simp [causalTracePrefix]

theorem causalTracePrefix_succ {n : ℕ} (w : CausalFiniteTrace A O (n + 1))
    (i : Fin n) :
    causalTracePrefix w i.succ = w 0 :: causalTracePrefix (Fin.tail w) i := by
  unfold causalTracePrefix
  rw [List.ofFn_succ]
  rfl

theorem causalTraceDecisionPoint_zero {n : ℕ} (w : CausalFiniteTrace A O (n + 1)) :
    causalTraceDecisionPoint w 0 =
      causalDecisionPointOfHistory (n + 1) [] (Nat.succ_pos n) := by
  unfold causalTraceDecisionPoint
  rw [causalDecisionPointOfHistory_congr (causalTracePrefix_zero w)]

theorem causalTraceDecisionPoint_succ {n : ℕ} (w : CausalFiniteTrace A O (n + 1))
    (i : Fin n) :
    causalTraceDecisionPoint w i.succ =
      CausalDecisionPoint.cons (w 0) (causalTraceDecisionPoint (Fin.tail w) i) := by
  unfold causalTraceDecisionPoint
  rw [causalDecisionPointOfHistory_congr (causalTracePrefix_succ w i),
    causalDecisionPointOfHistory_cons]

/-- A plan's action at the root decision point of any depth-`(n+1)` trace is
its root action. -/
theorem CausalPlan.apply_traceDecisionPoint_zero {n : ℕ} (τ : CausalPlan A O (n + 1))
    (w : CausalFiniteTrace A O (n + 1)) :
    τ (causalTraceDecisionPoint w 0) = τ.root := by
  rw [causalTraceDecisionPoint_zero]
  rfl

theorem CausalPlan.apply_traceDecisionPoint_succ {n : ℕ} (τ : CausalPlan A O (n + 1))
    (w : CausalFiniteTrace A O (n + 1)) (i : Fin n) :
    τ (causalTraceDecisionPoint w i.succ) =
      τ.afterFull (w 0) (causalTraceDecisionPoint (Fin.tail w) i) := by
  rw [causalTraceDecisionPoint_succ]
  rfl

/-- A depth-`(n+1)` plan agrees with a trace iff the trace's first action is
the root action and the continuation plan after the first pair agrees with
the tail. -/
theorem causalPlanAgreesTrace_succ_iff {n : ℕ} (τ : CausalPlan A O (n + 1))
    (w : CausalFiniteTrace A O (n + 1)) :
    CausalPlanAgreesTrace τ w ↔
      τ.root = (w 0).1 ∧ CausalPlanAgreesTrace (τ.afterFull (w 0)) (Fin.tail w) := by
  unfold CausalPlanAgreesTrace
  rw [Fin.forall_fin_succ, CausalPlan.apply_traceDecisionPoint_zero τ w]
  simp_rw [CausalPlan.apply_traceDecisionPoint_succ τ w]
  rfl

/-! ## Reconstruction of observation words, one step at a time -/

/-- The plan's reconstruction of `o :: w` is its root action paired with `o`,
followed by the continuation plan's reconstruction of `w`. -/
theorem causalTraceOfObservations_cons {n : ℕ} (τ : CausalPlan A O (n + 1))
    (o : O) (w : CausalObservationTrace O n) :
    causalTraceOfObservations τ (Fin.cons o w) =
      Fin.cons (α := fun _ => A × O) (τ.root, o)
        (causalTraceOfObservations (τ.after o) w) := by
  symm
  rw [eq_causalTraceOfObservations_iff]
  constructor
  · rw [causalPlanAgreesTrace_succ_iff]
    refine ⟨rfl, ?_⟩
    rw [Fin.cons_zero, Fin.tail_cons]
    exact causalPlanAgreesTrace_traceOfObservations (τ.after o) w
  · funext k
    refine Fin.cases ?_ ?_ k
    · rfl
    · intro k
      show (causalTraceOfObservations (τ.after o) w k).2 = w k
      exact congrFun (causalTraceObservations_traceOfObservations (τ.after o) w) k

theorem causalTraceOfObservations_succ {n : ℕ} (τ : CausalPlan A O (n + 1))
    (w : CausalObservationTrace O (n + 1)) :
    causalTraceOfObservations τ w =
      Fin.cons (α := fun _ => A × O) (τ.root, w 0)
        (causalTraceOfObservations (τ.after (w 0)) (Fin.tail w)) := by
  conv_lhs => rw [← Fin.cons_self_tail w]
  exact causalTraceOfObservations_cons τ (w 0) (Fin.tail w)

/-- Reassembling a plan from its root action and its on-path continuations
changes nothing that is defined through reconstruction. -/
theorem causalTraceOfObservations_cons_root_after {n : ℕ}
    (τ : CausalPlan A O (n + 1)) (w : CausalObservationTrace O (n + 1)) :
    causalTraceOfObservations (CausalPlan.cons τ.root τ.after) w =
      causalTraceOfObservations τ w := by
  rw [causalTraceOfObservations_succ, causalTraceOfObservations_succ τ,
    CausalPlan.cons_root, CausalPlan.cons_after]

/-! ## Shifting a response kernel past one action--observation pair -/

/-- The response kernel seen after one fixed first pair. -/
def CausalResponse.shift (Q : CausalResponse A O) (ao : A × O) : CausalResponse A O :=
  fun h => Q (ao :: h)

theorem IsCausalResponse.shift {Q : CausalResponse A O} (hQ : IsCausalResponse Q)
    (ao : A × O) : IsCausalResponse (Q.shift ao) :=
  fun h a => hQ (ao :: h) a

theorem causalResponseProbFrom_cons_shift (Q : CausalResponse A O) (ao : A × O)
    (pre rest : CausalHistory A O) :
    causalResponseProbFrom Q (ao :: pre) rest =
      causalResponseProbFrom (Q.shift ao) pre rest := by
  induction rest generalizing pre with
  | nil => rfl
  | cons bo rest ih =>
      simp only [causalResponseProbFrom, List.cons_append]
      rw [ih]
      rfl

theorem causalResponseProb_cons (Q : CausalResponse A O) (ao : A × O)
    (l : CausalHistory A O) :
    causalResponseProb Q (ao :: l) =
      Q [] ao.1 ao.2 * causalResponseProb (Q.shift ao) l := by
  unfold causalResponseProb
  simp only [causalResponseProbFrom, List.nil_append]
  rw [causalResponseProbFrom_cons_shift]

/-! ## The plan experiment through reconstruction -/

/-- The plan's observation experiment is the controlled likelihood of the
reconstructed history: the deterministic policy factor is one on-path. -/
theorem causalPlanObservationExperiment_eq_responseProb [Nonempty A]
    (n : ℕ) (τ : CausalPlan A O n) (Qs : Θ → CausalResponse A O)
    (θ : Θ) (w : CausalObservationTrace O n) :
    causalPlanObservationExperiment n τ Qs θ w =
      causalResponseProb (Qs θ) (List.ofFn (causalTraceOfObservations τ w)) := by
  rw [causalPlanObservationExperiment_eq_reconstruction]
  unfold causalFiniteExperiment
  rw [causalTraceProb_factor, causalPolicyProb_plan_eq_indicator]
  simp [causalPlanTraceIndicator, causalPlanAgreesTrace_traceOfObservations]

/-- At depth zero the unique observation word has probability one. -/
theorem causalPlanObservationExperiment_zero [Nonempty A]
    (τ : CausalPlan A O 0) (Qs : Θ → CausalResponse A O)
    (θ : Θ) (w : CausalObservationTrace O 0) :
    causalPlanObservationExperiment 0 τ Qs θ w = 1 := by
  rw [causalPlanObservationExperiment_eq_responseProb]
  rw [List.ofFn_zero]
  rfl

/-- **Depth recursion of the plan experiment.**  The probability of `o :: w`
under a depth-`(n+1)` plan is the root response probability of `o` times the
probability of `w` under the continuation plan in the shifted class. -/
theorem causalPlanObservationExperiment_succ [Nonempty A] {n : ℕ}
    (τ : CausalPlan A O (n + 1)) (Qs : Θ → CausalResponse A O)
    (θ : Θ) (o : O) (w : CausalObservationTrace O n) :
    causalPlanObservationExperiment (n + 1) τ Qs θ (Fin.cons o w) =
      Qs θ [] τ.root o *
        causalPlanObservationExperiment n (τ.after o)
          (fun θ => (Qs θ).shift (τ.root, o)) θ w := by
  rw [causalPlanObservationExperiment_eq_responseProb,
    causalPlanObservationExperiment_eq_responseProb,
    causalTraceOfObservations_cons, List.ofFn_cons, causalResponseProb_cons]

/-- The recursion at an explicitly assembled plan. -/
theorem causalPlanObservationExperiment_cons [Nonempty A] {n : ℕ}
    (a : A) (σ : O → CausalPlan A O n) (Qs : Θ → CausalResponse A O)
    (θ : Θ) (o : O) (w : CausalObservationTrace O n) :
    causalPlanObservationExperiment (n + 1) (CausalPlan.cons a σ) Qs θ (Fin.cons o w) =
      Qs θ [] a o *
        causalPlanObservationExperiment n (σ o) (fun θ => (Qs θ).shift (a, o)) θ w := by
  rw [causalPlanObservationExperiment_succ, CausalPlan.cons_root, CausalPlan.cons_after]

/-- The reassembled plan induces the same observation experiment. -/
theorem causalPlanObservationExperiment_cons_root_after [Nonempty A] {n : ℕ}
    (τ : CausalPlan A O (n + 1)) (Qs : Θ → CausalResponse A O) :
    causalPlanObservationExperiment (n + 1) (CausalPlan.cons τ.root τ.after) Qs =
      causalPlanObservationExperiment (n + 1) τ Qs := by
  funext θ w
  rw [causalPlanObservationExperiment_eq_responseProb,
    causalPlanObservationExperiment_eq_responseProb,
    causalTraceOfObservations_cons_root_after]

/-! ## Family laws along the plan tree -/

theorem familyPlanLaw_zero (τ : CausalPlan A O 0) (f : ConsistentFamily A O 0)
    (w : CausalObservationTrace O 0) : familyPlanLaw 0 τ f w = 1 := by
  unfold familyPlanLaw
  rw [List.ofFn_zero]
  exact f.root

theorem familyPlanLaw_succ {n : ℕ} (τ : CausalPlan A O (n + 1))
    (f : ConsistentFamily A O (n + 1)) (o : O) (w : CausalObservationTrace O n) :
    familyPlanLaw (n + 1) τ f (Fin.cons o w) =
      f.p ((τ.root, o) :: List.ofFn (causalTraceOfObservations (τ.after o) w)) := by
  unfold familyPlanLaw
  rw [causalTraceOfObservations_cons, List.ofFn_cons]

theorem familyPlanLaw_cons_root_after {n : ℕ} (τ : CausalPlan A O (n + 1))
    (f : ConsistentFamily A O (n + 1)) :
    familyPlanLaw (n + 1) (CausalPlan.cons τ.root τ.after) f =
      familyPlanLaw (n + 1) τ f := by
  funext w
  unfold familyPlanLaw
  rw [causalTraceOfObservations_cons_root_after]

/-- Summing a consistent family over all depth-`n` continuations that a plan
produces from a history recovers the history mass, whenever the extended
histories stay within the family's depth. -/
theorem ConsistentFamily.sum_append_traceOfObservations {N : ℕ}
    (f : ConsistentFamily A O N) (n : ℕ) :
    ∀ (h : CausalHistory A O), h.length + n ≤ N → ∀ τ : CausalPlan A O n,
      ∑ w : CausalObservationTrace O n,
        f.p (h ++ List.ofFn (causalTraceOfObservations τ w)) = f.p h := by
  induction n with
  | zero =>
      intro h _ τ
      rw [Fintype.sum_unique]
      simp [List.ofFn_zero]
  | succ n ih =>
      intro h hlen τ
      rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => O)).sum_comp, Fintype.sum_prod_type]
      have hcons (o : O) (w : CausalObservationTrace O n) :
          (Fin.consEquiv (fun _ : Fin (n + 1) => O)) (o, w) = Fin.cons o w := by
        funext i
        exact Fin.consEquiv_apply _ _ i
      calc
        ∑ o : O, ∑ w : CausalObservationTrace O n,
            f.p (h ++ List.ofFn (causalTraceOfObservations τ
              ((Fin.consEquiv (fun _ : Fin (n + 1) => O)) (o, w)))) =
            ∑ o : O, ∑ w : CausalObservationTrace O n,
              f.p ((h ++ [(τ.root, o)]) ++
                List.ofFn (causalTraceOfObservations (τ.after o) w)) := by
          apply Finset.sum_congr rfl
          intro o _
          apply Finset.sum_congr rfl
          intro w _
          rw [hcons, causalTraceOfObservations_cons, List.ofFn_cons,
            List.append_assoc, List.singleton_append]
        _ = ∑ o : O, f.p (h ++ [(τ.root, o)]) := by
          apply Finset.sum_congr rfl
          intro o _
          refine ih (h ++ [(τ.root, o)]) ?_ (τ.after o)
          simp only [List.length_append, List.length_singleton]
          omega
        _ = f.p h := f.consistent h τ.root (by omega)

/-- Following a plan through a consistent family gives a probability vector
on observation words. -/
theorem familyPlanLaw_sum (n : ℕ) (τ : CausalPlan A O n) (f : ConsistentFamily A O n) :
    ∑ w, familyPlanLaw n τ f w = 1 := by
  have h := f.sum_append_traceOfObservations n [] (by simp) τ
  simp only [List.nil_append] at h
  unfold familyPlanLaw
  rw [h, f.root]

theorem familyPlanLaw_isDist (n : ℕ) (τ : CausalPlan A O n)
    (f : ConsistentFamily A O n) : IsDist (familyPlanLaw n τ f) :=
  ⟨familyPlanLaw_nonneg n τ f, familyPlanLaw_sum n τ f⟩

theorem familyPlanLaw_mem_stdSimplex (n : ℕ) (τ : CausalPlan A O n)
    (f : ConsistentFamily A O n) :
    familyPlanLaw n τ f ∈ stdSimplex ℝ (CausalObservationTrace O n) :=
  ⟨familyPlanLaw_nonneg n τ f, familyPlanLaw_sum n τ f⟩

/-- One consistent family per acquired signal is a stochastic decoder for
every plan. -/
theorem familyPlanLaw_mem_stochasticRules (n : ℕ) (τ : CausalPlan A O n)
    (f : X → ConsistentFamily A O n) :
    (fun x => familyPlanLaw n τ (f x)) ∈
      stochasticRules X (CausalObservationTrace O n) :=
  fun x _ => familyPlanLaw_mem_stdSimplex n τ (f x)

/-! ## Constructions of consistent families -/

/-- Every valid causal response kernel is a consistent family at every depth:
its controlled history likelihoods. -/
noncomputable def ConsistentFamily.ofResponse (Q : CausalResponse A O)
    (hQ : IsCausalResponse Q) (n : ℕ) : ConsistentFamily A O n where
  p := causalResponseProb Q
  root := rfl
  nonneg := fun h => causalResponseProbFrom_nonneg Q hQ [] h
  consistent := by
    intro h a _
    simp_rw [causalResponseProb_append_singleton]
    rw [← Finset.mul_sum, (hQ h a).2, mul_one]

/-- Following a plan through a world's own kernel reproduces that world's
plan experiment. -/
theorem familyPlanLaw_ofResponse [Nonempty A] (n : ℕ) (τ : CausalPlan A O n)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ)) (θ : Θ) :
    familyPlanLaw n τ (ConsistentFamily.ofResponse (Qs θ) (hQ θ) n) =
      causalPlanObservationExperiment n τ Qs θ := by
  funext w
  rw [causalPlanObservationExperiment_eq_responseProb]
  rfl

/-- A stochastic mixture of consistent families is a consistent family. -/
noncomputable def ConsistentFamily.mix {J : Type*} [Fintype J] {n : ℕ}
    (c : J → ℝ) (hc : IsDist c) (g : J → ConsistentFamily A O n) :
    ConsistentFamily A O n where
  p := fun h => ∑ j, c j * (g j).p h
  root := by simp [(g _).root, hc.2]
  nonneg := fun h => Finset.sum_nonneg fun j _ => mul_nonneg (hc.1 j) ((g j).nonneg h)
  consistent := by
    intro h a hh
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.mul_sum, (g j).consistent h a hh]

theorem familyPlanLaw_mix {J : Type*} [Fintype J] {n : ℕ}
    (c : J → ℝ) (hc : IsDist c) (g : J → ConsistentFamily A O n)
    (τ : CausalPlan A O n) (w : CausalObservationTrace O n) :
    familyPlanLaw n τ (ConsistentFamily.mix c hc g) w =
      ∑ j, c j * familyPlanLaw n τ (g j) w := rfl

/-- Root allocation `m a o` followed by a continuation family after every
first pair: the history function of `ConsistentFamily.glue`. -/
noncomputable def ConsistentFamily.glueFun {n : ℕ} (m : A → O → ℝ)
    (g : A → O → ConsistentFamily A O n) : CausalHistory A O → ℝ
  | [] => 1
  | ao :: h => m ao.1 ao.2 * (g ao.1 ao.2).p h

@[simp] theorem ConsistentFamily.glueFun_nil {n : ℕ} (m : A → O → ℝ)
    (g : A → O → ConsistentFamily A O n) :
    ConsistentFamily.glueFun m g [] = 1 := rfl

@[simp] theorem ConsistentFamily.glueFun_cons {n : ℕ} (m : A → O → ℝ)
    (g : A → O → ConsistentFamily A O n) (ao : A × O) (h : CausalHistory A O) :
    ConsistentFamily.glueFun m g (ao :: h) = m ao.1 ao.2 * (g ao.1 ao.2).p h := rfl

/-- Glue a next-observation law for every root action with a depth-`n`
family after every first pair into a depth-`(n+1)` family. -/
noncomputable def ConsistentFamily.glue {n : ℕ} (m : A → O → ℝ) (hm : ∀ a, IsDist (m a))
    (g : A → O → ConsistentFamily A O n) : ConsistentFamily A O (n + 1) where
  p := ConsistentFamily.glueFun m g
  root := rfl
  nonneg := by
    intro h
    cases h with
    | nil => exact zero_le_one
    | cons ao h => exact mul_nonneg ((hm ao.1).1 ao.2) ((g ao.1 ao.2).nonneg h)
  consistent := by
    intro h a hh
    cases h with
    | nil =>
        simp only [List.nil_append, ConsistentFamily.glueFun_cons,
          ConsistentFamily.glueFun_nil, (g a _).root, mul_one]
        exact (hm a).2
    | cons ao h =>
        simp only [List.cons_append, ConsistentFamily.glueFun_cons]
        rw [← Finset.mul_sum, (g ao.1 ao.2).consistent h a (by simpa using hh)]

theorem ConsistentFamily.glue_p_nil {n : ℕ} (m : A → O → ℝ) (hm : ∀ a, IsDist (m a))
    (g : A → O → ConsistentFamily A O n) :
    (ConsistentFamily.glue m hm g).p [] = 1 := rfl

theorem ConsistentFamily.glue_p_cons {n : ℕ} (m : A → O → ℝ) (hm : ∀ a, IsDist (m a))
    (g : A → O → ConsistentFamily A O n) (ao : A × O) (h : CausalHistory A O) :
    (ConsistentFamily.glue m hm g).p (ao :: h) = m ao.1 ao.2 * (g ao.1 ao.2).p h := rfl

/-- The plan law of a glued family factors through the root. -/
theorem familyPlanLaw_glue {n : ℕ} (m : A → O → ℝ) (hm : ∀ a, IsDist (m a))
    (g : A → O → ConsistentFamily A O n) (τ : CausalPlan A O (n + 1))
    (o : O) (w : CausalObservationTrace O n) :
    familyPlanLaw (n + 1) τ (ConsistentFamily.glue m hm g) (Fin.cons o w) =
      m τ.root o * familyPlanLaw n (τ.after o) (g τ.root o) w := by
  rw [familyPlanLaw_succ]
  rfl

/-- Weighted glue: after every first pair a nonnegative combination of
depth-`n` families, with the root weights of every action summing to one.
This is the form produced by the quantitative gluing step, where the
continuation weights come from a decoder and need no normalization. -/
noncomputable def ConsistentFamily.glueMixFun {J : Type*} [Fintype J] {n : ℕ}
    (c : A → O → J → ℝ) (g : A → O → J → ConsistentFamily A O n) :
    CausalHistory A O → ℝ
  | [] => 1
  | ao :: h => ∑ j, c ao.1 ao.2 j * (g ao.1 ao.2 j).p h

noncomputable def ConsistentFamily.glueMix {J : Type*} [Fintype J] {n : ℕ}
    (c : A → O → J → ℝ) (hc0 : ∀ a o j, 0 ≤ c a o j)
    (hc1 : ∀ a, ∑ o, ∑ j, c a o j = 1)
    (g : A → O → J → ConsistentFamily A O n) : ConsistentFamily A O (n + 1) where
  p := ConsistentFamily.glueMixFun c g
  root := rfl
  nonneg := by
    intro h
    cases h with
    | nil => exact zero_le_one
    | cons ao h =>
        exact Finset.sum_nonneg fun j _ =>
          mul_nonneg (hc0 ao.1 ao.2 j) ((g ao.1 ao.2 j).nonneg h)
  consistent := by
    intro h a hh
    cases h with
    | nil =>
        simp only [List.nil_append, ConsistentFamily.glueMixFun, (g a _ _).root, mul_one]
        exact hc1 a
    | cons ao h =>
        simp only [List.cons_append, ConsistentFamily.glueMixFun]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.mul_sum, (g ao.1 ao.2 j).consistent h a (by simpa using hh)]

theorem ConsistentFamily.glueMix_p_cons {J : Type*} [Fintype J] {n : ℕ}
    (c : A → O → J → ℝ) (hc0 : ∀ a o j, 0 ≤ c a o j)
    (hc1 : ∀ a, ∑ o, ∑ j, c a o j = 1)
    (g : A → O → J → ConsistentFamily A O n) (ao : A × O) (h : CausalHistory A O) :
    (ConsistentFamily.glueMix c hc0 hc1 g).p (ao :: h) =
      ∑ j, c ao.1 ao.2 j * (g ao.1 ao.2 j).p h := rfl

theorem familyPlanLaw_glueMix {J : Type*} [Fintype J] {n : ℕ}
    (c : A → O → J → ℝ) (hc0 : ∀ a o j, 0 ≤ c a o j)
    (hc1 : ∀ a, ∑ o, ∑ j, c a o j = 1)
    (g : A → O → J → ConsistentFamily A O n) (τ : CausalPlan A O (n + 1))
    (o : O) (w : CausalObservationTrace O n) :
    familyPlanLaw (n + 1) τ (ConsistentFamily.glueMix c hc0 hc1 g) (Fin.cons o w) =
      ∑ j, c τ.root o j * familyPlanLaw n (τ.after o) (g τ.root o j) w := by
  rw [familyPlanLaw_succ]
  rfl

end IdExp
