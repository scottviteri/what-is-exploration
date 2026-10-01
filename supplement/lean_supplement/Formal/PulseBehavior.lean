import Formal.WaitingQueryNativeAudit

/-!
# Pulse worlds in which querying preserves the subsequent stream

Unlike `waitingQueryBehavior`, a root query does not suppress later pulses.
All statements concern the full countable class and literal collected logs.
`false` is WAIT, `true` is QUERY; `none` is the no-pulse world.
-/

namespace IdExp

open Finset Set

/-- Only the root action can change an observation. -/
def pulseOutput (θ : WaitingQueryWorld) (h : CausalHistory Bool Bool) (a : Bool) : Bool :=
  if h = [] then a && θ.isSome else waitingQueryBit θ h.length

noncomputable def pulseBehavior (θ : WaitingQueryWorld) : CausalBehavior Bool Bool :=
  CausalBehavior.ofResponse (detResponse (pulseOutput θ))
    (isCausalResponse_detResponse _)

/-- Take the specified root action, then wait. -/
def pulseAction (b : Bool) (h : CausalHistory Bool Bool) : Bool :=
  if h = [] then b else false

noncomputable def pulsePolicy (b : Bool) : ValidCausalPolicy Bool Bool :=
  validDetPolicy (pulseAction b)

/-- The literal trace, retaining the initial action as well as its answer. -/
def pulseTrace (b : Bool) (t : ℕ) (θ : WaitingQueryWorld) : CausalFiniteTrace Bool Bool t :=
  fun i => (if i.val = 0 then b else false,
    if i.val = 0 then b && θ.isSome else waitingQueryBit θ i.val)

@[simp] theorem pulseTrace_wait (t : ℕ) (θ : WaitingQueryWorld) :
    pulseTrace false t θ = waitingQueryTrace t θ := by
  funext i
  by_cases hi : i.val = 0
  · cases θ <;> simp [pulseTrace, waitingQueryTrace, waitingQueryBit, hi]
  · simp [pulseTrace, waitingQueryTrace, hi]

/-- Deterministic execution really produces the displayed trace. -/
theorem pulse_detTraceList (b : Bool) (t : ℕ) (θ : WaitingQueryWorld) :
    detTraceList (pulseAction b) (pulseOutput θ) t = List.ofFn (pulseTrace b t θ) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [detTraceList_succ, ih, List.ofFn_succ']
    have hlen : (List.ofFn (pulseTrace b t θ)).length = t := List.length_ofFn
    have hempty : List.ofFn (pulseTrace b t θ) = [] ↔ t = 0 := by
      rw [← List.length_eq_zero_iff, hlen]
    simp only [pulseAction, pulseOutput, hempty, hlen, pulseTrace, List.concat_eq_append]
    by_cases ht : t = 0
    · simp [ht]
    · simp only [Fin.val_castSucc, Fin.val_last, if_neg ht]
      rfl

theorem pulse_detTraceFin (b : Bool) (t : ℕ) (θ : WaitingQueryWorld) :
    detTraceFin (pulseAction b) (pulseOutput θ) t = pulseTrace b t θ := by
  apply List.ofFn_injective
  rw [ofFn_detTraceFin, pulse_detTraceList]

noncomputable def pulseExperiment (b : Bool) (t : ℕ) :
    FiniteExperiment WaitingQueryWorld (CausalFiniteTrace Bool Bool t) :=
  causalBehaviorFiniteExperiment (pulsePolicy b).1 pulseBehavior t

theorem pulseExperiment_eq_dirac (b : Bool) (t : ℕ) :
    pulseExperiment b t = diracExp (pulseTrace b t) := by
  change causalBehaviorFiniteExperiment (detPolicy (pulseAction b))
    (fun θ => CausalBehavior.ofResponse (detResponse (pulseOutput θ))
      (isCausalResponse_detResponse _)) t = _
  rw [causalBehaviorFiniteExperiment_ofResponse, causalFiniteExperiment_det]
  simp_rw [pulse_detTraceFin]

theorem pulseExperiment_valid (b : Bool) (t : ℕ) :
    IsFiniteExperiment (pulseExperiment b t) := by
  rw [pulseExperiment_eq_dirac]
  exact diracExp_valid _

theorem pulseExperiment_wait (t : ℕ) : pulseExperiment false t = waitingQueryExperiment t := by
  rw [pulseExperiment_eq_dirac, waitingQueryExperiment_eq_dirac]
  congr 1
  funext θ
  exact pulseTrace_wait t θ

/-- Worlds with the same first `t` queried observations agree on all
responses to histories shorter than `t`, including histories of other plans. -/
theorem pulseOutput_eq_of_queryTrace_eq {t : ℕ} {θ η : WaitingQueryWorld}
    (he : pulseTrace true t θ = pulseTrace true t η)
    (h : CausalHistory Bool Bool) (hh : h.length < t) (a : Bool) :
    pulseOutput θ h a = pulseOutput η h a := by
  have ho := congrArg (fun x : CausalFiniteTrace Bool Bool t => (x ⟨h.length, hh⟩).2) he
  by_cases hz : h = []
  · subst h
    simp only [pulseTrace, List.length_nil, ↓reduceIte, Bool.true_and] at ho
    simp [pulseOutput, ho]
  · have hl : h.length ≠ 0 := by simpa using hz
    simpa [pulseOutput, hz, pulseTrace, hl] using ho

/-- Finite deterministic execution only uses response rows before its horizon. -/
theorem detTraceList_congr_before {A O : Type*} [Fintype A] [Fintype O]
    (p : CausalHistory A O → A) (g g' : CausalHistory A O → A → O) (n : ℕ)
    (h : ∀ l : CausalHistory A O, l.length < n → ∀ a, g l a = g' l a) :
    detTraceList p g n = detTraceList p g' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn : detTraceList p g n = detTraceList p g' n :=
      ih (fun l hl a => h l (by omega) a)
    rw [detTraceList_succ, detTraceList_succ, hn,
      h _ (by simp only [detTraceList_length]; omega)]

/-- Equality of queried records separates every deterministic native target
whose depth is within the collection horizon. -/
theorem pulse_query_separates_plan {t m : ℕ} (hm : m ≤ t)
    (σ : CausalObservationPlan Bool Bool m) :
    SeparatesFor (pulseTrace true t)
      (fun θ => detPlanObs m σ.toCausalPlan (pulseOutput θ)) := by
  intro θ η he
  have hlist := detTraceList_congr_before (planAction m σ.toCausalPlan)
    (pulseOutput θ) (pulseOutput η) m
    (fun l hl a => pulseOutput_eq_of_queryTrace_eq he l (lt_of_lt_of_le hl hm) a)
  have hfin : detTraceFin (planAction m σ.toCausalPlan) (pulseOutput θ) m =
      detTraceFin (planAction m σ.toCausalPlan) (pulseOutput η) m := by
    apply List.ofFn_injective
    simpa only [ofFn_detTraceFin] using hlist
  exact congrArg causalTraceObservations hfin

theorem pulse_nativePlan_dirac {m : ℕ} (σ : CausalObservationPlan Bool Bool m) :
    CausalObservationPlan.behaviorPlanExperiment σ pulseBehavior =
      diracExp (fun θ => detPlanObs m σ.toCausalPlan (pulseOutput θ)) := by
  rw [CausalObservationPlan.behaviorPlanExperiment_toCausalPlan]
  change causalBehaviorPlanExperiment m σ.toCausalPlan
    (fun θ => CausalBehavior.ofResponse (detResponse (pulseOutput θ))
      (isCausalResponse_detResponse _)) = _
  rw [causalBehaviorPlanExperiment_ofResponse, causalPlanObservationExperiment_det]

theorem pulse_query_native_deficiency_zero {t m : ℕ} (hm : m ≤ t)
    (σ : CausalObservationPlan Bool Bool m) :
    finiteDeficiency (pulseExperiment true t)
      (CausalObservationPlan.behaviorPlanExperiment σ pulseBehavior) = 0 := by
  rw [pulseExperiment_eq_dirac, pulse_nativePlan_dirac]
  exact finiteDeficiency_diracExp_eq_zero_of_separates (pulse_query_separates_plan hm σ)

theorem pulse_rootQuery_observation (θ : WaitingQueryWorld) :
    detPlanObs 1 waitingQueryRootPlan.toCausalPlan (pulseOutput θ) =
      fun _ : Fin 1 => θ.isSome := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [detPlanObs, causalTraceObservations, detTraceFin, detTraceList,
    planAction, pulseOutput, waitingQueryRootPlan,
    CausalObservationPlan.toCausalPlan, CausalObservationPlan.toCausalPlanAux,
    CausalPlan.cons, CausalPlan.consFull, causalDecisionPointOfHistory]

/-- Waiting retains the persistent one-half obstruction to the actual
root-query native target, even though querying now preserves the stream. -/
theorem pulse_wait_rootQuery_deficiency (t : ℕ) :
    finiteDeficiency (pulseExperiment false t)
      (CausalObservationPlan.behaviorPlanExperiment waitingQueryRootPlan pulseBehavior) =
      (1 / 2 : ℝ) := by
  rw [pulseExperiment_wait, pulse_nativePlan_dirac]
  simp_rw [pulse_rootQuery_observation]
  rw [← waitingQueryRootPlan_experiment]
  exact waitingQuery_nativeQuery_deficiency_eq_half t

/-- Every complete deterministic pulse record identifies the world. This
is a statement about an infinite record, without any uniform finite cutoff. -/
theorem pulseTrace_all_injective (b : Bool) :
    Function.Injective (fun θ : WaitingQueryWorld => fun t => pulseTrace b t θ) := by
  intro θ η he
  have hobs : ∀ i, waitingQueryBit θ (i + 1) = waitingQueryBit η (i + 1) := by
    intro i
    have hi := congrArg (fun f : ∀ t, CausalFiniteTrace Bool Bool t =>
      (f (i + 2) ⟨i + 1, by omega⟩).2) he
    simpa [pulseTrace] using hi
  cases θ with
  | none =>
    cases η with
    | none => rfl
    | some k => simpa [waitingQueryBit] using hobs k
  | some k =>
    cases η with
    | none => simpa [waitingQueryBit] using hobs k
    | some l =>
      have hl := hobs k
      simpa [waitingQueryBit] using hl

/-- If one additional bit would make a deterministic record sufficient, a
fair guess for that bit gives a world-uniform one-half simulation bound.
No finiteness assumption on the world class is used. -/
theorem exists_one_missing_bit_decoder
    {Θ X Y : Type*} [Fintype X] [Fintype Y] [Nonempty Θ]
    (e : Θ → X) (b : Θ → Bool) (f : Θ → Y)
    (hsep : SeparatesFor (fun θ => (e θ, b θ)) f) :
    ∃ G : X → Y → ℝ, G ∈ stochasticRules X Y ∧
      ∀ θ, (1 / 2 : ℝ) ≤ G (e θ) (f θ) := by
  let D := diracPreimageDecoder (fun θ => (e θ, b θ)) f
  have hD : D ∈ stochasticRules (X × Bool) Y := diracPreimageDecoder_mem_stochasticRules _ _
  let G : X → Y → ℝ := fun x y => (D (x, false) y + D (x, true) y) / 2
  have hG : G ∈ stochasticRules X Y := by
    intro x _
    constructor
    · intro y
      exact div_nonneg (add_nonneg ((hD (x, false) trivial).1 y)
        ((hD (x, true) trivial).1 y)) (by norm_num)
    · change (∑ y, (D (x, false) y + D (x, true) y) / 2) = 1
      rw [← Finset.sum_div, Finset.sum_add_distrib,
        (hD (x, false) trivial).2, (hD (x, true) trivial).2]
      norm_num
  refine ⟨G, hG, fun θ => ?_⟩
  have hex : D (e θ, b θ) (f θ) = 1 := diracPreimageDecoder_apply_of_separates hsep θ
  have h0 := (hD (e θ, false) trivial).1 (f θ)
  have h1 := (hD (e θ, true) trivial).1 (f θ)
  dsimp [G]
  cases hb : b θ <;> simp only [hb] at hex <;> linarith

theorem finiteDeficiency_le_half_of_one_missing_bit
    {Θ X Y : Type*} [Fintype X] [Fintype Y] [Nonempty Θ]
    (e : Θ → X) (b : Θ → Bool) (f : Θ → Y)
    (hsep : SeparatesFor (fun θ => (e θ, b θ)) f) :
    finiteDeficiency (diracExp e) (diracExp f) ≤ (1 / 2 : ℝ) := by
  obtain ⟨G, hG, hcorrect⟩ := exists_one_missing_bit_decoder e b f hsep
  apply finiteDeficiency_le_of_decoder _ _ G hG
  intro θ
  rw [decodeErr_diracExp e f hG θ]
  linarith [hcorrect θ]

/-- The extra bit needed by the waiting record is exactly the root query answer. -/
theorem pulse_wait_bit_separates_plan {t m : ℕ} (hm : m ≤ t)
    (σ : CausalObservationPlan Bool Bool m) :
    SeparatesFor (fun θ => (pulseTrace false t θ, θ.isSome))
      (fun θ => detPlanObs m σ.toCausalPlan (pulseOutput θ)) := by
  intro θ η he
  apply pulse_query_separates_plan hm σ θ η
  funext i
  have hb : θ.isSome = η.isSome := congrArg Prod.snd he
  have ho := congrArg (fun x : CausalFiniteTrace Bool Bool t × Bool => (x.1 i).2) he
  by_cases hi : i.val = 0
  · simp [pulseTrace, hi, hb]
  · simpa [pulseTrace, hi] using ho

theorem pulse_wait_native_deficiency_le_half {t m : ℕ} (hm : m ≤ t)
    (σ : CausalObservationPlan Bool Bool m) :
    finiteDeficiency (pulseExperiment false t)
      (CausalObservationPlan.behaviorPlanExperiment σ pulseBehavior) ≤ (1 / 2 : ℝ) := by
  rw [pulseExperiment_eq_dirac, pulse_nativePlan_dirac]
  exact finiteDeficiency_le_half_of_one_missing_bit _ Option.isSome _
    (pulse_wait_bit_separates_plan hm σ)

/-- The full native audit, including all plans through depth `n`, is one half
at every `t ≥ n ≥ 1` for WAIT. -/
theorem pulse_wait_nativeAudit_eq_half {t n : ℕ} (ht : n ≤ t) (hn : 1 ≤ n) :
    causalBehaviorNativeDeficiencyUpTo (pulseExperiment false t) pulseBehavior n =
      (1 / 2 : ℝ) := by
  have hbound : ∀ d ∈ causalBehaviorNativeDeficiencyValuesUpTo
      (pulseExperiment false t) pulseBehavior n, d ≤ (1 / 2 : ℝ) := by
    rintro d ⟨m, hm, σ, rfl⟩
    exact pulse_wait_native_deficiency_le_half (hm.trans ht) σ
  have hmem : (1 / 2 : ℝ) ∈ causalBehaviorNativeDeficiencyValuesUpTo
      (pulseExperiment false t) pulseBehavior n :=
    ⟨1, hn, waitingQueryRootPlan, (pulse_wait_rootQuery_deficiency t).symm⟩
  exact le_antisymm (csSup_le ⟨_, hmem⟩ hbound) (le_csSup ⟨_, hbound⟩ hmem)

/-- QUERY is natively sufficient on the entire countable class. -/
theorem pulse_query_nativelySufficient :
    CausalBehaviorNativelySufficient pulseBehavior (pulsePolicy true) := by
  intro n ε hε
  refine ⟨n, fun t ht σ => ?_⟩
  change finiteDeficiency (pulseExperiment true t) _ < ε
  rw [pulse_query_native_deficiency_zero ht σ]
  exact hε

/-- WAIT is not natively sufficient, despite its injective complete record. -/
theorem pulse_wait_not_nativelySufficient :
    ¬ CausalBehaviorNativelySufficient pulseBehavior (pulsePolicy false) := by
  intro h
  obtain ⟨T, hT⟩ := h 1 (1 / 4) (by norm_num)
  have hf := hT T le_rfl waitingQueryRootPlan
  change finiteDeficiency (pulseExperiment false T) _ < (1 / 4 : ℝ) at hf
  rw [pulse_wait_rootQuery_deficiency] at hf
  norm_num at hf

/-- The queried process strictly dominates the waiting process in the
paper's actual finitary process preorder. -/
theorem pulse_query_strictly_dominates_wait :
    CausalBehaviorFinitaryDominates pulseBehavior (pulsePolicy true) (pulsePolicy false) ∧
    ¬ CausalBehaviorFinitaryDominates pulseBehavior (pulsePolicy false) (pulsePolicy true) := by
  have hgreat := (causalBehaviorNativelySufficient_iff_finitarilyGreatest
    pulseBehavior (pulsePolicy true)).1 pulse_query_nativelySufficient
  refine ⟨hgreat _, ?_⟩
  intro hback
  apply pulse_wait_not_nativelySufficient
  apply (causalBehaviorNativelySufficient_iff_finitarilyGreatest
    pulseBehavior (pulsePolicy false)).2
  intro ρ
  exact (causalBehaviorFinitaryDominates_isPreorder pulseBehavior).2
    _ _ _ hback (hgreat ρ)

end IdExp
