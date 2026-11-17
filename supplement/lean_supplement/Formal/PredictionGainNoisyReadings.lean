import Formal.AbsorbingExperiment
import Formal.CausalPartialExecution
import Formal.FiniteBayes

/-!
# Replay prediction gain prefers two noisy readings

This module formalizes the seven-state, two-world example of
`prop:prediction-gain-noisy-readings` in
`Paper/draft/intrinsic_rewards/prediction_gain_proof.tex`.

**The literal finite MDP.** The world is a bit `θ`. There are seven fully
observed physical states: START (`none`) and the six emitted states
`R b = (0,b)`, `U y = (1,y)`, `V z = (2,z)`. At START action `0` is REVEAL,
which moves to `R θ`, and action `1` is SAMPLE, which moves to `U y` with
`Pr(y = θ) = 9/10`. From `U y` the sole action moves to `V z` with
`Pr(z = θ) = 9/10`, independently of `y` given `θ`. Every `R b` and `V z` is
absorbing under its sole STAY action. The transition depends only on the
current physical state and action, so each world is a time-homogeneous MDP.
START is known and is not repeated in the emitted record, as in
`MOPFiniteMDP`; a record of length `t` contains `t` transitions.

**Legal actions.** Actions are encoded in the common alphabet `Fin 2`. Action
`1` is legal only at START. Off START both encoded actions have the identical
transition, so the ambient encoding adds no control; `Legal` records the
source convention. The native-deficiency, sufficiency and return theorems
hold for every valid randomized history policy of the ambient encoding,
hence in particular for every legal one.

**Shared tail.** The literal time-homogeneous response is world-dependent at
the controlled-null histories of length at least two that end in some `U y`.
`HasSupportedSharedCausalTail` therefore requires agreement only on histories
of nonzero controlled response likelihood. It is proved here to give the same
exact prefix Blackwell equivalence as `HasSharedCausalTail`.

**Reward scope.** The replay score below is the paper's exact Bayesian replay
prediction gain `eq:bayesian-replay-gain`, computed from the actual posterior
of the two-model class with prior `(1/2,1/2)`. Whether that score is the
source-faithful instantiation of the published prediction gain is an open
fidelity question recorded in
`Paper/research/prediction_gain_density_2026-10-07/` and
`Paper/research/source_fidelity_reconciliation_2026-10-07/`. Nothing here is
evidence about the established reward. Values at null predictive
probability use Lean's total division and carry zero expected weight.

**Main results.** For every valid randomized history policy with initial
REVEAL probability `s`:

* `native_deficiency`: deficiency `(1-s)/10` to the one-step native REVEAL
  experiment at every record length `t ≥ 2`; `eventualDeficiency_eq` and
  `native_deficiency_tendsto` give its infimum and limit;
* `revealPolicy_nativelySufficient` and `strictly_dominated`: REVEAL is natively
  sufficient and strictly dominates every policy with `s < 1`;
* `integer_certificate` and `sampleGainBits_gt_one`: `A > 1`;
* `horizonReturn_eq` and `completeReturn_eq`: the expected replay return is
  `s + (1-s) A` for every horizon `H ≥ 2` (counting transitions, that is
  rewards) and for the complete undiscounted sum; `replayGain_nonneg` and
  `horizonReturn_tendsto` show that the rewards are nonnegative and that this
  sum is the paper's complete return `lim_{H → ∞} E ∑_{u=1}^H r_u`;
* `horizon_maximizer_iff`, `complete_maximizer_iff` and their legal versions:
  maximizers are exactly the `s = 0` policies, attained by `samplePolicy`;
  `horizon_maximizer_native_loss` and its variants: every maximizer is
  strictly dominated and has permanent and eventual deficiency `1/10`.
-/

namespace IdExp

open Finset

/-! ## A support-restricted shared continuation -/

section SupportedSharedTail

variable {A O Θ : Type*} [Fintype A] [Fintype O]

/-- All worlds share the continuation kernel after depth `k` on every history
whose controlled response likelihood in that world is nonzero. Rows at
controlled-null histories are unconstrained. -/
def HasSupportedSharedCausalTail (Qs : Θ → CausalResponse A O) (k : ℕ)
    (R : CausalResponse A O) : Prop :=
  ∀ θ h a o, k ≤ h.length → causalResponseProb (Qs θ) h ≠ 0 → Qs θ h a o = R h a o

omit [Fintype A] [Fintype O] in
/-- The unrestricted shared-tail hypothesis is a special case. -/
theorem HasSharedCausalTail.supported {Qs : Θ → CausalResponse A O} {k : ℕ}
    {R : CausalResponse A O} (htail : HasSharedCausalTail Qs k R) :
    HasSupportedSharedCausalTail Qs k R :=
  fun θ h a o hk _ => htail θ h a o hk

/-- Exact one-step extension under the support-restricted hypothesis. At a
controlled-null prefix both sides vanish, whatever the response row there. -/
theorem causalFiniteExperiment_supportedSharedTail_step
    (π : CausalPolicy A O) (Qs : Θ → CausalResponse A O)
    (R : CausalResponse A O) (k n : ℕ) (htail : HasSupportedSharedCausalTail Qs k R)
    (hn : k ≤ n) :
    finiteDecisionLaw (causalFiniteExperiment π Qs n) (causalSharedTailRule π R n) =
      causalFiniteExperiment π Qs (n + 1) := by
  classical
  funext θ v
  unfold finiteDecisionLaw
  simp only [causalSharedTailRule, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  unfold causalFiniteExperiment
  rw [List.ofFn_succ_last, causalTraceProb_append_singleton]
  simp only [Fin.init_def]
  set h := List.ofFn (fun i : Fin n => v i.castSucc)
  by_cases hz : causalResponseProb (Qs θ) h = 0
  · have hp : causalTraceProb π (Qs θ) h = 0 := by
      rw [causalTraceProb_factor, hz, mul_zero]
    rw [hp]
    ring
  · rw [htail θ h _ _ (by simpa [h] using hn) hz]
    ring

theorem causalFiniteExperiment_supportedSharedTail_step_blackwell
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (R : CausalResponse A O)
    (hR : IsCausalResponse R) (k n : ℕ) (htail : HasSupportedSharedCausalTail Qs k R)
    (hn : k ≤ n) :
    FiniteBlackwellLE (causalFiniteExperiment π Qs (n + 1))
      (causalFiniteExperiment π Qs n) :=
  ⟨causalSharedTailRule π R n, causalSharedTailRule_valid π hπ R hR n,
    causalFiniteExperiment_supportedSharedTail_step π Qs R k n htail hn⟩

/-- A recorded `k`-prefix simulates every later finite record exactly. -/
theorem causalFiniteExperiment_of_supportedSharedTail_blackwell
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (R : CausalResponse A O)
    (hR : IsCausalResponse R) (k : ℕ) (htail : HasSupportedSharedCausalTail Qs k R)
    {n : ℕ} (hn : k ≤ n) :
    FiniteBlackwellLE (causalFiniteExperiment π Qs n)
      (causalFiniteExperiment π Qs k) := by
  exact Nat.le_induction (finiteBlackwellLE_refl _)
    (fun m hm ih => finiteBlackwellLE_trans
      (causalFiniteExperiment_supportedSharedTail_step_blackwell π hπ Qs R hR k m htail hm) ih)
    n hn

/-- Under the support-restricted shared tail, every later record is exactly
Blackwell-equivalent to the depth-`k` record. -/
theorem causalFiniteExperiment_supportedSharedTail_blackwell_equiv
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (R : CausalResponse A O) (hR : IsCausalResponse R)
    (k : ℕ) (htail : HasSupportedSharedCausalTail Qs k R) {n : ℕ} (hn : k ≤ n) :
    FiniteBlackwellLE (causalFiniteExperiment π Qs n)
      (causalFiniteExperiment π Qs k) ∧
    FiniteBlackwellLE (causalFiniteExperiment π Qs k)
      (causalFiniteExperiment π Qs n) :=
  ⟨causalFiniteExperiment_of_supportedSharedTail_blackwell π hπ Qs R hR k htail hn,
    causalFiniteExperiment_prefix_blackwell_of_le π hπ Qs hQ hn⟩

end SupportedSharedTail

namespace PredictionGainNoisyReadings

open Filter
open scoped Topology

noncomputable section

/-! ## The literal seven-state MDP -/

abbrev World := Fin 2
abbrev Action := Fin 2
/-- Emitted physical states: kind `0,1,2` for `R,U,V`, and a bit. -/
abbrev Outcome := Fin 3 × Fin 2
/-- Physical states; `none` is the known initial START. -/
abbrev State := Option Outcome
abbrev History := CausalHistory Action Outcome

/-- `R b`: the bit revealed exactly. -/
abbrev R (b : Fin 2) : Outcome := (0, b)
/-- `U y`: the first noisy reading. -/
abbrev U (y : Fin 2) : Outcome := (1, y)
/-- `V z`: the second noisy reading. -/
abbrev V (z : Fin 2) : Outcome := (2, z)

/-- REVEAL at START; the sole action (move or STAY) elsewhere. -/
abbrev reveal : Action := 0
/-- SAMPLE, legal only at START. -/
abbrev sample : Action := 1

theorem state_card : Fintype.card State = 7 := by decide

/-- A noisy reading of world bit `θ` is correct with probability `9/10`. -/
def noisy (θ : World) (y : Fin 2) : ℝ := if y = θ then 9/10 else 1/10

/-- Successor-state law over the emitted states. -/
def next (θ : World) : State → Action → Outcome → ℝ
  | none, a, o =>
      if a = 0 then (if o = (0, θ) then 1 else 0)
      else (if o.1 = 1 then noisy θ o.2 else 0)
  | some x, _, o =>
      if x.1 = 1 then (if o.1 = 2 then noisy θ o.2 else 0)
      else (if o = x then 1 else 0)

/-- The actual finite MDP transition kernel on all seven physical states. -/
def transition (θ : World) (x : State) (a : Action) : State → ℝ
  | none => 0
  | some o => next θ x a o

theorem noisy_nonneg (θ : World) (y : Fin 2) : 0 ≤ noisy θ y := by
  unfold noisy; split_ifs <;> norm_num

theorem sum_noisy (θ : World) : ∑ y, noisy θ y = 1 := by
  fin_cases θ <;> norm_num [noisy, Fin.sum_univ_two]

theorem noisy_add (θ : World) : noisy θ 0 + noisy θ 1 = 1 := by
  fin_cases θ <;> norm_num [noisy]

theorem next_valid (θ : World) (x : State) (a : Action) : IsDist (next θ x a) := by
  cases x with
  | none =>
    constructor
    · intro o; simp only [next]; split_ifs <;> first | exact noisy_nonneg _ _ | norm_num
    · by_cases ha : a = 0
      · simp only [next, ha, if_true]
        simp
      · simp only [next, ha, if_false, Fintype.sum_prod_type, Fin.sum_univ_three]
        simp [noisy_add]
  | some x =>
    constructor
    · intro o; simp only [next]; split_ifs <;> first | exact noisy_nonneg _ _ | norm_num
    · by_cases hx : x.1 = 1
      · simp only [next, hx, if_true, Fintype.sum_prod_type, Fin.sum_univ_three]
        simp [noisy_add]
      · simp only [next, hx, if_false]
        simp

theorem transition_valid (θ : World) (x : State) (a : Action) :
    IsDist (transition θ x a) := by
  constructor
  · intro y; cases y with
    | none => exact le_rfl
    | some o => exact (next_valid θ x a).1 o
  · simpa [Fintype.sum_option, transition] using (next_valid θ x a).2

@[simp] theorem transition_never_start (θ : World) (x : State) (a : Action) :
    transition θ x a none = 0 := rfl

/-- Off START the two encoded actions have the identical transition. -/
theorem transition_offStart_action (θ : World) (o : Outcome) (a a' : Action) :
    transition θ (some o) a = transition θ (some o) a' := by
  funext y; cases y <;> rfl

/-! The literal transition table, stated with the named states. -/

theorem next_start_reveal (θ : World) (o : Outcome) :
    next θ none reveal o = if o = R θ then 1 else 0 := rfl

theorem next_start_sample_U (θ y : Fin 2) : next θ none sample (U y) = noisy θ y := rfl

theorem next_start_sample_not_U (θ : World) (o : Outcome) (ho : o.1 ≠ 1) :
    next θ none sample o = 0 := by
  simp [next, ho]

theorem next_U_V (θ y : Fin 2) (a : Action) (z : Fin 2) :
    next θ (some (U y)) a (V z) = noisy θ z := rfl

theorem next_U_not_V (θ y : Fin 2) (a : Action) (o : Outcome) (ho : o.1 ≠ 2) :
    next θ (some (U y)) a o = 0 := by
  simp [next, ho]

theorem next_R_stay (θ b : Fin 2) (a : Action) (o : Outcome) :
    next θ (some (R b)) a o = if o = R b then 1 else 0 := by
  simp [next]

theorem next_V_stay (θ z : Fin 2) (a : Action) (o : Outcome) :
    next θ (some (V z)) a o = if o = V z then 1 else 0 := by
  simp [next]

/-- The last emitted state; the default is used only for the empty record, whose
current state is the known START. -/
def lastObs (h : History) : Outcome := (h.reverse.headD (0, (0, 0))).2

def currentState (h : History) : State := if h = [] then none else some (lastObs h)

@[simp] theorem currentState_nil : currentState [] = none := by simp [currentState]

@[simp] theorem lastObs_append (h : History) (a : Action) (o : Outcome) :
    lastObs (h ++ [(a, o)]) = o := by
  simp [lastObs, List.reverse_append]

@[simp] theorem currentState_append (h : History) (a : Action) (o : Outcome) :
    currentState (h ++ [(a, o)]) = some o := by
  simp [currentState]

@[simp] theorem currentState_singleton (x : Action × Outcome) :
    currentState [x] = some x.2 := by
  simpa using currentState_append [] x.1 x.2

/-- The causal response of world `θ`: the physical transition from the current
state, restricted to the emitted states. -/
def response (θ : World) : CausalResponse Action Outcome :=
  fun h a o => transition θ (currentState h) a (some o)

theorem response_eq_next (θ : World) (h : History) (a : Action) (o : Outcome) :
    response θ h a o = next θ (currentState h) a o := rfl

/-- The emitted record law is exactly the MDP transition law: no mass is lost
on START. -/
theorem transition_response (θ : World) (h : History) (a : Action) (o : Outcome) :
    transition θ (currentState h) a (some o) = response θ h a o := rfl

theorem response_valid (θ : World) : IsCausalResponse (response θ) := by
  intro h a
  exact next_valid θ (currentState h) a

@[simp] theorem response_nil (θ : World) (a : Action) (o : Outcome) :
    response θ [] a o = next θ none a o := by
  simp [response_eq_next]

theorem response_append (θ : World) (h : History) (x : Action × Outcome)
    (a : Action) (o : Outcome) :
    response θ (h ++ [x]) a o = next θ (some x.2) a o := by
  obtain ⟨a', o'⟩ := x
  simp [response_eq_next]

/-- Legal actions: both at START, only action `0` at every emitted state. -/
def available (x : State) : Finset Action := if x = none then univ else {0}

/-- A history policy is legal when it uses only actions available at the
current physical state. -/
def Legal (π : ValidCausalPolicy Action Outcome) : Prop :=
  ∀ h a, a ∉ available (currentState h) → π.1 h a = 0

theorem legal_iff (π : ValidCausalPolicy Action Outcome) :
    Legal π ↔ ∀ h : History, h ≠ [] → π.1 h 1 = 0 := by
  constructor
  · intro hl h hh
    apply hl
    simp [available, currentState, hh]
  · intro hl h a ha
    by_cases hh : h = []
    · subst hh; simp [available] at ha
    · have ha1 : a = 1 := by
        simp only [available, currentState, hh, if_false, reduceCtorEq] at ha
        fin_cases a <;> simp_all
      rw [ha1]; exact hl h hh

/-! ## Later records add no information -/

/-- The world-independent STAY continuation at an `R` or `V` state. -/
def stay : CausalResponse Action Outcome :=
  fun h _ o => if o = lastObs h then 1 else 0

theorem stay_valid : IsCausalResponse stay := by
  intro h a
  constructor
  · intro o; simp only [stay]; split_ifs <;> norm_num
  · simp [stay]

/-- After START, no transition reaches a `U` state in either world. -/
theorem next_some_ne_U (θ : World) (x : Outcome) (a : Action) (o : Outcome)
    (hnz : next θ (some x) a o ≠ 0) : o.1 ≠ 1 := by
  intro ho
  simp only [next] at hnz
  split_ifs at hnz with h1 h2 h3
  · rw [ho] at h2; exact absurd h2 (by decide)
  · exact hnz rfl
  · exact h1 (h3 ▸ ho)
  · exact hnz rfl

/-- The controlled response likelihood factors at the last transition. -/
theorem causalResponseProb_append (Q : CausalResponse Action Outcome) (h : History)
    (x : Action × Outcome) :
    causalResponseProb Q (h ++ [x]) = causalResponseProb Q h * Q h x.1 x.2 := by
  unfold causalResponseProb
  rw [causalResponseProbFrom_append_singleton]
  simp

/-- A history of length at least two with positive controlled likelihood in
some world ends at an `R` or `V` state. -/
theorem lastObs_ne_U_of_support (θ : World) (h : History) (hlen : 2 ≤ h.length)
    (hne : causalResponseProb (response θ) h ≠ 0) : (lastObs h).1 ≠ 1 := by
  have hh : h ≠ [] := by
    intro hz; simp [hz] at hlen
  obtain ⟨h', x, rfl⟩ : ∃ h' x, h = h' ++ [x] :=
    ⟨h.dropLast, h.getLast hh, (List.dropLast_append_getLast hh).symm⟩
  have hh' : h' ≠ [] := by
    intro hz; simp [hz] at hlen
  have hstep : response θ h' x.1 x.2 ≠ 0 := by
    intro hz
    apply hne
    rw [causalResponseProb_append, hz, mul_zero]
  rw [response_eq_next] at hstep
  simp only [currentState, if_neg hh'] at hstep
  obtain ⟨a', o'⟩ := x
  rw [lastObs_append]
  exact next_some_ne_U θ _ _ _ hstep

/-- At an `R` or `V` state both worlds use the same STAY row. -/
theorem response_eq_stay (θ : World) (h : History) (a : Action) (o : Outcome)
    (hh : h ≠ []) (hx : (lastObs h).1 ≠ 1) : response θ h a o = stay h a o := by
  rw [response_eq_next]
  simp only [currentState, if_neg hh, next, if_neg hx, stay]

/-- Every history of positive controlled likelihood and length at least two
ends at an `R` or `V` state, where both worlds use the STAY kernel. -/
theorem response_supportedSharedTail : HasSupportedSharedCausalTail response 2 stay := by
  intro θ h a o hlen hne
  have hh : h ≠ [] := by
    intro hz; simp [hz] at hlen
  exact response_eq_stay θ h a o hh (lastObs_ne_U_of_support θ h hlen hne)

/-- The unrestricted shared-tail hypothesis fails for the literal
time-homogeneous response: at the controlled-null record `[(SAMPLE, U 0),
(0, U 0)]` the two worlds' rows differ. -/
theorem not_hasSharedCausalTail : ¬ ∃ Q, HasSharedCausalTail response 2 Q := by
  rintro ⟨Q, hQ⟩
  have h0 := hQ 0 [(1, (1, 0)), (0, (1, 0))] 0 (2, 0) (by simp)
  have h1 := hQ 1 [(1, (1, 0)), (0, (1, 0))] 0 (2, 0) (by simp)
  have e (θ : World) : response θ [(1, (1, 0)), (0, (1, 0))] 0 (2, 0) = noisy θ 0 :=
    response_append θ [(1, (1, 0))] (0, (1, 0)) 0 (2, 0)
  rw [← h1, e, e] at h0
  norm_num [noisy] at h0

/-- The shared tail starts at two transitions for every policy. -/
theorem record_blackwell_equiv (π : ValidCausalPolicy Action Outcome) {t : ℕ}
    (ht : 2 ≤ t) :
    FiniteBlackwellLE (causalFiniteExperiment π.1 response t)
        (causalFiniteExperiment π.1 response 2) ∧
      FiniteBlackwellLE (causalFiniteExperiment π.1 response 2)
        (causalFiniteExperiment π.1 response t) :=
  causalFiniteExperiment_supportedSharedTail_blackwell_equiv π.1 π.2 response
    response_valid stay stay_valid 2 response_supportedSharedTail ht

/-! ## The one-step native REVEAL experiment -/

/-- The first transition from START, as a finite experiment for each action. -/
def rootRow (a : Action) : FiniteExperiment World Outcome := fun θ o => next θ none a o

theorem rootRow_valid (a : Action) : IsFiniteExperiment (rootRow a) :=
  fun θ => next_valid θ none a

/-- REVEAL's exact revelation of the world bit. -/
def revealRow : FiniteExperiment World Outcome := rootRow 0

theorem revealRow_valid : IsFiniteExperiment revealRow := rootRow_valid 0

theorem revealRow_apply (θ : World) (o : Outcome) :
    revealRow θ o = if o = (0, θ) then 1 else 0 := by
  simp [revealRow, rootRow, next]

/-- The deterministic one-step native intervention REVEAL. -/
def revealPlan : CausalPlan Action Outcome 1 := fun _ => 0

/-- The paper's `F`: the observation experiment of the native REVEAL test. -/
def nativeReveal : FiniteExperiment World (CausalObservationTrace Outcome 1) :=
  causalPlanObservationExperiment 1 revealPlan response

theorem nativeReveal_valid : IsFiniteExperiment nativeReveal :=
  causalPlanObservationExperiment_valid 1 revealPlan response response_valid

/-- One-step records see only the START transition. -/
theorem one_eq_absorbing (π : CausalPolicy Action Outcome) :
    causalFiniteExperiment π response 1 =
      causalFiniteExperiment π (absorbingResponse (0, 0) rootRow) 1 := by
  funext θ w
  simp [causalFiniteExperiment, causalTraceProb, List.ofFn_succ, causalTraceProbFrom,
    absorbingResponse, rootRow]

theorem nativeReveal_equiv :
    FiniteBlackwellLE nativeReveal revealRow ∧ FiniteBlackwellLE revealRow nativeReveal := by
  have heq : nativeReveal =
      causalPlanObservationExperiment 1 revealPlan (absorbingResponse (0, 0) rootRow) := by
    unfold nativeReveal causalPlanObservationExperiment
    rw [one_eq_absorbing]
  rw [heq]
  exact absorbingNativeTest_all_depths_blackwell_equiv (0, 0) rootRow rootRow_valid 0 revealPlan

/-! ## The two-transition record -/

theorem policy_root_other (π : ValidCausalPolicy Action Outcome) :
    π.1 [] 1 = 1 - π.1 [] 0 := by
  have h := (π.2 []).2
  rw [Fin.sum_univ_two] at h
  linarith

theorem policy_root_bounds (π : ValidCausalPolicy Action Outcome) :
    0 ≤ π.1 [] 0 ∧ π.1 [] 0 ≤ 1 := by
  refine ⟨(π.2 []).1 0, ?_⟩
  have hn := (π.2 []).1 1
  rw [policy_root_other] at hn
  linarith

/-- Observation law of the two transitions after root action `a`. -/
def obs2 (θ : World) (a : Action) (o0 o1 : Outcome) : ℝ :=
  next θ none a o0 * next θ (some o0) 0 o1

/-- The two SAMPLE readings are conditionally independent given the world. -/
theorem obs2_sample_readings (θ y z : Fin 2) :
    obs2 θ sample (U y) (V z) = noisy θ y * noisy θ z := rfl

theorem next_some_action (θ : World) (o : Outcome) (a : Action) (o' : Outcome) :
    next θ (some o) a o' = next θ (some o) 0 o' := rfl

theorem sum_trace_two (f : CausalFiniteTrace Action Outcome 2 → ℝ) :
    ∑ w, f w = ∑ x : Action × Outcome, ∑ y : Action × Outcome, f ![x, y] := by
  rw [← (finTwoArrowEquiv (Action × Outcome)).symm.sum_comp, Fintype.sum_prod_type]
  simp only [finTwoArrowEquiv_symm_apply]

theorem record_two_apply (π : CausalPolicy Action Outcome) (θ : World)
    (x y : Action × Outcome) :
    causalFiniteExperiment π response 2 θ ![x, y] =
      π [] x.1 * π [x] y.1 * obs2 θ x.1 x.2 y.2 := by
  obtain ⟨a, o⟩ := x
  obtain ⟨a', o'⟩ := y
  simp only [causalFiniteExperiment, causalTraceProb, List.ofFn_succ, List.ofFn_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, causalTraceProbFrom, List.nil_append,
    obs2, response_nil]
  rw [show [(a, o)] = ([] : History) ++ [(a, o)] from rfl, response_append]
  simp only [List.nil_append, next_some_action θ o a' o']
  ring

/-- Policy weights factor out of the two-transition record; the second action
label does not affect either world's transition. -/
theorem sum_policy_two (π : ValidCausalPolicy Action Outcome)
    (g : Action → Outcome → Outcome → ℝ) :
    ∑ x : Action × Outcome, ∑ y : Action × Outcome, π.1 [] x.1 * π.1 [x] y.1 * g x.1 x.2 y.2 =
      ∑ a, π.1 [] a * ∑ o0, ∑ o1, g a o0 o1 := by
  have key (a : Action) (o0 : Outcome) :
      ∑ y : Action × Outcome, π.1 [] a * π.1 [(a, o0)] y.1 * g a o0 y.2 =
        π.1 [] a * ∑ o1, g a o0 o1 := by
    rw [Fintype.sum_prod_type]
    calc ∑ a1, ∑ o1, π.1 [] a * π.1 [(a, o0)] a1 * g a o0 o1
        = ∑ a1, π.1 [(a, o0)] a1 * (π.1 [] a * ∑ o1, g a o0 o1) := by
          apply sum_congr rfl; intro a1 _
          rw [mul_sum, mul_sum]; apply sum_congr rfl; intro o1 _; ring
      _ = π.1 [] a * ∑ o1, g a o0 o1 := by rw [← sum_mul, (π.2 _).2, one_mul]
  rw [Fintype.sum_prod_type]
  simp only [key, mul_sum]

theorem record_two_sum (π : ValidCausalPolicy Action Outcome) (θ : World)
    (f : Outcome → Outcome → ℝ) :
    ∑ w, causalFiniteExperiment π.1 response 2 θ w * f (w 0).2 (w 1).2 =
      ∑ a, π.1 [] a * ∑ o0, ∑ o1, obs2 θ a o0 o1 * f o0 o1 := by
  rw [sum_trace_two]
  simp only [record_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← sum_policy_two π (fun a o0 o1 => obs2 θ a o0 o1 * f o0 o1)]
  apply sum_congr rfl; intro x _; apply sum_congr rfl; intro y _; ring

theorem obs2_tv_reveal :
    ∑ o0, ∑ o1, |obs2 0 0 o0 o1 - obs2 1 0 o0 o1| = 2 := by
  simp [obs2, next, noisy, Fintype.sum_prod_type, Fin.sum_univ_three]
  norm_num

theorem obs2_tv_sample :
    ∑ o0, ∑ o1, |obs2 0 1 o0 o1 - obs2 1 1 o0 o1| = 8/5 := by
  simp [obs2, next, noisy, Fintype.sum_prod_type, Fin.sum_univ_three]
  norm_num

/-- The two full-record rows have distance `s + (1-s) 4/5`. -/
theorem record_two_pairTV (π : ValidCausalPolicy Action Outcome) :
    finiteTV (causalFiniteExperiment π.1 response 2 0)
      (causalFiniteExperiment π.1 response 2 1) = π.1 [] 0 + (1 - π.1 [] 0) * (4/5) := by
  unfold finiteTV
  rw [sum_trace_two]
  have habs (x y : Action × Outcome) :
      |causalFiniteExperiment π.1 response 2 0 ![x, y] -
          causalFiniteExperiment π.1 response 2 1 ![x, y]| =
        π.1 [] x.1 * π.1 [x] y.1 * |obs2 0 x.1 x.2 y.2 - obs2 1 x.1 x.2 y.2| := by
    rw [record_two_apply, record_two_apply, ← mul_sub, abs_mul,
      abs_of_nonneg (mul_nonneg ((π.2 _).1 _) ((π.2 _).1 _))]
  simp only [habs]
  rw [sum_policy_two π (fun a o0 o1 => |obs2 0 a o0 o1 - obs2 1 a o0 o1|),
    Fin.sum_univ_two, obs2_tv_reveal, obs2_tv_sample, policy_root_other]
  ring

theorem revealRow_pairTV : finiteTV (revealRow 0) (revealRow 1) = 1 := by
  simp [finiteTV, revealRow_apply, Fintype.sum_prod_type, Fin.sum_univ_three]
  norm_num

/-- Copy a revealed bit; on agreeing readings return the common bit; on
disagreeing readings guess fairly. Impossible records are sent to `R 0`. -/
def decodeObs (o0 o1 : Outcome) : Outcome → ℝ := fun o =>
  if o0.1 = 0 then (if o = o0 then 1 else 0)
  else if o0.1 = 1 ∧ o1.1 = 2 then
    (if o0.2 = o1.2 then (if o = (0, o0.2) then 1 else 0) else (if o.1 = 0 then 1/2 else 0))
  else (if o = (0, 0) then 1 else 0)

theorem decodeObs_valid (o0 o1 : Outcome) : IsDist (decodeObs o0 o1) := by
  constructor
  · intro o; unfold decodeObs; split_ifs <;> norm_num
  · unfold decodeObs
    split_ifs <;> (simp [Fintype.sum_prod_type, Fin.sum_univ_three]; try norm_num)

/-- The world-independent decoder from the two-transition record. -/
def decoder : CausalFiniteTrace Action Outcome 2 → Outcome → ℝ :=
  fun w => decodeObs (w 0).2 (w 1).2

theorem decoder_valid :
    decoder ∈ stochasticRules (CausalFiniteTrace Action Outcome 2) Outcome :=
  fun _ _ => decodeObs_valid _ _

theorem decode_reveal (θ : World) (o : Outcome) :
    ∑ o0, ∑ o1, obs2 θ 0 o0 o1 * decodeObs o0 o1 o = revealRow θ o := by
  rw [revealRow_apply]
  obtain ⟨k, b⟩ := o
  fin_cases θ <;> fin_cases k <;> fin_cases b <;>
    simp [obs2, next, noisy, decodeObs, Fintype.sum_prod_type, Fin.sum_univ_three]

/-- Sampling decodes the bit correctly with probability `9/10`. -/
def sampleDecoded (θ : World) (o : Outcome) : ℝ :=
  if o = (0, θ) then 9/10 else if o.1 = 0 then 1/10 else 0

theorem decode_sample (θ : World) (o : Outcome) :
    ∑ o0, ∑ o1, obs2 θ 1 o0 o1 * decodeObs o0 o1 o = sampleDecoded θ o := by
  obtain ⟨k, b⟩ := o
  fin_cases θ <;> fin_cases k <;> fin_cases b <;>
    simp [obs2, next, noisy, decodeObs, sampleDecoded, Fintype.sum_prod_type,
      Fin.sum_univ_three] <;> norm_num

theorem sampleDecoded_tv (θ : World) :
    ∑ o, |sampleDecoded θ o - revealRow θ o| = 1/5 := by
  fin_cases θ <;>
    simp [sampleDecoded, revealRow_apply, Fintype.sum_prod_type, Fin.sum_univ_three] <;>
    norm_num

theorem decoder_error (π : ValidCausalPolicy Action Outcome) (θ : World) :
    decodeErr (causalFiniteExperiment π.1 response 2) revealRow decoder θ =
      (1 - π.1 [] 0) / 10 := by
  have hs := policy_root_bounds π
  unfold decodeErr
  have hlaw (o : Outcome) :
      ∑ w, causalFiniteExperiment π.1 response 2 θ w * decoder w o =
        π.1 [] 0 * revealRow θ o + (1 - π.1 [] 0) * sampleDecoded θ o := by
    unfold decoder
    rw [record_two_sum π θ (fun o0 o1 => decodeObs o0 o1 o), Fin.sum_univ_two,
      decode_reveal, decode_sample, policy_root_other]
  have hterm (o : Outcome) :
      |(∑ w, causalFiniteExperiment π.1 response 2 θ w * decoder w o) - revealRow θ o| =
        (1 - π.1 [] 0) * |sampleDecoded θ o - revealRow θ o| := by
    rw [hlaw, show π.1 [] 0 * revealRow θ o + (1 - π.1 [] 0) * sampleDecoded θ o -
        revealRow θ o = (1 - π.1 [] 0) * (sampleDecoded θ o - revealRow θ o) by ring,
      abs_mul, abs_of_nonneg (by linarith)]
  simp only [hterm, ← mul_sum, sampleDecoded_tv]
  ring

/-- Exact deficiency of the two-transition record to exact revelation. -/
theorem record_two_revelation_deficiency (π : ValidCausalPolicy Action Outcome) :
    finiteDeficiency (causalFiniteExperiment π.1 response 2) revealRow =
      (1 - π.1 [] 0) / 10 := by
  apply le_antisymm
  · exact finiteDeficiency_le_of_decoder _ _ decoder decoder_valid _
      (fun θ => (decoder_error π θ).le)
  · have h := finiteDeficiency_pairwise_lower (causalFiniteExperiment π.1 response 2) revealRow
      (causalFiniteExperiment_valid π.1 π.2 response response_valid 2) revealRow_valid 0 1
    rw [revealRow_pairTV, record_two_pairTV] at h
    linarith

theorem record_revelation_deficiency (π : ValidCausalPolicy Action Outcome) {t : ℕ}
    (ht : 2 ≤ t) :
    finiteDeficiency (causalFiniteExperiment π.1 response t) revealRow =
      (1 - π.1 [] 0) / 10 := by
  obtain ⟨h1, h2⟩ := record_blackwell_equiv π ht
  rw [finiteDeficiency_eq_of_source_blackwellEquiv _ _ revealRow h1 h2]
  exact record_two_revelation_deficiency π

/-- **Native deficiency.** For every valid randomized history policy and every
record length `t ≥ 2`, the deficiency to the one-step native REVEAL experiment
is `(1-s)/10`, where `s` is the initial REVEAL probability. -/
theorem native_deficiency (π : ValidCausalPolicy Action Outcome) {t : ℕ} (ht : 2 ≤ t) :
    finiteDeficiency (causalFiniteExperiment π.1 response t) nativeReveal =
      (1 - π.1 [] 0) / 10 := by
  rw [finiteDeficiency_eq_of_target_blackwellEquiv _ _ revealRow
    (causalFiniteExperiment_valid π.1 π.2 response response_valid t) nativeReveal_valid
    revealRow_valid nativeReveal_equiv.1 nativeReveal_equiv.2]
  exact record_revelation_deficiency π ht

/-- Discarding later observations cannot reduce deficiency. -/
theorem native_deficiency_ge (π : ValidCausalPolicy Action Outcome) (t : ℕ) :
    (1 - π.1 [] 0) / 10 ≤
      finiteDeficiency (causalFiniteExperiment π.1 response t) nativeReveal := by
  rw [← native_deficiency π (le_max_right t 2)]
  exact finiteDeficiency_mono_source_of_finiteBlackwellLE _ _ _
    (causalFiniteExperiment_prefix_blackwell_of_le π.1 π.2 response response_valid
      (le_max_left t 2))

/-- Infimum over all record lengths of the native REVEAL deficiency. -/
def eventualDeficiency (π : ValidCausalPolicy Action Outcome) : ℝ :=
  sInf (Set.range fun t => finiteDeficiency (causalFiniteExperiment π.1 response t) nativeReveal)

theorem eventualDeficiency_eq (π : ValidCausalPolicy Action Outcome) :
    eventualDeficiency π = (1 - π.1 [] 0) / 10 := by
  apply IsLeast.csInf_eq
  refine ⟨⟨2, native_deficiency π le_rfl⟩, ?_⟩
  rintro _ ⟨t, rfl⟩
  exact native_deficiency_ge π t

theorem native_deficiency_tendsto (π : ValidCausalPolicy Action Outcome) :
    Tendsto (fun t => finiteDeficiency (causalFiniteExperiment π.1 response t) nativeReveal)
      atTop (𝓝 ((1 - π.1 [] 0) / 10)) :=
  tendsto_atTop_of_eventually_const (i₀ := 2) fun _ ht => native_deficiency π ht

/-! ## REVEAL is natively sufficient -/

/-- Exact revelation of the world bit generates every finite two-world experiment. -/
theorem revelation_dominates {Y : Type*} [Fintype Y]
    (E : FiniteExperiment World Y) (hE : IsFiniteExperiment E) :
    FiniteBlackwellLE E revealRow := by
  classical
  let G : Outcome → Y → ℝ := fun o => if o = (0, 0) then E 0 else E 1
  refine ⟨G, ?_, ?_⟩
  · intro o _
    by_cases ho : o = (0, 0)
    · simpa [G, ho] using hE 0
    · simpa [G, ho] using hE 1
  · funext θ y
    fin_cases θ <;>
      simp [finiteDecisionLaw, revealRow_apply, G]

/-- Always take action `0`: REVEAL at START and the sole action afterwards. -/
def revealPolicy : ValidCausalPolicy Action Outcome :=
  ⟨fun _ a => if a = 0 then 1 else 0, fun _ => by
    constructor
    · intro a; dsimp only; split_ifs <;> norm_num
    · simp⟩

/-- SAMPLE at START and the sole action afterwards. -/
def samplePolicy : ValidCausalPolicy Action Outcome :=
  ⟨fun h a => if h = [] then (if a = 1 then 1 else 0) else (if a = 0 then 1 else 0), fun h => by
    constructor
    · intro a; dsimp only; split_ifs <;> norm_num
    · by_cases hh : h = [] <;> simp [hh]⟩

theorem revealPolicy_root : revealPolicy.1 [] 0 = 1 := rfl

theorem samplePolicy_root : samplePolicy.1 [] 0 = 0 := rfl

theorem revealPolicy_legal : Legal revealPolicy :=
  (legal_iff _).2 fun _ _ => rfl

theorem samplePolicy_legal : Legal samplePolicy :=
  (legal_iff _).2 fun h hh => by simp [samplePolicy, hh]

/-- REVEAL simulates every finite native intervention after two transitions,
including interventions in the ambient action encoding. -/
theorem revealPolicy_nativelySufficient : CausalNativelySufficient response revealPolicy := by
  intro n ε hε
  refine ⟨2, ?_⟩
  intro t ht τ
  have h := finiteDeficiency_mono_target_of_finiteBlackwellLE
    (causalFiniteExperiment revealPolicy.1 response t)
    (causalPlanObservationExperiment n τ response) revealRow
    (causalFiniteExperiment_valid revealPolicy.1 revealPolicy.2 response response_valid t)
    revealRow_valid
    (revelation_dominates _ (causalPlanObservationExperiment_valid n τ response response_valid))
  rw [record_revelation_deficiency revealPolicy ht, revealPolicy_root] at h
  linarith

/-- Every policy with initial REVEAL probability below one fails native
sufficiency. -/
theorem not_nativelySufficient (π : ValidCausalPolicy Action Outcome)
    (hs : π.1 [] 0 < 1) : ¬ CausalNativelySufficient response π := by
  intro hsuff
  obtain ⟨T, hT⟩ := hsuff 1 ((1 - π.1 [] 0) / 10) (by linarith)
  have h := hT (max T 2) (le_max_left _ _) revealPlan
  rw [show causalPlanObservationExperiment 1 revealPlan response = nativeReveal from rfl,
    native_deficiency π (le_max_right _ _)] at h
  exact lt_irrefl _ h

/-- REVEAL strictly finitarily dominates every policy with `s < 1`. -/
theorem strictly_dominated (π : ValidCausalPolicy Action Outcome) (hs : π.1 [] 0 < 1) :
    CausalFinitaryDominates response revealPolicy π ∧
      ¬ CausalFinitaryDominates response π revealPolicy := by
  have hgreat := (causalNativelySufficient_iff_finitarilyGreatest response response_valid
    revealPolicy).1 revealPolicy_nativelySufficient
  refine ⟨hgreat π, ?_⟩
  intro hback
  apply not_nativelySufficient π hs
  apply (causalNativelySufficient_iff_finitarilyGreatest response response_valid π).2
  intro ρ
  exact causalFinitaryDominates_trans response response_valid hback (hgreat ρ)

/-! ## The strict score gap -/

/-- Expected SAMPLE replay gain in bits. -/
def sampleGainBits : ℝ :=
  Real.logb 2 (41/25) + (41/50) * Real.logb 2 (1825/1681) + (9/50) * Real.logb 2 (25/9)

/-- The integer certificate, by direct integer arithmetic. -/
theorem integer_certificate : (2:ℕ)^50 * 3^18 * 41^32 < 73^41 := by norm_num

theorem sampleGainBits_gt_one : 1 < sampleGainBits := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hprod : (41/25 : ℝ)^50 * (1825/1681)^41 * (25/9)^9 = 73^41 / (3^18 * 41^32) := by
    norm_num
  have hcert : ((2:ℝ))^50 < (41/25 : ℝ)^50 * (1825/1681)^41 * (25/9)^9 := by
    rw [hprod, lt_div_iff₀ (by positivity)]
    exact_mod_cast (show (2:ℕ)^50 * (3^18 * 41^32) < 73^41 by
      simp only [← mul_assoc]; exact integer_certificate)
  have hlog := Real.log_lt_log (by positivity) hcert
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  unfold sampleGainBits Real.logb
  rw [← sub_pos]
  have : Real.log (41/25) / Real.log 2 + 41/50 * (Real.log (1825/1681) / Real.log 2) +
      9/50 * (Real.log (25/9) / Real.log 2) - 1 =
      ((50 * Real.log (41/25) + 41 * Real.log (1825/1681) + 9 * Real.log (25/9)) -
        50 * Real.log 2) / (50 * Real.log 2) := by
    field_simp
  rw [this]
  apply div_pos _ (by positivity)
  push_cast at hlog
  linarith

/-! ## Exact Bayesian replay prediction gain -/

/-- The paper's uniform prior on the two transition models. -/
def prior : World → ℝ := fun _ => 1/2

/-- Actual Bayesian posterior over the two transition models after a retained
record. The world-independent policy factor of the record likelihood cancels
on every positive-probability record and is omitted. -/
def posterior (h : History) : World → ℝ :=
  finiteBayesPosterior prior (fun θ h => causalResponseProb (response θ) h) h

/-- The replay score `eq:bayesian-replay-gain`. With likelihoods
`L θ = Q_θ(o | h,a)`, current posterior `q = posterior h`, predictive
probability `z = ∑ q L` and updated posterior `p = posterior (h ++ [(a,o)])`,
it is `log₂ ((∑ p L) / z)`. At null predictive probability Lean's total
division gives `0`; such points carry zero expected weight. -/
def replayGain (h : History) (a : Action) (o : Outcome) : ℝ :=
  Real.logb 2 ((∑ θ, posterior (h ++ [(a, o)]) θ * response θ h a o) /
    ∑ θ, posterior h θ * response θ h a o)

/-- The updated posterior is Bayes' rule `p = q L / z` applied to the current
posterior, whenever the predictive probability is positive. -/
theorem posterior_append (h : History) (a : Action) (o : Outcome) (θ : World)
    (hz : ∑ c, posterior h c * response c h a o ≠ 0) :
    posterior (h ++ [(a, o)]) θ =
      posterior h θ * response θ h a o / ∑ c, posterior h c * response c h a o := by
  have hN : (∑ c, prior c * causalResponseProb (response c) h) ≠ 0 := by
    intro hN0; apply hz
    simp only [posterior, finiteBayesPosterior, hN0, div_zero, zero_mul, sum_const_zero]
  have hsum : ∑ c, posterior h c * response c h a o =
      (∑ c, prior c * (causalResponseProb (response c) h * response c h a o)) /
        ∑ c, prior c * causalResponseProb (response c) h := by
    rw [sum_div]; apply sum_congr rfl; intro c _
    simp only [posterior, finiteBayesPosterior]; ring
  have hS : ∑ c, prior c * (causalResponseProb (response c) h * response c h a o) ≠ 0 := by
    intro hS; apply hz; rw [hsum, hS, zero_div]
  have hS' : ∑ x, prior x * causalResponseProb (response x) h * response x h a o ≠ 0 := by
    simpa only [mul_assoc] using hS
  rw [hsum, eq_div_iff (div_ne_zero hS hN)]
  simp only [posterior, finiteBayesPosterior, causalResponseProb_append]
  field_simp

theorem posterior_nonneg (h : History) (θ : World) : 0 ≤ posterior h θ :=
  finiteBayesPosterior_nonneg _ _ (fun _ => by norm_num [prior])
    (fun θ h => causalResponseProbFrom_nonneg _ (response_valid θ) _ _) h θ

/-- At positive predictive probability, the replay score equals the other two
displayed forms of `eq:bayesian-replay-gain` in this two-world model: the
squared-likelihood form and the order-two Rényi form over the supported
worlds. -/
theorem replayGain_eq_sq_form (h : History) (a : Action) (o : Outcome)
    (hz : ∑ θ, posterior h θ * response θ h a o ≠ 0) :
    replayGain h a o = Real.logb 2 ((∑ θ, posterior h θ * response θ h a o ^ 2) /
      (∑ θ, posterior h θ * response θ h a o) ^ 2) := by
  unfold replayGain
  congr 1
  simp only [posterior_append h a o _ hz, sum_div]
  apply sum_congr rfl; intro θ _
  field_simp

theorem replayGain_eq_renyi_form (h : History) (a : Action) (o : Outcome)
    (hz : ∑ θ, posterior h θ * response θ h a o ≠ 0) :
    replayGain h a o = Real.logb 2 (∑ θ ∈ univ.filter (fun θ => 0 < posterior h θ),
      posterior (h ++ [(a, o)]) θ ^ 2 / posterior h θ) := by
  rw [replayGain_eq_sq_form h a o hz, sum_filter]
  congr 1
  rw [sum_div]
  apply sum_congr rfl; intro θ _
  split_ifs with hq
  · rw [posterior_append h a o θ hz]
    field_simp
  · have : posterior h θ = 0 := le_antisymm (not_lt.mp hq) (posterior_nonneg h θ)
    simp [this]

/-- At positive predictive probability the current posterior is a probability
vector. -/
theorem posterior_sum_eq_one (h : History) (a : Action) (o : Outcome)
    (hz : ∑ θ, posterior h θ * response θ h a o ≠ 0) : ∑ θ, posterior h θ = 1 := by
  have hN : (∑ c, prior c * causalResponseProb (response c) h) ≠ 0 := by
    intro hN0; apply hz
    simp only [posterior, finiteBayesPosterior, hN0, div_zero, zero_mul, sum_const_zero]
  simp only [posterior, finiteBayesPosterior, ← sum_div]
  exact div_self hN

/-- The replay score is a nonnegative reward at every record, action and
response (Cauchy--Schwarz in the squared-likelihood form; `0` at null
predictive probability). Hence the paper's complete return, defined for
nonnegative rewards as the limit of the finite returns, applies. -/
theorem replayGain_nonneg (h : History) (a : Action) (o : Outcome) :
    0 ≤ replayGain h a o := by
  by_cases hz : ∑ θ, posterior h θ * response θ h a o = 0
  · simp [replayGain, hz]
  · rw [replayGain_eq_sq_form h a o hz]
    apply Real.logb_nonneg (by norm_num)
    have hz2 : 0 < (∑ θ, posterior h θ * response θ h a o) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hz))
    rw [le_div_iff₀ hz2, one_mul]
    have hq := posterior_sum_eq_one h a o hz
    have hq0 := posterior_nonneg h 0
    have hq1 := posterior_nonneg h 1
    simp only [Fin.sum_univ_two] at hq ⊢
    set q0 := posterior h 0
    set q1 := posterior h 1
    set L0 := response 0 h a o
    set L1 := response 1 h a o
    have key : q0 * L0 ^ 2 + q1 * L1 ^ 2 - (q0 * L0 + q1 * L1) ^ 2 =
        q0 * q1 * (L0 - L1) ^ 2 + (1 - (q0 + q1)) * (q0 * L0 ^ 2 + q1 * L1 ^ 2) := by
      ring
    rw [hq, sub_self, zero_mul, add_zero] at key
    nlinarith [mul_nonneg (mul_nonneg hq0 hq1) (sq_nonneg (L0 - L1))]

theorem causalResponseProb_nil (Q : CausalResponse Action Outcome) :
    causalResponseProb Q [] = 1 := rfl

theorem causalResponseProb_singleton (Q : CausalResponse Action Outcome)
    (x : Action × Outcome) : causalResponseProb Q [x] = Q [] x.1 x.2 := by
  simp [causalResponseProb, causalResponseProbFrom]

theorem causalResponseProb_pair (Q : CausalResponse Action Outcome)
    (x y : Action × Outcome) : causalResponseProb Q [x, y] = Q [] x.1 x.2 * Q [x] y.1 y.2 := by
  simp [causalResponseProb, causalResponseProbFrom]

@[simp] theorem response_singleton (θ : World) (x : Action × Outcome) (a : Action)
    (o : Outcome) : response θ [x] a o = next θ (some x.2) a o := by
  simpa using response_append θ [] x a o

theorem posterior_nil (θ : World) : posterior [] θ = 1/2 := by
  simp [posterior, finiteBayesPosterior, causalResponseProb_nil, prior]

/-- A likelihood constant across the two worlds gives zero replay gain. -/
theorem replayGain_eq_zero_of_const (h : History) (a : Action) (o : Outcome) (c : ℝ)
    (hc : ∀ θ, response θ h a o = c) : replayGain h a o = 0 := by
  unfold replayGain
  simp only [hc]
  by_cases hc0 : c = 0
  · simp [hc0]
  · have hp (θ : World) : posterior (h ++ [(a, o)]) θ = posterior h θ := by
      simp only [posterior, finiteBayesPosterior, causalResponseProb_append, hc]
      rw [show ∑ c', prior c' * (causalResponseProb (response c') h * c) =
          (∑ c', prior c' * causalResponseProb (response c') h) * c by
            rw [sum_mul]; apply sum_congr rfl; intro c' _; ring,
        show prior θ * (causalResponseProb (response θ) h * c) =
          prior θ * causalResponseProb (response θ) h * c by ring,
        mul_div_mul_right _ _ hc0]
    simp only [hp]
    by_cases hz : ∑ θ, posterior h θ * c = 0
    · simp [hz]
    · rw [div_self hz, Real.logb_one]

/-- Off START the encoded action label does not change the replay score. -/
theorem replayGain_action (h : History) (hh : h ≠ []) (a : Action) (o : Outcome) :
    replayGain h a o = replayGain h 0 o := by
  have hr (θ : World) (b : Action) : response θ h b o = response θ h 0 o := by
    simp only [response_eq_next, currentState, if_neg hh]; rfl
  have hp (θ : World) : posterior (h ++ [(a, o)]) θ = posterior (h ++ [(0, o)]) θ := by
    simp only [posterior, finiteBayesPosterior, causalResponseProb_append, hr]
  simp only [replayGain, hp, hr]

theorem gain_root_reveal (b : Fin 2) : replayGain [] 0 (0, b) = 1 := by
  have h : (∑ θ, posterior ([] ++ [((0 : Action), ((0, b) : Outcome))]) θ *
      response θ [] 0 (0, b)) / ∑ θ, posterior [] θ * response θ [] 0 (0, b) = 2 := by
    fin_cases b <;>
      simp [posterior, finiteBayesPosterior, causalResponseProb_singleton,
        causalResponseProb_nil, prior, next]
  rw [replayGain, h, Real.logb_self_eq_one (by norm_num)]

theorem gain_root_sample (y : Fin 2) : replayGain [] 1 (1, y) = Real.logb 2 (41/25) := by
  have h : (∑ θ, posterior ([] ++ [((1 : Action), ((1, y) : Outcome))]) θ *
      response θ [] 1 (1, y)) / ∑ θ, posterior [] θ * response θ [] 1 (1, y) = 41/25 := by
    fin_cases y <;>
      simp [posterior, finiteBayesPosterior, causalResponseProb_singleton,
        causalResponseProb_nil, prior, next, noisy, Fin.sum_univ_two] <;> norm_num
  rw [replayGain, h]

theorem gain_after_reveal (b : Fin 2) : replayGain [(0, (0, b))] 0 (0, b) = 0 := by
  apply replayGain_eq_zero_of_const _ _ _ 1
  intro θ
  simp [next]

theorem gain_agree (y : Fin 2) :
    replayGain [(1, (1, y))] 0 (2, y) = Real.logb 2 (1825/1681) := by
  have h : (∑ θ, posterior ([((1 : Action), ((1, y) : Outcome))] ++ [(0, (2, y))]) θ *
      response θ [(1, (1, y))] 0 (2, y)) /
      ∑ θ, posterior [(1, (1, y))] θ * response θ [(1, (1, y))] 0 (2, y) = 1825/1681 := by
    fin_cases y <;>
      simp [posterior, finiteBayesPosterior, causalResponseProb_singleton,
        causalResponseProb_pair, prior, next, noisy, Fin.sum_univ_two] <;> norm_num
  rw [replayGain, h]

theorem gain_disagree (y z : Fin 2) (hyz : y ≠ z) :
    replayGain [(1, (1, y))] 0 (2, z) = Real.logb 2 (25/9) := by
  have h : (∑ θ, posterior ([((1 : Action), ((1, y) : Outcome))] ++ [(0, (2, z))]) θ *
      response θ [(1, (1, y))] 0 (2, z)) /
      ∑ θ, posterior [(1, (1, y))] θ * response θ [(1, (1, y))] 0 (2, z) = 25/9 := by
    fin_cases y <;> fin_cases z <;> simp at hyz <;>
      simp [posterior, finiteBayesPosterior, causalResponseProb_singleton,
        causalResponseProb_pair, prior, next, noisy, Fin.sum_univ_two] <;> norm_num
  rw [replayGain, h]

/-- Expected replay gain of the next transition in world `θ`. -/
def localGain (π : CausalPolicy Action Outcome) (θ : World) (h : History) : ℝ :=
  ∑ a, π h a * ∑ o, response θ h a o * replayGain h a o

/-- Expected replay gain of transition `u+1` in world `θ`. -/
def worldStage (π : ValidCausalPolicy Action Outcome) (θ : World) (u : ℕ) : ℝ :=
  ∑ w : CausalFiniteTrace Action Outcome u,
    causalFiniteExperiment π.1 response u θ w * localGain π.1 θ (List.ofFn w)

/-- Prior-averaged expected replay gain of transition `u+1`. -/
def stageGain (π : ValidCausalPolicy Action Outcome) (u : ℕ) : ℝ :=
  ∑ θ, prior θ * worldStage π θ u

/-- Expected replay-prediction-gain return over the first `H` transitions. -/
def horizonReturn (π : ValidCausalPolicy Action Outcome) (H : ℕ) : ℝ :=
  ∑ u ∈ range H, stageGain π u

/-- Complete undiscounted expected replay-prediction-gain return. -/
def completeReturn (π : ValidCausalPolicy Action Outcome) : ℝ :=
  ∑' u, stageGain π u

theorem sum_outcome (f : Outcome → ℝ) :
    ∑ o, f o = f (0, 0) + f (0, 1) + f (1, 0) + f (1, 1) + f (2, 0) + f (2, 1) := by
  simp [Fintype.sum_prod_type, Fin.sum_univ_three]
  ring

theorem localGain_of_ne_nil (π : ValidCausalPolicy Action Outcome) (θ : World) (h : History)
    (hh : h ≠ []) :
    localGain π.1 θ h = ∑ o, response θ h 0 o * replayGain h 0 o := by
  have hr (b : Action) (o : Outcome) : response θ h b o = response θ h 0 o := by
    simp only [response_eq_next, currentState, if_neg hh]; rfl
  simp only [localGain, hr, replayGain_action h hh]
  rw [← sum_mul, (π.2 h).2, one_mul]

theorem root_reveal_sum (θ : World) :
    ∑ o, next θ none 0 o * replayGain [] 0 o = 1 := by
  rw [sum_outcome]
  fin_cases θ <;> simp [next, gain_root_reveal]

theorem root_sample_sum (θ : World) :
    ∑ o, next θ none 1 o * replayGain [] 1 o = Real.logb 2 (41/25) := by
  rw [sum_outcome]
  fin_cases θ <;> simp [next, noisy, gain_root_sample] <;> ring

theorem worldStage_zero (π : ValidCausalPolicy Action Outcome) (θ : World) :
    worldStage π θ 0 = π.1 [] 0 + (1 - π.1 [] 0) * Real.logb 2 (41/25) := by
  have hw : worldStage π θ 0 = localGain π.1 θ [] := by
    simp [worldStage, causalFiniteExperiment, causalTraceProb, causalTraceProbFrom]
  rw [hw, localGain, Fin.sum_univ_two]
  simp only [response_nil, root_reveal_sum, root_sample_sum, policy_root_other]
  ring

theorem localGain_after_reveal (π : ValidCausalPolicy Action Outcome) (θ b : Fin 2) :
    localGain π.1 θ [(0, (0, b))] = 0 := by
  rw [localGain_of_ne_nil π θ _ (by simp), sum_outcome]
  fin_cases θ <;> fin_cases b <;> simp [next, gain_after_reveal]

theorem localGain_after_sample (π : ValidCausalPolicy Action Outcome) (θ y : Fin 2) :
    localGain π.1 θ [(1, (1, y))] =
      noisy θ y * Real.logb 2 (1825/1681) + (1 - noisy θ y) * Real.logb 2 (25/9) := by
  rw [localGain_of_ne_nil π θ _ (by simp), sum_outcome]
  have hd01 := gain_disagree 0 1 (by decide)
  have hd10 := gain_disagree 1 0 (by decide)
  fin_cases θ <;> fin_cases y <;> simp [next, noisy, gain_agree, hd01, hd10] <;> norm_num <;> ring

theorem worldStage_one (π : ValidCausalPolicy Action Outcome) (θ : World) :
    worldStage π θ 1 = (1 - π.1 [] 0) *
      ((41/50) * Real.logb 2 (1825/1681) + (9/50) * Real.logb 2 (25/9)) := by
  have hw : worldStage π θ 1 = ∑ x : Action × Outcome,
      π.1 [] x.1 * next θ none x.1 x.2 * localGain π.1 θ [x] := by
    unfold worldStage
    rw [← (Equiv.funUnique (Fin 1) (Action × Outcome)).symm.sum_comp]
    apply sum_congr rfl; intro x _
    simp [causalFiniteExperiment, causalTraceProb, causalTraceProbFrom]
  rw [hw, Fintype.sum_prod_type, Fin.sum_univ_two, sum_outcome, sum_outcome]
  rw [policy_root_other]
  fin_cases θ <;>
    simp [next, noisy, localGain_after_reveal, localGain_after_sample] <;> ring

theorem worldStage_add_two (π : ValidCausalPolicy Action Outcome) (θ : World) (u : ℕ) :
    worldStage π θ (u + 2) = 0 := by
  apply sum_eq_zero
  intro w _
  by_cases hK : causalFiniteExperiment π.1 response (u + 2) θ w = 0
  · rw [hK, zero_mul]
  · have hR : causalResponseProb (response θ) (List.ofFn w) ≠ 0 := by
      intro hR; apply hK
      unfold causalFiniteExperiment
      rw [causalTraceProb_factor, hR, mul_zero]
    have hlen : 2 ≤ (List.ofFn w).length := by simp
    have hh : List.ofFn w ≠ [] := by simp
    have hx := lastObs_ne_U_of_support θ _ hlen hR
    have hg (a : Action) (o : Outcome) : replayGain (List.ofFn w) a o = 0 :=
      replayGain_eq_zero_of_const _ a o (stay (List.ofFn w) a o)
        (fun θ' => response_eq_stay θ' _ a o hh hx)
    simp only [localGain, hg, mul_zero, sum_const_zero]

theorem stageGain_of_world (π : ValidCausalPolicy Action Outcome) (u : ℕ) (c : ℝ)
    (hc : ∀ θ, worldStage π θ u = c) : stageGain π u = c := by
  simp [stageGain, hc, prior]

theorem stageGain_zero (π : ValidCausalPolicy Action Outcome) :
    stageGain π 0 = π.1 [] 0 + (1 - π.1 [] 0) * Real.logb 2 (41/25) :=
  stageGain_of_world π 0 _ (worldStage_zero π)

theorem stageGain_one (π : ValidCausalPolicy Action Outcome) :
    stageGain π 1 = (1 - π.1 [] 0) *
      ((41/50) * Real.logb 2 (1825/1681) + (9/50) * Real.logb 2 (25/9)) :=
  stageGain_of_world π 1 _ (worldStage_one π)

theorem stageGain_add_two (π : ValidCausalPolicy Action Outcome) (u : ℕ) :
    stageGain π (u + 2) = 0 :=
  stageGain_of_world π (u + 2) 0 (fun θ => worldStage_add_two π θ u)

theorem twoStage_value (π : ValidCausalPolicy Action Outcome) :
    stageGain π 0 + stageGain π 1 = π.1 [] 0 + (1 - π.1 [] 0) * sampleGainBits := by
  rw [stageGain_zero, stageGain_one, sampleGainBits]
  ring

/-- Every finite horizon `H ≥ 2` has expected return `s + (1-s) A`. -/
theorem horizonReturn_eq (π : ValidCausalPolicy Action Outcome) {H : ℕ} (hH : 2 ≤ H) :
    horizonReturn π H = π.1 [] 0 + (1 - π.1 [] 0) * sampleGainBits := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hH
  rw [horizonReturn, sum_range_add]
  have htail : ∑ x ∈ range k, stageGain π (2 + x) = 0 := by
    apply sum_eq_zero; intro x _
    rw [add_comm]; exact stageGain_add_two π x
  rw [htail, add_zero, sum_range_succ, sum_range_one, twoStage_value]

/-- The complete undiscounted sum is identical: all later gains vanish. -/
theorem completeReturn_eq (π : ValidCausalPolicy Action Outcome) :
    completeReturn π = π.1 [] 0 + (1 - π.1 [] 0) * sampleGainBits := by
  rw [completeReturn, tsum_eq_sum (s := range 2)]
  · rw [sum_range_succ, sum_range_one, twoStage_value]
  · intro u hu
    simp only [mem_range, not_lt] at hu
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hu
    rw [add_comm]; exact stageGain_add_two π k

theorem localGain_nonneg (π : ValidCausalPolicy Action Outcome) (θ : World) (h : History) :
    0 ≤ localGain π.1 θ h :=
  sum_nonneg fun a _ => mul_nonneg ((π.2 h).1 a)
    (sum_nonneg fun o _ => mul_nonneg ((response_valid θ h a).1 o) (replayGain_nonneg h a o))

/-- Every expected stage gain is nonnegative. -/
theorem stageGain_nonneg (π : ValidCausalPolicy Action Outcome) (u : ℕ) :
    0 ≤ stageGain π u :=
  sum_nonneg fun θ _ => mul_nonneg (by norm_num [prior])
    (sum_nonneg fun w _ => mul_nonneg
      ((causalFiniteExperiment_valid π.1 π.2 response response_valid u θ).1 w)
      (localGain_nonneg π θ _))

/-- `completeReturn` is the paper's complete return
`lim_{H → ∞} E ∑_{u=1}^H r_u`: the finite returns converge to it (they are
constant from `H = 2` on). -/
theorem horizonReturn_tendsto (π : ValidCausalPolicy Action Outcome) :
    Tendsto (fun H => horizonReturn π H) atTop (𝓝 (completeReturn π)) := by
  rw [completeReturn_eq]
  exact tendsto_atTop_of_eventually_const (i₀ := 2) fun H hH => horizonReturn_eq π hH

/-! ## Every maximizer chooses the two noisy readings -/

theorem value_le_iff {s s' : ℝ} :
    s' + (1 - s') * sampleGainBits ≤ s + (1 - s) * sampleGainBits ↔ s ≤ s' := by
  have hA := sampleGainBits_gt_one
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

theorem maximizer_iff_of_value (J : ValidCausalPolicy Action Outcome → ℝ)
    (hJ : ∀ ρ, J ρ = ρ.1 [] 0 + (1 - ρ.1 [] 0) * sampleGainBits)
    (P : ValidCausalPolicy Action Outcome → Prop) (hsample : P samplePolicy)
    (π : ValidCausalPolicy Action Outcome) :
    (∀ ρ, P ρ → J ρ ≤ J π) ↔ π.1 [] 0 = 0 := by
  constructor
  · intro hmax
    have h := hmax samplePolicy hsample
    rw [hJ, hJ, value_le_iff, samplePolicy_root] at h
    exact le_antisymm h (policy_root_bounds π).1
  · intro hs ρ _
    rw [hJ, hJ, value_le_iff, hs]
    exact (policy_root_bounds ρ).1

/-- Over every valid randomized history policy, the maximizers of each finite
horizon `H ≥ 2` are exactly the policies with `s = 0`. -/
theorem horizon_maximizer_iff {H : ℕ} (hH : 2 ≤ H) (π : ValidCausalPolicy Action Outcome) :
    (∀ ρ, horizonReturn ρ H ≤ horizonReturn π H) ↔ π.1 [] 0 = 0 := by
  simpa using maximizer_iff_of_value (fun ρ => horizonReturn ρ H)
    (fun ρ => horizonReturn_eq ρ hH) (fun _ => True) trivial π

theorem complete_maximizer_iff (π : ValidCausalPolicy Action Outcome) :
    (∀ ρ, completeReturn ρ ≤ completeReturn π) ↔ π.1 [] 0 = 0 := by
  simpa using maximizer_iff_of_value completeReturn completeReturn_eq
    (fun _ => True) trivial π

/-- The same characterization within the legal policies. -/
theorem legal_horizon_maximizer_iff {H : ℕ} (hH : 2 ≤ H)
    (π : ValidCausalPolicy Action Outcome) :
    (∀ ρ, Legal ρ → horizonReturn ρ H ≤ horizonReturn π H) ↔ π.1 [] 0 = 0 :=
  maximizer_iff_of_value (fun ρ => horizonReturn ρ H) (fun ρ => horizonReturn_eq ρ hH)
    Legal samplePolicy_legal π

theorem legal_complete_maximizer_iff (π : ValidCausalPolicy Action Outcome) :
    (∀ ρ, Legal ρ → completeReturn ρ ≤ completeReturn π) ↔ π.1 [] 0 = 0 :=
  maximizer_iff_of_value completeReturn completeReturn_eq Legal samplePolicy_legal π

/-- A maximizer is attained by the legal SAMPLE policy. -/
theorem samplePolicy_maximizes {H : ℕ} (hH : 2 ≤ H) :
    (∀ ρ, horizonReturn ρ H ≤ horizonReturn samplePolicy H) ∧
      ∀ ρ, completeReturn ρ ≤ completeReturn samplePolicy :=
  ⟨(horizon_maximizer_iff hH samplePolicy).2 samplePolicy_root,
    (complete_maximizer_iff samplePolicy).2 samplePolicy_root⟩

/-- Consequences for a policy with `s = 0`: permanent and eventual native
REVEAL deficiency `1/10`, and strict domination by REVEAL. -/
theorem sampling_native_loss (π : ValidCausalPolicy Action Outcome) (hs : π.1 [] 0 = 0) :
    (∀ t, 2 ≤ t →
      finiteDeficiency (causalFiniteExperiment π.1 response t) nativeReveal = 1/10) ∧
    eventualDeficiency π = 1/10 ∧
    CausalFinitaryDominates response revealPolicy π ∧
      ¬ CausalFinitaryDominates response π revealPolicy := by
  refine ⟨fun t ht => by rw [native_deficiency π ht, hs]; norm_num, ?_, ?_⟩
  · rw [eventualDeficiency_eq, hs]; norm_num
  · exact strictly_dominated π (by rw [hs]; norm_num)

/-- **Prediction gain prefers two noisy readings.** Every maximizer of the
expected replay-prediction-gain return over a finite horizon `H ≥ 2` is
strictly dominated by REVEAL and has permanent and eventual native REVEAL
deficiency `1/10`. -/
theorem horizon_maximizer_native_loss {H : ℕ} (hH : 2 ≤ H)
    (π : ValidCausalPolicy Action Outcome)
    (hmax : ∀ ρ, horizonReturn ρ H ≤ horizonReturn π H) :
    (∀ t, 2 ≤ t →
      finiteDeficiency (causalFiniteExperiment π.1 response t) nativeReveal = 1/10) ∧
    eventualDeficiency π = 1/10 ∧
    CausalFinitaryDominates response revealPolicy π ∧
      ¬ CausalFinitaryDominates response π revealPolicy :=
  sampling_native_loss π ((horizon_maximizer_iff hH π).1 hmax)

/-- The same conclusion for the complete undiscounted return. -/
theorem complete_maximizer_native_loss (π : ValidCausalPolicy Action Outcome)
    (hmax : ∀ ρ, completeReturn ρ ≤ completeReturn π) :
    (∀ t, 2 ≤ t →
      finiteDeficiency (causalFiniteExperiment π.1 response t) nativeReveal = 1/10) ∧
    eventualDeficiency π = 1/10 ∧
    CausalFinitaryDominates response revealPolicy π ∧
      ¬ CausalFinitaryDominates response π revealPolicy :=
  sampling_native_loss π ((complete_maximizer_iff π).1 hmax)

/-- Legal-policy versions: maximizing among legal policies forces `s = 0`. -/
theorem legal_horizon_maximizer_native_loss {H : ℕ} (hH : 2 ≤ H)
    (π : ValidCausalPolicy Action Outcome)
    (hmax : ∀ ρ, Legal ρ → horizonReturn ρ H ≤ horizonReturn π H) :
    (∀ t, 2 ≤ t →
      finiteDeficiency (causalFiniteExperiment π.1 response t) nativeReveal = 1/10) ∧
    eventualDeficiency π = 1/10 ∧
    CausalFinitaryDominates response revealPolicy π ∧
      ¬ CausalFinitaryDominates response π revealPolicy :=
  sampling_native_loss π ((legal_horizon_maximizer_iff hH π).1 hmax)

theorem legal_complete_maximizer_native_loss (π : ValidCausalPolicy Action Outcome)
    (hmax : ∀ ρ, Legal ρ → completeReturn ρ ≤ completeReturn π) :
    (∀ t, 2 ≤ t →
      finiteDeficiency (causalFiniteExperiment π.1 response t) nativeReveal = 1/10) ∧
    eventualDeficiency π = 1/10 ∧
    CausalFinitaryDominates response revealPolicy π ∧
      ¬ CausalFinitaryDominates response π revealPolicy :=
  sampling_native_loss π ((legal_complete_maximizer_iff π).1 hmax)

end
end PredictionGainNoisyReadings
end IdExp
