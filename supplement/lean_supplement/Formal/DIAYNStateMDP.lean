import Formal.ControlEntropy
import Formal.RewardProcessWitness
import Formal.DeterministicDeficiency

/-! A fully observed absorbing MDP for the stationary, state-based DIAYN objective.
The unknown world determines READ's absorbing state. LABEL actions select
world-independent absorbing states. All three actions remain available forever.
The stationary law below is proved to be the actual limiting law from `none`. -/
namespace IdExp.DIAYNState
open Finset Filter
open scoped Topology
noncomputable section

abbrev World := Fin 2
abbrev Skill := Fin 2
abbrev Action := Fin 3
abbrev State := Option (World ⊕ Skill)
abbrev History := CausalHistory Action State

/-- READ is zero; the two successors are LABEL0 and LABEL1. -/
def branch (θ : World) : Action → State :=
  Fin.cases (some (Sum.inl θ)) (fun z => some (Sum.inr z))

@[simp] theorem branch_zero (θ : World) : branch θ 0 = some (Sum.inl θ) := rfl
@[simp] theorem branch_succ (θ : World) (z : Skill) :
    branch θ z.succ = some (Sum.inr z) := rfl
@[simp] theorem branch_ne_none (θ : World) (a : Action) : branch θ a ≠ none := by
  refine Fin.cases ?_ (fun z => ?_) a <;> simp

/-- The chosen initial action is recoverable from the observed state without
knowing the world; READ outcomes retain their world label as well. -/
def actionOfState : State → Action
  | none => 0
  | some (Sum.inl _) => 0
  | some (Sum.inr z) => z.succ

@[simp] theorem actionOfState_branch (θ : World) (a : Action) :
    actionOfState (branch θ a) = a := by
  refine Fin.cases ?_ (fun z => ?_) a <;> rfl

theorem branch_injective (θ : World) : Function.Injective (branch θ) :=
  Function.LeftInverse.injective (actionOfState_branch θ)

def point (s : State) (x : State) : ℝ := if x = s then 1 else 0
def transition (θ : World) : State → Action → State → ℝ
  | none, a => point (branch θ a)
  | some b, _ => point (some b)

theorem point_valid (s : State) : IsDist (point s) := by
  constructor
  · intro x; unfold point; split_ifs <;> norm_num
  · simp [point]
theorem transition_valid (θ : World) (s : State) (a : Action) :
    IsDist (transition θ s a) := by
  cases s with
  | none => exact point_valid (branch θ a)
  | some b => exact point_valid (some b)

/-- Actual current state, observed after each transition. -/
def currentState (h : History) : State := ((h.getLast?).map Prod.snd).getD none
@[simp] theorem currentState_nil : currentState [] = none := rfl
@[simp] theorem currentState_append (h : History) (ao : Action × State) :
    currentState (h ++ [ao]) = ao.2 := by simp [currentState]
def response (θ : World) : CausalResponse Action State :=
  fun h a => transition θ (currentState h) a
theorem response_valid (θ : World) : IsCausalResponse (response θ) :=
  fun h a => transition_valid θ (currentState h) a

/-- Stationary randomized policies, conditioned on a skill. -/
abbrev Policy := Skill → State → {p : Action → ℝ // IsDist p}
def causalPolicy (P : Policy) (z : Skill) : ValidCausalPolicy Action State :=
  ⟨fun h => (P z (currentState h)).1, fun h => (P z (currentState h)).2⟩
def rootExperiment (P : Policy) : FiniteExperiment Skill Action :=
  fun z a => (P z none).1 a
def stateExperiment (P : Policy) (θ : World) : FiniteExperiment Skill State :=
  finiteDecisionLaw (rootExperiment P) (diracExp (branch θ))

theorem rootExperiment_valid (P : Policy) : IsFiniteExperiment (rootExperiment P) :=
  fun z => (P z none).2
theorem stateExperiment_valid (P : Policy) (θ : World) :
    IsFiniteExperiment (stateExperiment P θ) :=
  finiteDecisionLaw_valid _ (rootExperiment_valid P) _
    (fun a _ => diracExp_valid (branch θ) a)

@[simp] theorem stateExperiment_none (P : Policy) (θ : World) (z : Skill) :
    stateExperiment P θ z none = 0 := by
  have hn (a : Action) : none ≠ branch θ a := (branch_ne_none θ a).symm
  simp [stateExperiment, finiteDecisionLaw, diracExp_apply, hn]

theorem stateExperiment_branch (P : Policy) (θ : World) (z : Skill) (a : Action) :
    stateExperiment P θ z (branch θ a) = rootExperiment P z a := by
  simp [stateExperiment, finiteDecisionLaw, diracExp_apply, (branch_injective θ).eq_iff]

theorem stateExperiment_decode (P : Policy) (θ : World) :
    finiteDecisionLaw (stateExperiment P θ) (diracExp actionOfState) = rootExperiment P := by
  funext z a
  unfold stateExperiment finiteDecisionLaw
  simp_rw [sum_mul]
  rw [sum_comm]
  simp_rw [mul_assoc, ← mul_sum]
  have hd (x : Action) :
      (∑ s : State, diracExp (branch θ) x s * diracExp actionOfState s a) =
        diracExp actionOfState (branch θ x) a := by
    exact congrFun (finiteDecisionLaw_diracExp (branch θ) (diracExp actionOfState) x) a
  simp_rw [hd, diracExp_apply, actionOfState_branch]
  simp

/-- Actual state marginal of the full policy-induced record, for arbitrary
history-dependent randomized policies, including policies outside `Policy`. -/
def stateMarginal (π : ValidCausalPolicy Action State) (θ : World) (t : ℕ)
    (s : State) : ℝ :=
  ∑ w : CausalFiniteTrace Action State t,
    causalFiniteExperiment π.1 response t θ w *
      (if currentState (List.ofFn w) = s then 1 else 0)

theorem tail_state (π : CausalPolicy Action State) (θ : World)
    (pre rest : History) (b : World ⊕ Skill) (hpre : currentState pre = some b)
    (hne : causalTraceProbFrom π (response θ) pre rest ≠ 0) :
    currentState (pre ++ rest) = some b := by
  induction rest generalizing pre with
  | nil => simpa using hpre
  | cons ao rest ih =>
    have ho : ao.2 = some b := by
      by_contra hn
      apply hne
      simp [causalTraceProbFrom, response, hpre, transition, point, hn]
    have hr : causalTraceProbFrom π (response θ) (pre ++ [ao]) rest ≠ 0 := by
      intro hz; apply hne; simp [causalTraceProbFrom, hz]
    simpa [List.append_assoc] using ih (pre ++ [ao]) (by simpa using ho) hr

theorem tail_state_of_ne_none (π : CausalPolicy Action State) (θ : World)
    (pre rest : History) (s : State) (hs : s ≠ none) (hpre : currentState pre = s)
    (hne : causalTraceProbFrom π (response θ) pre rest ≠ 0) :
    currentState (pre ++ rest) = s := by
  cases s with
  | none => exact False.elim (hs rfl)
  | some b => exact tail_state π θ pre rest b hpre hne

/-- Every positive-time supported record is already in the state selected by
its first action. No claim is made about impossible histories ending at `none`. -/
theorem supported_currentState_eq_branch (π : CausalPolicy Action State) (θ : World)
    (n : ℕ) (w : CausalFiniteTrace Action State (n+1))
    (hw : causalFiniteExperiment π response (n+1) θ w ≠ 0) :
    currentState (List.ofFn w) = branch θ (w 0).1 := by
  have hwlist : List.ofFn w = w 0 :: List.ofFn (Fin.tail w) := by
    simpa only [List.ofFn_cons] using congrArg List.ofFn (Fin.cons_self_tail w).symm
  have ho : (w 0).2 = branch θ (w 0).1 := by
    by_contra hn
    apply hw
    simp [causalFiniteExperiment, causalTraceProb, causalTraceProbFrom,
      response, transition, point, hn]
  have hr : causalTraceProbFrom π (response θ) [w 0] (List.ofFn (Fin.tail w)) ≠ 0 := by
    intro hz
    apply hw
    unfold causalFiniteExperiment causalTraceProb
    rw [hwlist]
    simp only [causalTraceProbFrom, List.nil_append]
    rw [hz]
    simp
  rw [hwlist]
  exact tail_state_of_ne_none π θ [w 0] (List.ofFn (Fin.tail w)) _
    (branch_ne_none θ _) (by simpa [currentState] using ho) hr

theorem supported_currentState_ne_none (π : CausalPolicy Action State) (θ : World)
    (n : ℕ) (w : CausalFiniteTrace Action State (n+1))
    (hw : causalFiniteExperiment π response (n+1) θ w ≠ 0) :
    currentState (List.ofFn w) ≠ none := by
  rw [supported_currentState_eq_branch π θ n w hw]
  exact branch_ne_none θ _

theorem tail_state_sum (π : ValidCausalPolicy Action State) (θ : World)
    (pre : History) (b : World ⊕ Skill) (hpre : currentState pre = some b) (n : ℕ)
    (s : State) :
    (∑ w : CausalFiniteTrace Action State n,
      causalTraceProbFrom π.1 (response θ) pre (List.ofFn w) *
        (if currentState (pre ++ List.ofFn w) = s then 1 else 0)) =
      if some b = s then 1 else 0 := by
  calc
    _ = ∑ w : CausalFiniteTrace Action State n,
        causalTraceProbFrom π.1 (response θ) pre (List.ofFn w) *
          (if some b = s then 1 else 0) := by
      apply sum_congr rfl
      intro w _
      by_cases hw : causalTraceProbFrom π.1 (response θ) pre (List.ofFn w) = 0
      · simp [hw]
      · rw [tail_state π.1 θ pre (List.ofFn w) b hpre hw]
    _ = _ := by
      rw [← sum_mul, sum_causalTraceProbFrom π.1 π.2 _ (response_valid θ), one_mul]

theorem tail_state_sum_of_ne_none (π : ValidCausalPolicy Action State) (θ : World)
    (pre : History) (b : State) (hb : b ≠ none) (hpre : currentState pre = b) (n : ℕ)
    (s : State) :
    (∑ w : CausalFiniteTrace Action State n,
      causalTraceProbFrom π.1 (response θ) pre (List.ofFn w) *
        (if currentState (pre ++ List.ofFn w) = s then 1 else 0)) =
      if b = s then 1 else 0 := by
  cases b with
  | none => exact False.elim (hb rfl)
  | some b => exact tail_state_sum π θ pre b hpre n s

@[simp] theorem stateMarginal_zero (π : ValidCausalPolicy Action State) (θ : World)
    (s : State) : stateMarginal π θ 0 s = point none s := by
  simp [stateMarginal, causalFiniteExperiment, causalTraceProb, causalTraceProbFrom,
    point, eq_comm]

theorem stateMarginal_succ (π : ValidCausalPolicy Action State) (θ : World) (n : ℕ)
    (s : State) :
    stateMarginal π θ (n+1) s = ∑ a, π.1 [] a * point (branch θ a) s := by
  unfold stateMarginal
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Action × State)).sum_comp]
  rw [Fintype.sum_prod_type]
  have hcons (ao : Action × State) (w : CausalFiniteTrace Action State n) :
      (Fin.consEquiv (fun _ : Fin (n+1) => Action × State)) (ao,w) = Fin.cons ao w := by
    funext i; exact Fin.consEquiv_apply _ _ i
  simp_rw [hcons, List.ofFn_cons]
  simp only [causalFiniteExperiment, causalTraceProb, List.ofFn_cons, causalTraceProbFrom,
    List.nil_append]
  simp_rw [mul_assoc, ← mul_sum]
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a _
  rw [sum_eq_single (branch θ a)]
  · have hs := tail_state_sum_of_ne_none π θ [(a, branch θ a)] (branch θ a)
      (branch_ne_none θ a) (by simp [currentState]) n s
    simp only [List.singleton_append] at hs
    rw [hs]
    simp [response, transition, point, eq_comm]
  · intro b _ hb
    simp [response, transition, point, hb]
  · simp

theorem policy_stateMarginal_succ (P : Policy) (z : Skill) (θ : World) (n : ℕ) :
    stateMarginal (causalPolicy P z) θ (n+1) = stateExperiment P θ z := by
  funext s
  rw [stateMarginal_succ]
  simp [causalPolicy, stateExperiment, finiteDecisionLaw, rootExperiment, point,
    diracExp_apply]

/-- Skill-conditioned one-step state kernel, with all actions available at
all five actual observed states. -/
def stateKernel (P : Policy) (z : Skill) (θ : World) (s s' : State) : ℝ :=
  ∑ a, (P z s).1 a * transition θ s a s'

theorem stateKernel_valid (P : Policy) (z : Skill) (θ : World) (s : State) :
    IsDist (stateKernel P z θ s) := by
  constructor
  · intro s'
    exact sum_nonneg fun a _ => mul_nonneg ((P z s).2.1 a)
      ((transition_valid θ s a).1 s')
  · unfold stateKernel
    rw [sum_comm]
    simp_rw [← mul_sum, (transition_valid θ s _).2, mul_one]
    exact (P z s).2.2

@[simp] theorem stateKernel_some (P : Policy) (z : Skill) (θ : World)
    (b : World ⊕ Skill) (s : State) :
    stateKernel P z θ (some b) s = point (some b) s := by
  simp only [stateKernel, transition, ← sum_mul, (P z (some b)).2.2, one_mul]

/-- Invariance is for the actual law selected from the specified root, not an
arbitrary invariant distribution of this non-ergodic absorbing MDP. -/
theorem stateExperiment_invariant (P : Policy) (θ : World) (z : Skill) (s : State) :
    (∑ x, stateExperiment P θ z x * stateKernel P z θ x s) =
      stateExperiment P θ z s := by
  rw [Fintype.sum_option, stateExperiment_none, zero_mul, zero_add]
  simp_rw [stateKernel_some]
  cases s with
  | none => simp [point]
  | some b => simp [point]

/-- Every positive-time state law is already the stationary law selected by
the prescribed initial state. This is an ensemble statement, not ergodicity
of a single absorbing trajectory. -/
theorem stateExperiment_reached (P : Policy) (θ : World) (z : Skill)
    (t : ℕ) (ht : 0 < t) :
    stateMarginal (causalPolicy P z) θ t = stateExperiment P θ z := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  exact policy_stateMarginal_succ P z θ n

theorem stateMarginal_tendsto (P : Policy) (θ : World) (z : Skill) :
    Tendsto (fun t : ℕ => stateMarginal (causalPolicy P z) θ t) atTop
      (𝓝 (stateExperiment P θ z)) := by
  have he : (fun _ : ℕ => stateExperiment P θ z) =ᶠ[atTop]
      (fun t => stateMarginal (causalPolicy P z) θ t) := by
    filter_upwards [eventually_ge_atTop 1] with t ht
    exact (stateExperiment_reached P θ z t (by omega)).symm
  exact tendsto_const_nhds.congr' he

/-- Actual joint law of the current state and the next action. -/
def stateActionMarginal (P : Policy) (z : Skill) (θ : World) (t : ℕ)
    (s : State) (a : Action) : ℝ :=
  ∑ w : CausalFiniteTrace Action State t,
    causalFiniteExperiment (causalPolicy P z).1 response t θ w *
      (if currentState (List.ofFn w) = s then
        (causalPolicy P z).1 (List.ofFn w) a else 0)

theorem stateActionMarginal_eq (P : Policy) (z : Skill) (θ : World) (t : ℕ)
    (s : State) (a : Action) :
    stateActionMarginal P z θ t s a =
      stateMarginal (causalPolicy P z) θ t s * (P z s).1 a := by
  unfold stateActionMarginal stateMarginal
  rw [sum_mul]
  apply sum_congr rfl
  intro w _
  by_cases hs : currentState (List.ofFn w) = s
  · simp [causalPolicy, hs]
  · simp [hs]

theorem policy_stateActionMarginal_succ (P : Policy) (z : Skill) (θ : World)
    (n : ℕ) (s : State) (a : Action) :
    stateActionMarginal P z θ (n+1) s a =
      stateExperiment P θ z s * (P z s).1 a := by
  rw [stateActionMarginal_eq, policy_stateMarginal_succ]

end
end IdExp.DIAYNState
