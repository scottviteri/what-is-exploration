import Formal.ControlEntropy
import Formal.RewardProcessWitness

/-! Actual infinite discounted state-visitation entropy in a fully observed
three-state MDP. TEST selects the absorbing state named by the unknown model;
RANDOM selects either absorbing state fairly. The objective is H(d_pi), not
empirical observation entropy or an entropy after pooling unknown models. -/
namespace IdExp.StateOccupancyEntropy
open Finset
noncomputable section
abbrev World := Fin 2
abbrev Action := Fin 2
abbrev State := Option (Fin 2)
abbrev History := CausalHistory Action State

def point (s : State) (x : State) : ℝ := if x = s then 1 else 0
def fair : State → ℝ | none => 0 | some _ => 1 / 2
def transition (θ : World) : State → Action → State → ℝ
  | none, a, x => if a = 0 then point (some θ) x else fair x
  | some b, _, x => point (some b) x

theorem point_valid (s : State) : IsDist (point s) := by
  constructor
  · intro x; unfold point; split_ifs <;> norm_num
  · simp [point]
theorem fair_valid : IsDist fair := by
  constructor
  · intro x; cases x <;> norm_num [fair]
  · norm_num [Fintype.sum_option, Fin.sum_univ_two, fair]
theorem transition_valid (θ : World) (s : State) (a : Action) :
    IsDist (transition θ s a) := by
  cases s with
  | none =>
    change IsDist (fun x => if a = 0 then point (some θ) x else fair x)
    by_cases ha : a = 0
    · simpa [transition, ha] using point_valid (some θ)
    · simpa [transition, ha] using fair_valid
  | some b => exact point_valid (some b)

/-- The actual current state, fully observed after every transition. -/
def currentState (h : History) : State := ((h.getLast?).map Prod.snd).getD none
@[simp] theorem currentState_nil : currentState [] = none := rfl
@[simp] theorem currentState_append (h : History) (ao : Action × State) :
    currentState (h ++ [ao]) = ao.2 := by simp [currentState]
def response (θ : World) : CausalResponse Action State :=
  fun h a => transition θ (currentState h) a
theorem response_valid (θ : World) : IsCausalResponse (response θ) :=
  fun h a => transition_valid θ (currentState h) a

/-- State marginal of the actual full policy-induced record. -/
def stateMarginal (π : ValidCausalPolicy Action State) (θ : World) (t : ℕ)
    (s : State) : ℝ :=
  ∑ w : CausalFiniteTrace Action State t,
    causalFiniteExperiment π.1 response t θ w *
      (if currentState (List.ofFn w) = s then 1 else 0)
def terminalLaw (π : ValidCausalPolicy Action State) (θ : World) (b : Fin 2) : ℝ :=
  π.1 [] 0 * (if b = θ then 1 else 0) + π.1 [] 1 / 2

theorem root_weights (π : ValidCausalPolicy Action State) : π.1 [] 0 + π.1 [] 1 = 1 := by
  simpa [Fin.sum_univ_two] using (π.2 []).2
theorem terminalLaw_valid (π : ValidCausalPolicy Action State) (θ : World) :
    IsDist (terminalLaw π θ) := by
  constructor
  · intro b
    unfold terminalLaw
    exact add_nonneg (mul_nonneg ((π.2 []).1 0) (by split_ifs <;> norm_num))
      (div_nonneg ((π.2 []).1 1) (by norm_num))
  · have hp := root_weights π
    fin_cases θ <;> simp [terminalLaw, Fin.sum_univ_two] <;> linarith

theorem tail_state (π : CausalPolicy Action State) (θ : World)
    (pre rest : History) (b : Fin 2) (hpre : currentState pre = some b)
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

theorem tail_state_sum (π : ValidCausalPolicy Action State) (θ : World)
    (pre : History) (b : Fin 2) (hpre : currentState pre = some b) (n : ℕ)
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

@[simp] theorem stateMarginal_zero (π : ValidCausalPolicy Action State) (θ : World)
    (s : State) : stateMarginal π θ 0 s = point none s := by
  simp [stateMarginal, causalFiniteExperiment, causalTraceProb, causalTraceProbFrom,
    point, eq_comm]

theorem stateMarginal_succ (π : ValidCausalPolicy Action State) (θ : World) (n : ℕ)
    (s : State) :
    stateMarginal π θ (n+1) s = match s with | none => 0 | some b => terminalLaw π θ b := by
  unfold stateMarginal
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Action × State)).sum_comp]
  rw [Fintype.sum_prod_type]
  have hcons (ao : Action × State) (w : CausalFiniteTrace Action State n) :
      (Fin.consEquiv (fun _ : Fin (n+1) => Action × State)) (ao,w) = Fin.cons ao w := by
    funext i; exact Fin.consEquiv_apply _ _ i
  simp_rw [hcons, List.ofFn_cons]
  simp only [causalFiniteExperiment, causalTraceProb, List.ofFn_cons, causalTraceProbFrom, List.nil_append]
  simp_rw [mul_assoc, ← mul_sum]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_option]
  have hz (a : Action) : response θ [] a none = 0 := by
    simp [response, transition, point, fair]
  simp only [hz, zero_mul, mul_zero, zero_add]
  have hs (a : Action) (b : Fin 2) :
      (∑ w : CausalFiniteTrace Action State n,
        causalTraceProbFrom π.1 (response θ) [(a, some b)] (List.ofFn w) *
          (if currentState ((a, some b) :: List.ofFn w) = s then 1 else 0)) =
        if some b = s then 1 else 0 := by
    simpa using tail_state_sum π θ [(a, some b)] b (by simp [currentState]) n s
  simp_rw [hs]
  cases s with
  | none => simp
  | some b =>
    simp only [Option.some.injEq]
    simp [Fin.sum_univ_two, response, transition, point, fair, terminalLaw, div_eq_mul_inv]

/-- Literal infinite discounted state occupancy, including the initial state. -/
def occupancy (π : ValidCausalPolicy Action State) (θ : World) (γ : ℝ) (s : State) : ℝ :=
  (1-γ) * ∑' t : ℕ, γ^t * stateMarginal π θ t s

theorem occupancy_eq (π : ValidCausalPolicy Action State) (θ : World) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : State) :
    occupancy π θ γ s = match s with
      | none => 1-γ
      | some b => γ * terminalLaw π θ b := by
  have hs : Summable (fun t : ℕ => γ^t * stateMarginal π θ (t+1) s) := by
    simp_rw [stateMarginal_succ]
    exact (summable_geometric_of_lt_one hγ0 hγ1).mul_right _
  have hall : Summable (fun t : ℕ => γ^t * stateMarginal π θ t s) := by
    apply (summable_nat_add_iff 1).1
    simpa [pow_succ, mul_left_comm, mul_assoc] using hs.mul_left γ
  unfold occupancy
  rw [hall.tsum_eq_zero_add]
  simp only [pow_zero, one_mul, stateMarginal_zero, stateMarginal_succ]
  cases s with
  | none => simp [point]
  | some b =>
    simp only [point, reduceCtorEq, if_false, zero_add, pow_succ, mul_assoc,
      tsum_mul_right, tsum_geometric_of_lt_one hγ0 hγ1]
    have hne : 1-γ ≠ 0 := by linarith
    field_simp

/-- The published objective is entropy AFTER averaging state occupancy. -/
def objective (π : ValidCausalPolicy Action State) (θ : World) (γ : ℝ) : ℝ :=
  ent (occupancy π θ γ)
def binaryEntropy (p : ℝ) : ℝ := Real.negMulLog (1-p) + Real.negMulLog p

def purePolicy (a : Action) : ValidCausalPolicy Action State :=
  ⟨fun _ b => if b = a then 1 else 0, by
    intro h
    constructor
    · intro b; dsimp; split_ifs <;> norm_num
    · simp⟩

theorem occupancy_valid (π : ValidCausalPolicy Action State) (θ : World) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) : IsDist (occupancy π θ γ) := by
  constructor
  · intro s; rw [occupancy_eq π θ γ hγ0 hγ1]
    cases s with
    | none => dsimp; linarith
    | some b => exact mul_nonneg hγ0 ((terminalLaw_valid π θ).1 b)
  · simp_rw [occupancy_eq π θ γ hγ0 hγ1]
    simp only [Fintype.sum_option, ← mul_sum, (terminalLaw_valid π θ).2, mul_one]
    ring

theorem objective_eq (π : ValidCausalPolicy Action State) (θ : World) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    objective π θ γ = binaryEntropy γ + γ * ent (terminalLaw π θ) := by
  unfold objective ent
  simp_rw [occupancy_eq π θ γ hγ0 hγ1]
  simp only [Fintype.sum_option, Real.negMulLog_mul, sum_add_distrib]
  simp only [← sum_mul, ← mul_sum, (terminalLaw_valid π θ).2, one_mul]
  unfold binaryEntropy
  ring

theorem terminalLaw_uniform_iff (π : ValidCausalPolicy Action State) (θ : World) :
    terminalLaw π θ = uniformPrior (Fin 2) ↔ π.1 [] 0 = 0 := by
  have hw := root_weights π
  constructor
  · intro he
    have h := congrFun he θ
    simp [terminalLaw, uniformPrior] at h
    linarith
  · intro hp
    have hq : π.1 [] 1 = 1 := by linarith
    funext b
    simp [terminalLaw, hp, hq, uniformPrior]

theorem objective_le (π : ValidCausalPolicy Action State) (θ : World) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    objective π θ γ ≤ binaryEntropy γ + γ * Real.log 2 := by
  rw [objective_eq π θ γ hγ0 hγ1]
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ hγ0
  simpa using ent_le_log_card (terminalLaw π θ) (terminalLaw_valid π θ)

theorem objective_eq_max_iff (π : ValidCausalPolicy Action State) (θ : World) (γ : ℝ)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    objective π θ γ = binaryEntropy γ + γ * Real.log 2 ↔ π.1 [] 0 = 0 := by
  rw [objective_eq π θ γ hγ0.le hγ1, add_right_inj,
    mul_right_inj' (ne_of_gt hγ0)]
  have he := ent_eq_log_card_iff (terminalLaw π θ) (terminalLaw_valid π θ)
  simpa [terminalLaw_uniform_iff] using he

/-- All and only policies that choose RANDOM initially maximize H(d_pi).
The statement holds in EACH fixed MDP, with no world prior. -/
theorem objective_maximizer_iff (π : ValidCausalPolicy Action State) (θ : World)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    (∀ ρ, objective ρ θ γ ≤ objective π θ γ) ↔ π.1 [] 0 = 0 := by
  have hr : objective (purePolicy 1) θ γ = binaryEntropy γ + γ * Real.log 2 :=
    (objective_eq_max_iff _ θ γ hγ0 hγ1).2 (by simp [purePolicy])
  constructor
  · intro h
    apply (objective_eq_max_iff π θ γ hγ0 hγ1).1
    exact le_antisymm (objective_le π θ γ hγ0.le hγ1) (by simpa [hr] using h (purePolicy 1))
  · intro hp ρ
    rw [(objective_eq_max_iff π θ γ hγ0 hγ1).2 hp]
    exact objective_le ρ θ γ hγ0.le hγ1

theorem objective_attained (θ : World) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∀ ρ, objective ρ θ γ ≤ objective (purePolicy 1) θ γ :=
  (objective_maximizer_iff _ θ γ hγ0 hγ1).2 (by simp [purePolicy])

/-- The explicit binary-entropy formula is the same in the two fixed MDPs. -/
theorem objective_eq_binary (π : ValidCausalPolicy Action State) (θ : World) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    objective π θ γ = binaryEntropy γ + γ * binaryEntropy ((1 + π.1 [] 0)/2) := by
  rw [objective_eq π θ γ hγ0 hγ1]
  have hw := root_weights π
  have hq : π.1 [] 1 = 1 - π.1 [] 0 := by linarith
  have hb : (1 - π.1 [] 0)/2 = 1 - (1 + π.1 [] 0)/2 := by ring
  have hc : π.1 [] 0 + (1 - (1 + π.1 [] 0)/2) = (1 + π.1 [] 0)/2 := by ring
  have he : ent (terminalLaw π θ) = binaryEntropy ((1 + π.1 [] 0)/2) := by
    fin_cases θ <;>
      simp [ent, terminalLaw, Fin.sum_univ_two, binaryEntropy, hq, hb, hc, add_comm]
  rw [he]

end
end IdExp.StateOccupancyEntropy
