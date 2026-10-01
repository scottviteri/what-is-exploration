import Formal.AlarmPanel

/-!
# Each alarm/panel world has a finite hidden-state realization

A world-specific finite countdown tracks the remaining monitor ticks until its
single pulse. The never-pulse world uses countdown zero. Mode and phase are
retained, and the most recent raw label is stored so that the percept law depends
only on the next hidden state. Actions remain Fin 3 and visible observations
remain Fin 4; no hidden state coordinate is exposed to the policy. The number of
hidden states may depend on the world, with no uniform bound asserted.
-/
namespace IdExp.AlarmPanel.FiniteHiddenState
open Finset
noncomputable section

/-- One more than the finite pulse index; zero in the never-pulse world. -/
def countdownBound : World → ℕ
  | none => 0
  | some k => k+1

abbrev Countdown (θ : World) := Fin (countdownBound θ + 1)
/-- No mode before startup; afterwards inspected?, next-is-panel?, countdown. -/
abbrev Summary (θ : World) := Option (Bool × Bool × Countdown θ)
abbrev State (θ : World) := Summary θ × Observation

def initialCountdown (θ : World) : Countdown θ := ⟨countdownBound θ, by omega⟩
def predecessor (θ : World) (c : Countdown θ) : Countdown θ :=
  ⟨c.val - 1, by have := c.isLt; omega⟩

def update (θ : World) : Summary θ → Action → Summary θ
  | none, a => some (decide (a = inspect), true, initialCountdown θ)
  | some (i, panel, c), _ =>
    if panel then some (i, false, c) else some (i, true, predecessor θ c)

def emission (θ : World) : Summary θ → Action → Observation → ℝ
  | none, a, o => if a = inspect then pairDist θ.isSome o else uniformDist o
  | some (i, panel, c), a, o =>
    if panel then (if i then pointDist 0 o else pairDist (a == play1) o)
    else pointDist (if c.val = 1 then 1 else 0) o

theorem emission_valid (θ : World) (q : Summary θ) (a : Action) :
    IsDist (emission θ q a) := by
  cases q with
  | none =>
    change IsDist (fun o => if a = inspect then pairDist θ.isSome o else uniformDist o)
    by_cases h : a = inspect
    · simpa only [h, if_true] using pairDist_valid θ.isSome
    · simpa only [h, if_false] using uniformDist_valid
  | some q =>
    rcases q with ⟨i, panel, c⟩
    change IsDist (fun o => if panel then
      (if i then pointDist 0 o else pairDist (a == play1) o)
      else pointDist (if c.val = 1 then 1 else 0) o)
    cases panel <;> cases i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> first
      | exact pointDist_valid _
      | exact pairDist_valid _

def remaining (θ : World) (h : History) : Countdown θ :=
  ⟨countdownBound θ - (h.length - 1)/2,
    lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_self _)⟩

def summary (θ : World) (h : History) : Summary θ :=
  if h = [] then none else
    some (decide (inspected h), decide (h.length % 2 = 1), remaining θ h)

@[simp] theorem summary_nil (θ : World) : summary θ [] = none := by simp [summary]

theorem inspected_append (h : History) (a : Action) (o : Observation) (hh : h ≠ []) :
    inspected (h ++ [(a,o)]) ↔ inspected h := by
  cases h with
  | nil => contradiction
  | cons x xs => simp [inspected]

theorem remaining_append_panel (θ : World) (h : History) (a : Action) (o : Observation)
    (hp : h.length % 2 = 1) : remaining θ (h ++ [(a,o)]) = remaining θ h := by
  apply Fin.ext
  simp only [remaining, List.length_append, List.length_singleton]
  omega

theorem remaining_append_monitor (θ : World) (h : History) (a : Action) (o : Observation)
    (hh : h ≠ []) (hp : h.length % 2 ≠ 1) :
    remaining θ (h ++ [(a,o)]) = predecessor θ (remaining θ h) := by
  have hn : 0 < h.length := by cases h with
    | nil => contradiction
    | cons x xs => simp
  apply Fin.ext
  simp only [remaining, predecessor, List.length_append, List.length_singleton]
  omega

/-- The finite summary updates from the last summary and current action alone. -/
theorem summary_append (θ : World) (h : History) (a : Action) (o : Observation) :
    summary θ (h ++ [(a,o)]) = update θ (summary θ h) a := by
  by_cases hh : h = []
  · subst h
    simp [summary, update, inspected, remaining, initialCountdown]
  · have hn : h ++ [(a,o)] ≠ [] := by simp
    have hi := inspected_append h a o hh
    by_cases hp : h.length % 2 = 1
    · simp [summary, hh, hn, hi, hp, update, remaining_append_panel θ h a o hp]
      omega
    · simp [summary, hh, hn, hi, hp, update, remaining_append_monitor θ h a o hh hp]
      omega

theorem remaining_monitor (θ : World) (h : History) (hh : h ≠ [])
    (hp : h.length % 2 ≠ 1) :
    (if (remaining θ h).val = 1 then (1 : Observation) else 0) =
      monitorLabel θ ((h.length - 2)/2) := by
  have hn : 0 < h.length := by cases h with
    | nil => contradiction
    | cons x xs => simp
  have he : (remaining θ h).val = 1 ↔ θ = some ((h.length - 2)/2) := by
    cases θ with
    | none => simp [remaining, countdownBound]
    | some k => simp only [remaining, countdownBound, Option.some.injEq]; omega
  simp only [monitorLabel, he]

/-- Literal response equality, including histories of probability zero. -/
theorem emission_summary_eq_response (θ : World) (h : History) (a : Action) (o : Observation) :
    emission θ (summary θ h) a o = response θ h a o := by
  by_cases hh : h = []
  · subst h; simp [summary, emission, response]
  · by_cases hp : h.length % 2 = 1
    · simp [summary, hh, hp, emission, response]
    · simp [summary, hh, hp, emission, response, remaining_monitor θ h hh hp]

/-- The next raw label is sampled by the transition, then emitted deterministically. -/
def transition (θ : World) (x : State θ) (a : Action) (y : State θ) : ℝ :=
  if y.1 = update θ x.1 a then emission θ x.1 a y.2 else 0

def percept (θ : World) (x : State θ) : Observation → ℝ := pointDist x.2

theorem transition_valid (θ : World) (x : State θ) (a : Action) :
    IsDist (transition θ x a) := by
  constructor
  · intro y; unfold transition; split_ifs
    · exact (emission_valid θ x.1 a).1 y.2
    · norm_num
  · simp only [transition, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single (update θ x.1 a)]
    · simpa using (emission_valid θ x.1 a).2
    · intro q _ hq; simp [hq]
    · simp

theorem percept_valid (θ : World) (x : State θ) : IsDist (percept θ x) :=
  pointDist_valid x.2

/-- Marginalizing the next hidden state recovers the original sensor row. -/
theorem transition_percept_eq (θ : World) (x : State θ) (a : Action) (o : Observation) :
    (∑ y : State θ, transition θ x a y * percept θ y o) = emission θ x.1 a o := by
  simp [transition, percept, pointDist, Fintype.sum_prod_type, mul_ite]

def initialState (θ : World) : State θ := (none, 0)
def stateAfter (θ : World) (h : History) : State θ :=
  (summary θ h, ((h.getLast?).map Prod.snd).getD 0)

@[simp] theorem stateAfter_nil (θ : World) : stateAfter θ [] = initialState θ := by
  simp [stateAfter, initialState]

theorem stateAfter_append (θ : World) (h : History) (a : Action) (o : Observation) :
    stateAfter θ (h ++ [(a,o)]) = (update θ (summary θ h) a, o) := by
  simp [stateAfter, summary_append]

/-- Given a visible next label, only the correctly updated hidden state can
have nonzero joint transition/percept mass. -/
theorem transition_percept_joint (θ : World) (h : History) (a : Action)
    (o : Observation) (y : State θ) :
    transition θ (stateAfter θ h) a y * percept θ y o =
      if y = stateAfter θ (h ++ [(a,o)]) then response θ h a o else 0 := by
  rcases y with ⟨q, z⟩
  rw [stateAfter_append]
  by_cases hq : q = update θ (summary θ h) a
  · subst q
    by_cases hz : z = o
    · subst z
      simp [transition, percept, pointDist, stateAfter, emission_summary_eq_response]
    · simp [transition, percept, pointDist, stateAfter, hz, Ne.symm hz]
  · simp [transition, percept, pointDist, stateAfter, hq]

/-- Imposed-action observation likelihood from the actual finite hidden-state
transition/percept model, summing over all intervening hidden states. -/
def observationMassFrom (θ : World) : State θ → History → ℝ
  | _, [] => 1
  | x, (a,o)::rest => ∑ y : State θ,
      transition θ x a y * percept θ y o * observationMassFrom θ y rest

/-- The actual hidden-state path sum agrees with the original response-product
likelihood after every prefix, including off-support prefixes. -/
theorem observationMassFrom_eq (θ : World) (pre rest : History) :
    observationMassFrom θ (stateAfter θ pre) rest =
      causalResponseProbFrom (response θ) pre rest := by
  induction rest generalizing pre with
  | nil => rfl
  | cons ao rest ih =>
    rcases ao with ⟨a,o⟩
    simp only [observationMassFrom, transition_percept_joint, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true, ih, causalResponseProbFrom]

/-- Equality of the controlled-prefix probabilities of the two presentations. -/
theorem observationMass_eq (θ : World) (h : History) :
    observationMassFrom θ (initialState θ) h = causalResponseProb (response θ) h := by
  simpa only [stateAfter_nil, causalResponseProb] using observationMassFrom_eq θ [] h

/-- The POMDP has a finite state set for each fixed world, not one finite
clock shared by all delay worlds. -/
theorem state_card (θ : World) :
    Fintype.card (State θ) = 4 * (1 + 4 * (countdownBound θ + 1)) := by
  simp [State, Summary, Countdown, Fintype.card_prod, Fintype.card_option]
  ring

/-- The marginal conditional response of the finite hidden-state realization. -/
def realizedResponse (θ : World) : CausalResponse Action Observation :=
  fun h a o => ∑ y : State θ, transition θ (stateAfter θ h) a y * percept θ y o

theorem realizedResponse_eq (θ : World) : realizedResponse θ = response θ := by
  funext h a o
  rw [realizedResponse, transition_percept_eq]
  exact emission_summary_eq_response θ h a o

theorem realizedResponse_valid (θ : World) : IsCausalResponse (realizedResponse θ) := by
  rw [realizedResponse_eq]
  exact response_valid θ

/-- All policies, including arbitrary randomized history-dependent policies,
induce exactly the original full-record experiments. -/
theorem realized_experiment_eq (π : CausalPolicy Action Observation) (t : ℕ) :
    causalFiniteExperiment π realizedResponse t = experiment π t := by
  have he : realizedResponse = response := funext realizedResponse_eq
  rw [he]
  rfl

#print axioms emission_summary_eq_response
#print axioms transition_valid
#print axioms observationMass_eq
#print axioms realized_experiment_eq
end
end IdExp.AlarmPanel.FiniteHiddenState
