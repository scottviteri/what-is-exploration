import Formal.PhysicalEntropyLoss

/-! A finite, fully observed, time-homogeneous MDP for the original MOP objective.
There are five physical states: START and four absorbing outcomes. The ambient
two-action encoding is restricted by `SourceAdmissible` to one legal STAY action
at every absorbing state, following the source convention. Stationary policies see the actual physical state,
not the unknown transition-model index. Their records retain every action and state.
The known initial START need not be repeated in the observation alphabet. -/
namespace IdExp.MOPFiniteMDP
open Finset Filter
open scoped Topology
noncomputable section

abbrev World := PhysicalEntropyControl.World
abbrev Action := PhysicalEntropyControl.Action
abbrev Outcome := PhysicalEntropyControl.Observation
abbrev History := CausalHistory Action Outcome
abbrev State := Option Outcome
abbrev Policy := State → {p : Action → ℝ // IsDist p}

def liftDist (p : Outcome → ℝ) : State → ℝ
  | none => 0
  | some o => p o

theorem liftDist_valid (p : Outcome → ℝ) (hp : IsDist p) : IsDist (liftDist p) := by
  constructor
  · intro x; cases x with
    | none => simp [liftDist]
    | some o => exact hp.1 o
  · simpa [Fintype.sum_option, liftDist] using hp.2

@[simp] theorem entropy_liftDist (p : Outcome → ℝ) : ent (liftDist p) = ent p := by
  simp [ent, Fintype.sum_option, liftDist, Real.negMulLog_zero]

/-- The actual finite physical transition law. The model index changes READ's
outcome, not what the agent is told about its current state. -/
def transition (θ : World) : State → Action → State → ℝ
  | none, a => liftDist (PhysicalEntropyControl.root a θ)
  | some b, _ => liftDist (fun o => if o = b then 1 else 0)

theorem state_card : Fintype.card State = 5 := by decide

theorem transition_valid (θ : World) (x : State) (a : Action) :
    IsDist (transition θ x a) := by
  cases x with
  | none => exact liftDist_valid _ (PhysicalEntropyControl.root_valid a θ)
  | some b =>
    apply liftDist_valid
    constructor
    · intro o; dsimp; split_ifs <;> norm_num
    · simp

@[simp] theorem transition_never_start (θ : World) (x : State) (a : Action) :
    transition θ x a none = 0 := by cases x <;> rfl

/-- START is known initially; subsequently the last observed outcome IS the
current physical state. No hidden clock, mode or model index is appended. -/
def currentState (h : History) : State :=
  if h = [] then none else some (PhysicalEntropyControl.state h)

@[simp] theorem currentState_nil : currentState [] = none := by simp [currentState]
@[simp] theorem currentState_append (h : History) (a : Action) (o : Outcome) :
    currentState (h ++ [(a,o)]) = some o := by
  simp [currentState, PhysicalEntropyControl.state, List.reverse_append]

/-- The already checked causal record law is exactly the finite MDP transition
law, with the known initial state omitted from the emitted record. -/
theorem transition_response (θ : World) (h : History) (a : Action) :
    transition θ (currentState h) a = liftDist (PhysicalEntropyControl.response θ h a) := by
  by_cases hh : h = []
  · subst h; simp [transition]
  · rw [PhysicalEntropyControl.response_tail θ h a hh]
    simp only [currentState, if_neg hh, transition]
    rfl

def causalPolicy (P : Policy) : ValidCausalPolicy Action Outcome :=
  ⟨fun h => (P (currentState h)).1, fun h => (P (currentState h)).2⟩

/-- Original MOP's unit-weight local action and successor-STATE entropies. -/
def localReward (P : Policy) (θ : World) (x : State) : ℝ :=
  ent (P x).1 + ∑ a, (P x).1 a * ent (transition θ x a)

theorem localReward_eq (P : Policy) (θ : World) (h : History) :
    localReward P θ (currentState h) =
      PhysicalEntropyControl.localReward (causalPolicy P).1 θ h := by
  simp [localReward, PhysicalEntropyControl.localReward, causalPolicy, transition_response]

/-- Actual expected state-based reward in one fixed MDP, without a world prior. -/
def stage (P : Policy) (θ : World) (t : ℕ) : ℝ :=
  ∑ w : CausalFiniteTrace Action Outcome t,
    causalFiniteExperiment (causalPolicy P).1 PhysicalEntropyControl.response t θ w *
      localReward P θ (currentState (List.ofFn w))

def objective (γ : ℝ) (P : Policy) (θ : World) : ℝ := ∑' t, γ^t * stage P θ t

theorem stage_nonneg (P : Policy) (θ : World) (t : ℕ) : 0 ≤ stage P θ t := by
  apply sum_nonneg; intro w _
  apply mul_nonneg
  · exact (causalFiniteExperiment_valid _ (causalPolicy P).2 _
      PhysicalEntropyControl.response_valid t θ).1 w
  rw [localReward_eq]
  unfold PhysicalEntropyControl.localReward
  apply add_nonneg (ent_nonneg_of_isDist _ ((causalPolicy P).2 _))
  apply sum_nonneg; intro a _
  exact mul_nonneg (((causalPolicy P).2 _).1 a)
    (ent_nonneg_of_isDist _ (PhysicalEntropyControl.response_valid θ _ a))

theorem stage_zero (P : Policy) (θ : World) :
    stage P θ 0 = splitBinaryEntropy ((P none).1 0) := by
  simp only [stage, localReward_eq]
  have hr := PhysicalEntropyControl.localReward_root (causalPolicy P) θ
  simpa [causalFiniteExperiment, causalTraceProb, causalTraceProbFrom,
    causalPolicy] using hr

/-- Every positive record length has the same exact loss; later actions and the
entire state-action record are retained. -/
theorem native_loss (P : Policy) (t : ℕ) :
    finiteDeficiency
      (causalFiniteExperiment (causalPolicy P).1 PhysicalEntropyControl.response (t+1))
      (causalPlanObservationExperiment 1 PhysicalEntropyControl.readPlan
        PhysicalEntropyControl.response) = (1 - (P none).1 0)/2 := by
  simpa [causalPolicy] using PhysicalEntropyControl.prefix_nativeRead_deficiency (causalPolicy P) t

/-- The same deficiency holds even for the infinite record and arbitrary
measurable randomized decoding. -/
theorem path_native_loss (P : Policy) :
    finiteMeasureDeficiency
      (causalPathExperiment PhysicalEntropyControl.response
        PhysicalEntropyControl.response_valid (causalPolicy P))
      (rowExperiment (causalPlanObservationExperiment 1 PhysicalEntropyControl.readPlan
        PhysicalEntropyControl.response)) = (1 - (P none).1 0)/2 := by
  simpa [causalPolicy] using PhysicalEntropyControl.path_nativeRead_deficiency (causalPolicy P)

def eventualDeficiency (P : Policy) : ℝ :=
  sInf (Set.range fun t => finiteDeficiency
    (causalFiniteExperiment (causalPolicy P).1 PhysicalEntropyControl.response (t+1))
    (causalPlanObservationExperiment 1 PhysicalEntropyControl.readPlan
      PhysicalEntropyControl.response))

/-- The original paper gives absorbing states only STAY. Action 0 denotes READ
at START and STAY at an absorbing state; action 1 is available only at START.
Zero padding into a common finite action alphabet does not add an action choice. -/
def available (x : State) : Finset Action := if x = none then univ else {0}

def SourceAdmissible (P : Policy) : Prop := ∀ o, (P (some o)).1 = ![1,0]

theorem sourceAdmissible_iff_supported (P : Policy) : SourceAdmissible P ↔
    ∀ x a, a ∉ available x → (P x).1 a = 0 := by
  constructor
  · intro hp x a ha
    cases x with
    | none => simp [available] at ha
    | some o =>
      rw [hp o]
      fin_cases a <;> simp_all [available]
  · intro hp o
    have hz : (P (some o)).1 1 = 0 := hp _ _ (by simp [available])
    have hs := (P (some o)).2.2
    rw [Fin.sum_univ_two, hz] at hs
    funext a; fin_cases a <;> simp_all

def sourcePolicy (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Policy
  | none => ⟨![p,1-p], by simpa [PhysicalEntropyControl.uniformTail] using
      PhysicalEntropyControl.uniformTail_valid hp0 hp1 []⟩
  | some _ => ⟨![1,0], by
      constructor
      · intro a; fin_cases a <;> norm_num
      · norm_num [Fin.sum_univ_two]⟩

theorem sourcePolicy_admissible (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    SourceAdmissible (sourcePolicy p hp0 hp1) := by intro o; rfl

theorem source_stage_succ (P : Policy) (hp : SourceAdmissible P) (θ : World) (t : ℕ) :
    stage P θ (t+1) = 0 := by
  unfold stage
  apply sum_eq_zero; intro w _
  rw [localReward_eq, PhysicalEntropyControl.localReward_tail _ _ _ (by simp)]
  have hh : List.ofFn w ≠ [] := by simp
  simp only [causalPolicy, currentState, if_neg hh]
  rw [hp (PhysicalEntropyControl.state (List.ofFn w))]
  norm_num [ent, Fin.sum_univ_two]

/-- Literal discounted MOP with one available action at each absorbing state.
Its only nonzero contribution is the root action-plus-state entropy. -/
theorem source_objective (γ : ℝ) (P : Policy) (hp : SourceAdmissible P) (θ : World) :
    objective γ P θ = splitBinaryEntropy ((P none).1 0) := by
  unfold objective
  rw [tsum_eq_single 0]
  · simp [stage_zero]
  · intro t ht
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht
    rw [source_stage_succ P hp θ k, mul_zero]

def sourceOptimizer : Policy := sourcePolicy (1/3) (by norm_num) (by norm_num)

theorem sourceOptimizer_admissible : SourceAdmissible sourceOptimizer :=
  sourcePolicy_admissible _ _ _

theorem sourceOptimizer_value (γ : ℝ) (θ : World) :
    objective γ sourceOptimizer θ = Real.log 3 := by
  rw [source_objective γ _ sourceOptimizer_admissible θ]
  change splitBinaryEntropy (1/3) = Real.log 3
  exact (splitBinaryEntropy_eq_iff (by norm_num : (0:ℝ) ≤ 1/3)
    (by norm_num : (1/3:ℝ) ≤ 1)).2 rfl

theorem sourceOptimizer_maximizes (γ : ℝ) (θ : World) (P : Policy)
    (hp : SourceAdmissible P) : objective γ P θ ≤ objective γ sourceOptimizer θ := by
  rw [sourceOptimizer_value, source_objective γ P hp θ]
  have hp1 : (P none).1 0 ≤ 1 := by
    have h := (P none).2.2
    rw [Fin.sum_univ_two] at h
    linarith [(P none).2.1 1]
  exact splitBinaryEntropy_le ((P none).2.1 0) hp1

theorem source_maximizing_root (γ : ℝ) (θ : World) (P : Policy)
    (hp : SourceAdmissible P)
    (hmax : ∀ R, SourceAdmissible R → objective γ R θ ≤ objective γ P θ) :
    (P none).1 0 = 1/3 := by
  have hp1 : (P none).1 0 ≤ 1 := by
    have h := (P none).2.2
    rw [Fin.sum_univ_two] at h
    linarith [(P none).2.1 1]
  apply (splitBinaryEntropy_eq_iff ((P none).2.1 0) hp1).1
  apply le_antisymm (splitBinaryEntropy_le ((P none).2.1 0) hp1)
  have h := hmax sourceOptimizer sourceOptimizer_admissible
  rwa [sourceOptimizer_value, source_objective γ P hp θ] at h

theorem source_maximizing_native_loss (γ : ℝ) (θ : World) (P : Policy)
    (hp : SourceAdmissible P)
    (hmax : ∀ R, SourceAdmissible R → objective γ R θ ≤ objective γ P θ) :
    (∀ t, finiteDeficiency
      (causalFiniteExperiment (causalPolicy P).1 PhysicalEntropyControl.response (t+1))
      (causalPlanObservationExperiment 1 PhysicalEntropyControl.readPlan
        PhysicalEntropyControl.response) = 1/3) ∧
    finiteMeasureDeficiency
      (causalPathExperiment PhysicalEntropyControl.response
        PhysicalEntropyControl.response_valid (causalPolicy P))
      (rowExperiment (causalPlanObservationExperiment 1 PhysicalEntropyControl.readPlan
        PhysicalEntropyControl.response)) = 1/3 := by
  have hr := source_maximizing_root γ θ P hp hmax
  constructor
  · intro t; rw [native_loss, hr]; norm_num
  · rw [path_native_loss, hr]; norm_num

theorem source_maximizing_eventualDeficiency (γ : ℝ) (θ : World) (P : Policy)
    (hp : SourceAdmissible P)
    (hmax : ∀ R, SourceAdmissible R → objective γ R θ ≤ objective γ P θ) :
    eventualDeficiency P = 1/3 := by
  have ht := (source_maximizing_native_loss γ θ P hp hmax).1
  simp only [eventualDeficiency, ht, Set.range_const, csInf_singleton]

theorem source_read_sufficient : CausalNativelySufficient PhysicalEntropyControl.response
    (causalPolicy (sourcePolicy 1 (by norm_num) (by norm_num))) := by
  let P := sourcePolicy 1 (by norm_num) (by norm_num)
  intro n ε hε
  refine ⟨1, ?_⟩
  intro t ht τ
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show t ≠ 0 by omega)
  have h := finiteDeficiency_mono_target_of_finiteBlackwellLE
    (causalFiniteExperiment (causalPolicy P).1 PhysicalEntropyControl.response (k+1))
    (causalPlanObservationExperiment n τ PhysicalEntropyControl.response)
    (PhysicalEntropyControl.root 0)
    (causalFiniteExperiment_valid _ (causalPolicy P).2 _ PhysicalEntropyControl.response_valid (k+1))
    (PhysicalEntropyControl.root_valid 0)
    (PhysicalEntropyControl.revelation_dominates _ (causalPlanObservationExperiment_valid n τ _
      PhysicalEntropyControl.response_valid))
  rw [PhysicalEntropyControl.prefix_revelation_deficiency] at h
  norm_num [P, causalPolicy, sourcePolicy] at h
  simpa [P, causalPolicy, sourcePolicy] using h.trans_lt hε

theorem source_maximizing_strictly_dominated (γ : ℝ) (θ : World) (P : Policy)
    (hp : SourceAdmissible P)
    (hmax : ∀ R, SourceAdmissible R → objective γ R θ ≤ objective γ P θ) :
    CausalFinitaryDominates PhysicalEntropyControl.response
      (causalPolicy (sourcePolicy 1 (by norm_num) (by norm_num))) (causalPolicy P) ∧
    ¬ CausalFinitaryDominates PhysicalEntropyControl.response (causalPolicy P)
      (causalPolicy (sourcePolicy 1 (by norm_num) (by norm_num))) := by
  have hgreat := (causalNativelySufficient_iff_finitarilyGreatest _
    PhysicalEntropyControl.response_valid _).1 source_read_sufficient
  refine ⟨hgreat (causalPolicy P), ?_⟩
  intro hback
  have hsuff := (causalNativelySufficient_iff_finitarilyGreatest _
    PhysicalEntropyControl.response_valid (causalPolicy P)).2
      (fun ρ => causalFinitaryDominates_trans _ PhysicalEntropyControl.response_valid hback (hgreat ρ))
  obtain ⟨T, hT⟩ := hsuff 1 (1/3) (by norm_num)
  have h := hT (T+1) (by omega) PhysicalEntropyControl.readPlan
  rw [(source_maximizing_native_loss γ θ P hp hmax).1 T] at h
  exact lt_irrefl _ h

theorem source_optimizer_family_limit (γ : ℕ → ℝ) (P : ℕ → Policy) (θ : World)
    (hp : ∀ n, SourceAdmissible (P n))
    (hmax : ∀ n R, SourceAdmissible R → objective (γ n) R θ ≤ objective (γ n) (P n) θ) :
    Tendsto (fun n => eventualDeficiency (P n)) atTop (nhds (1/3)) := by
  have he (n : ℕ) := source_maximizing_eventualDeficiency (γ n) θ (P n) (hp n) (hmax n)
  simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1/3 : ℝ)) atTop (nhds (1/3)))

end
end IdExp.MOPFiniteMDP
