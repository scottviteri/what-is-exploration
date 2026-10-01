import Formal.ControlEntropy
import Formal.CausalSharedTailExact
import Formal.AbsorbingExperiment

/-!
# Literal stochastic physical-entropy control counterexample

There are two root actions: action zero reveals the fixed world bit and
action one produces an independent fair label. Every resulting observed
physical state has two actions, both self-loops. Policies may randomize and
depend on the entire retained history. The reward is action entropy plus
entropy of the physical transition in the fixed world, not posterior
predictive entropy. All logarithms are natural.
-/

namespace IdExp.PhysicalEntropyControl
open Finset
noncomputable section

abbrev World := Fin 2
abbrev Action := Fin 2
abbrev Observation := Fin 4

/-- Observations zero and one reveal the bit; two and three are known noise. -/
def root (a : Action) (θ : World) : Observation → ℝ :=
  if a = 0 then ![if θ = 0 then 1 else 0, if θ = 1 then 1 else 0, 0, 0]
  else ![0, 0, 1/2, 1/2]

theorem root_valid (a : Action) : IsFiniteExperiment (root a) := by
  intro θ
  constructor
  · intro o
    fin_cases a <;> fin_cases θ <;> fin_cases o <;> norm_num [root]
  · fin_cases a <;> fin_cases θ <;> norm_num [root, Fin.sum_univ_succ]

/-- The last observed physical state. The default is used only at the root. -/
def state (h : CausalHistory Action Observation) : Observation :=
  (h.reverse.headD (0, 0)).2

/-- Both available actions stay at the current observed physical state. -/
def stay : CausalResponse Action Observation :=
  fun h _ o => if o = state h then 1 else 0

theorem stay_valid : IsCausalResponse stay := by
  intro h a
  constructor
  · intro o; simp only [stay]; split_ifs <;> norm_num
  · simp [stay]

def response (θ : World) : CausalResponse Action Observation :=
  fun h a o => if h = [] then root a θ o else stay h a o

@[simp] theorem response_root (θ : World) (a : Action) : response θ [] a = root a θ := by
  funext o
  simp [response]

theorem response_tail (θ : World) (h : CausalHistory Action Observation)
    (a : Action) (hh : h ≠ []) : response θ h a = stay h a := by
  funext o
  simp [response, hh]

theorem response_valid (θ : World) : IsCausalResponse (response θ) := by
  intro h a
  by_cases hh : h = []
  · subst h; rw [response_root]; exact root_valid a θ
  · rw [response_tail θ h a hh]; exact stay_valid h a

theorem response_sharedTail : HasSharedCausalTail response 1 stay := by
  intro θ h a o hh
  have hne : h ≠ [] := by intro hz; simp [hz] at hh
  simp [response, hne]

/-- Physical transition entropy, evaluated separately in each actual world. -/
def localReward (π : CausalPolicy Action Observation) (θ : World)
    (h : CausalHistory Action Observation) : ℝ :=
  ent (π h) + ∑ a, π h a * ent (response θ h a)

/-- Expected stage reward under the fair prior on the fixed world bit. -/
def stageReward (π : ValidCausalPolicy Action Observation) (t : ℕ) : ℝ :=
  ∑ θ : World, (1/2 : ℝ) * ∑ w : CausalFiniteTrace Action Observation t,
    causalFiniteExperiment π.1 response t θ w * localReward π.1 θ (List.ofFn w)

/-- Literal infinite discounted physical MOP return, with both coefficients one. -/
def objective (γ : ℝ) (π : ValidCausalPolicy Action Observation) : ℝ :=
  ∑' t, γ^t * stageReward π t

theorem root_entropy (a : Action) (θ : World) :
    ent (root a θ) = if a = 0 then 0 else Real.log 2 := by
  have hhalf : Real.negMulLog (1/2 : ℝ) = Real.log 2 / 2 := by
    simp [Real.negMulLog, one_div, Real.log_inv]; ring
  fin_cases a <;> fin_cases θ <;>
    norm_num [root, ent, Fin.sum_univ_succ, hhalf]

theorem stay_entropy (h : CausalHistory Action Observation) (a : Action) :
    ent (stay h a) = 0 := by
  apply sum_eq_zero
  intro o _
  simp only [stay]
  split_ifs <;> simp

theorem policy_root_other (π : ValidCausalPolicy Action Observation) :
    π.1 [] 1 = 1 - π.1 [] 0 := by
  have h := (π.2 []).2
  rw [Fin.sum_univ_two] at h
  linarith

theorem policy_root_bounds (π : ValidCausalPolicy Action Observation) :
    0 ≤ π.1 [] 0 ∧ π.1 [] 0 ≤ 1 := by
  refine ⟨(π.2 []).1 0, ?_⟩
  have hn := (π.2 []).1 1
  rw [policy_root_other] at hn
  linarith

theorem localReward_root (π : ValidCausalPolicy Action Observation) (θ : World) :
    localReward π.1 θ [] = splitBinaryEntropy (π.1 [] 0) := by
  simp only [localReward, response_root, root_entropy, Fin.sum_univ_two]
  norm_num
  rw [show ent (π.1 []) = Real.negMulLog (π.1 [] 0) + Real.negMulLog (π.1 [] 1) by simp [ent, Fin.sum_univ_two], policy_root_other]
  rfl

theorem localReward_tail (π : CausalPolicy Action Observation) (θ : World)
    (h : CausalHistory Action Observation) (hh : h ≠ []) :
    localReward π θ h = ent (π h) := by
  simp [localReward, response_tail _ _ _ hh, stay_entropy]

theorem stageReward_nonneg (π : ValidCausalPolicy Action Observation) (t : ℕ) :
    0 ≤ stageReward π t := by
  apply sum_nonneg
  intro θ _
  apply mul_nonneg (by norm_num)
  apply sum_nonneg
  intro w _
  apply mul_nonneg ((causalFiniteExperiment_valid π.1 π.2 response response_valid t θ).1 w)
  apply add_nonneg (ent_nonneg_of_isDist _ (π.2 _))
  apply sum_nonneg
  intro a _
  exact mul_nonneg ((π.2 _).1 a)
    (ent_nonneg_of_isDist _ (response_valid θ _ a))

theorem stageReward_zero (π : ValidCausalPolicy Action Observation) :
    stageReward π 0 = splitBinaryEntropy (π.1 [] 0) := by
  simp [stageReward, causalFiniteExperiment, causalTraceProb, causalTraceProbFrom,
    localReward_root]

theorem stageReward_succ_le (π : ValidCausalPolicy Action Observation) (t : ℕ) :
    stageReward π (t+1) ≤ Real.log 2 := by
  have hθ (θ : World) :
      (∑ w : CausalFiniteTrace Action Observation (t+1),
        causalFiniteExperiment π.1 response (t+1) θ w *
          localReward π.1 θ (List.ofFn w)) ≤ Real.log 2 := by
    calc
      _ ≤ ∑ w : CausalFiniteTrace Action Observation (t+1),
          causalFiniteExperiment π.1 response (t+1) θ w * Real.log 2 := by
        apply sum_le_sum
        intro w _
        apply mul_le_mul_of_nonneg_left _
          ((causalFiniteExperiment_valid π.1 π.2 response response_valid (t+1) θ).1 w)
        rw [localReward_tail _ _ _ (by simp)]
        simpa using ent_le_log_card (π.1 (List.ofFn w)) (π.2 _)
      _ = Real.log 2 := by
        rw [← sum_mul, (causalFiniteExperiment_valid π.1 π.2 response response_valid (t+1) θ).2,
          one_mul]
  calc
    stageReward π (t+1) ≤ ∑ _θ : World, (1/2 : ℝ) * Real.log 2 := by
      exact sum_le_sum fun θ _ => mul_le_mul_of_nonneg_left (hθ θ) (by norm_num)
    _ = Real.log 2 := by simp

/-- Uniform tail actions attain the physical-control ceiling, regardless of
which root branch occurred. The root itself is an arbitrary Bernoulli row. -/
def uniformTail (s : ℝ) : CausalPolicy Action Observation :=
  fun h => if h = [] then ![s, 1-s] else uniformPrior Action

theorem uniformTail_valid {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    IsCausalPolicy (uniformTail s) := by
  intro h
  by_cases hh : h = []
  · constructor
    · intro a; fin_cases a <;> simp [uniformTail, hh] <;> linarith
    · simp [uniformTail, hh, Fin.sum_univ_two]
  · simpa [uniformTail, hh] using (isDist_uniformPrior (Θ := Action))

def optimizer : ValidCausalPolicy Action Observation :=
  ⟨uniformTail (1/3), uniformTail_valid (by norm_num) (by norm_num)⟩

theorem uniformTail_stageReward_succ {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (t : ℕ) :
    stageReward ⟨uniformTail s, uniformTail_valid hs0 hs1⟩ (t+1) = Real.log 2 := by
  have hlocal (θ : World) (w : CausalFiniteTrace Action Observation (t+1)) :
      localReward (uniformTail s) θ (List.ofFn w) = Real.log 2 := by
    have hh : List.ofFn w ≠ [] := by simp
    rw [localReward_tail _ _ _ hh]
    simp [uniformTail, ent_uniformPrior]
  simp only [stageReward, hlocal, ← sum_mul,
    (causalFiniteExperiment_valid (uniformTail s) (uniformTail_valid hs0 hs1)
      response response_valid (t+1) _).2, one_mul, Fin.sum_univ_two]
  ring

/-- A bound on the literal full return, uniformly over all stochastic policies. -/
theorem objective_le_root_add_tail (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (π : ValidCausalPolicy Action Observation) :
    objective γ π ≤ splitBinaryEntropy (π.1 [] 0) + γ * Real.log 2 / (1-γ) := by
  simpa only [objective, stageReward_zero] using
    discounted_le_root_add_tail hγ0 hγ1 (stageReward_nonneg π) (stageReward_succ_le π)

theorem objective_le (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (π : ValidCausalPolicy Action Observation) :
    objective γ π ≤ Real.log 3 + γ * Real.log 2 / (1-γ) :=
  (objective_le_root_add_tail γ hγ0 hγ1 π).trans
    (add_le_add (splitBinaryEntropy_le (policy_root_bounds π).1 (policy_root_bounds π).2) le_rfl)

theorem objective_uniformTail (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    objective γ ⟨uniformTail s, uniformTail_valid hs0 hs1⟩ =
      splitBinaryEntropy s + γ * Real.log 2 / (1-γ) := by
  let π : ValidCausalPolicy Action Observation := ⟨uniformTail s, uniformTail_valid hs0 hs1⟩
  have hsumm : Summable (fun t => γ^t * stageReward π t) :=
    summable_discounted_of_bounded hγ0 hγ1 (stageReward_nonneg π)
      (B := max (stageReward π 0) (Real.log 2)) (fun t => by
        cases t with
        | zero => exact le_max_left _ _
        | succ t => exact (stageReward_succ_le π t).trans (le_max_right _ _))
  change (∑' t, γ^t * stageReward π t) = _
  rw [hsumm.tsum_eq_zero_add]
  simp only [pow_zero, one_mul, stageReward_zero]
  change splitBinaryEntropy s + (∑' t, γ^(t+1) * stageReward π (t+1)) = _
  have htail (t : ℕ) : stageReward π (t+1) = Real.log 2 :=
    uniformTail_stageReward_succ hs0 hs1 t
  simp only [htail, pow_succ, mul_assoc, tsum_mul_right,
    tsum_geometric_of_lt_one hγ0 hγ1]
  ring

theorem objective_optimizer (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    objective γ optimizer = Real.log 3 + γ * Real.log 2 / (1-γ) := by
  rw [optimizer, objective_uniformTail γ hγ0 hγ1 (by norm_num) (by norm_num),
    (splitBinaryEntropy_eq_iff (by norm_num : (0:ℝ) ≤ 1/3)
      (by norm_num : (1/3:ℝ) ≤ 1)).2 rfl]

/-- The displayed stochastic policy really maximizes the full discounted
return among every history-dependent randomized causal policy. -/
theorem optimizer_maximizes (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (π : ValidCausalPolicy Action Observation) : objective γ π ≤ objective γ optimizer := by
  rw [objective_optimizer γ hγ0 hγ1]
  exact objective_le γ hγ0 hγ1 π

/-- Every maximizer, not just the displayed policy, reveals with probability
one third at the root. Tail action randomization cannot compensate for a
strictly smaller root entropy. -/
theorem maximizing_root_eq_third (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (π : ValidCausalPolicy Action Observation)
    (hmax : ∀ ρ : ValidCausalPolicy Action Observation, objective γ ρ ≤ objective γ π) :
    π.1 [] 0 = 1/3 := by
  apply (splitBinaryEntropy_eq_iff (policy_root_bounds π).1 (policy_root_bounds π).2).1
  apply le_antisymm (splitBinaryEntropy_le (policy_root_bounds π).1 (policy_root_bounds π).2)
  have hlo := hmax optimizer
  rw [objective_optimizer γ hγ0 hγ1] at hlo
  have hhi := objective_le_root_add_tail γ hγ0 hγ1 π
  linarith

end
end IdExp.PhysicalEntropyControl
