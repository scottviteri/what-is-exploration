import Formal.DIAYNStateMDP
import Formal.DIAYNInformation

/-! The original DIAYN state-information and action-entropy objective on actual
limiting state visitation in each fixed MDP. Every stationary Markov skill policy
is feasible. No unknown-world pooling occurs inside either entropy. -/
namespace IdExp.DIAYNState
open Finset
noncomputable section

/-- Actual conditional law of action and stationary physical state, given skill. -/
def actionStateLaw (P : Policy) (θ : World) (z : Skill) : Action × State → ℝ :=
  fun p => stateExperiment P θ z p.2 * (P z p.2).1 p.1

theorem actionStateLaw_valid (P : Policy) (θ : World) (z : Skill) :
    IsDist (actionStateLaw P θ z) := by
  constructor
  · intro p
    exact mul_nonneg ((stateExperiment_valid P θ z).1 p.2) ((P z p.2).2.1 p.1)
  · unfold actionStateLaw
    rw [Fintype.sum_prod_type, sum_comm]
    simp only [← mul_sum, (P _ _).2.2, mul_one]
    exact (stateExperiment_valid P θ z).2

/-- This is the actual state-action law at every positive collection time. -/
theorem actionStateLaw_eq_actual (P : Policy) (θ : World) (z : Skill) (n : ℕ) :
    actionStateLaw P θ z = fun p : Action × State =>
      stateActionMarginal P z θ (n+1) p.2 p.1 := by
  funext p
  exact (policy_stateActionMarginal_succ P z θ n p.2 p.1).symm

/-- Mutual information between the fair skill and actual stationary state. -/
def stateInformation (P : Policy) (θ : World) : ℝ :=
  finiteBayesInformation (uniformPrior Skill) (stateExperiment P θ)

/-- H(A | S,Z), with the same state distribution as in the information term. -/
def actionEntropy (P : Policy) (θ : World) : ℝ :=
  ∑ z, uniformPrior Skill z * finiteConditionalEntropy (actionStateLaw P θ z)

/-- The source objective; alpha=1 is its displayed theoretical expression. -/
def objective (P : Policy) (θ : World) (α : ℝ) : ℝ :=
  stateInformation P θ + α * actionEntropy P θ

/-- The observed branch states retain exactly the initial action information. -/
theorem stateInformation_eq_root (P : Policy) (θ : World) :
    stateInformation P θ = finiteBayesInformation (uniformPrior Skill) (rootExperiment P) := by
  apply le_antisymm
  · exact finiteBayesInformation_garble_le _ isDist_uniformPrior
      (rootExperiment P) (rootExperiment_valid P) (diracExp (branch θ))
      (fun a _ => diracExp_valid _ a)
  · have h := finiteBayesInformation_garble_le (uniformPrior Skill) isDist_uniformPrior
      (stateExperiment P θ) (stateExperiment_valid P θ) (diracExp actionOfState)
      (fun s _ => diracExp_valid _ s)
    rw [stateExperiment_decode] at h
    exact h

theorem stateInformation_le (P : Policy) (θ : World) :
    stateInformation P θ ≤ Real.log 2 := by
  simpa [stateInformation] using finiteBayesInformation_le_ent (uniformPrior Skill)
    isDist_uniformPrior (stateExperiment P θ) (stateExperiment_valid P θ)

theorem actionEntropy_le (P : Policy) (θ : World) : actionEntropy P θ ≤ Real.log 3 := by
  calc
    _ ≤ ∑ z, uniformPrior Skill z * Real.log 3 := by
      apply sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left _ (isDist_uniformPrior.1 z)
      simpa using finiteConditionalEntropy_le _ (actionStateLaw_valid P θ z)
    _ = _ := by rw [← sum_mul, isDist_uniformPrior.2, one_mul]

theorem objective_le (P : Policy) (θ : World) {α : ℝ} (hα : 0 ≤ α) :
    objective P θ α ≤ Real.log 2 + α * Real.log 3 :=
  add_le_add (stateInformation_le P θ) (mul_le_mul_of_nonneg_left (actionEntropy_le P θ) hα)

/-- A continuum of disjoint root choices, parametrized by the collector's READ mass. -/
def witnessRoot (s : ℝ) (z : Skill) : Action → ℝ :=
  if z = 0 then ![2*s, 1-2*s, 0] else ![0, 0, 1]

theorem witnessRoot_valid {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1/2) (z : Skill) :
    IsDist (witnessRoot s z) := by
  constructor
  · intro a
    fin_cases z <;> fin_cases a <;> simp [witnessRoot] <;> linarith
  · fin_cases z <;> simp [witnessRoot, Fin.sum_univ_three]

def witness (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1/2) : Policy :=
  fun z st => if st = none then ⟨witnessRoot s z, witnessRoot_valid hs0 hs1 z⟩
    else ⟨uniformPrior Action, isDist_uniformPrior⟩

theorem witness_root (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1/2) (z : Skill) :
    rootExperiment (witness s hs0 hs1) z = witnessRoot s z := by
  funext a
  simp [rootExperiment, witness]

theorem witness_information (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1/2) (θ : World) :
    stateInformation (witness s hs0 hs1) θ = Real.log 2 := by
  rw [stateInformation_eq_root]
  apply (binary_information_max_iff_disjoint _ (rootExperiment_valid _)).2
  intro a
  rw [witness_root, witness_root]
  fin_cases a <;> simp [witnessRoot]

theorem actionEntropy_eq (P : Policy) (θ : World) :
    actionEntropy P θ = ∑ z, uniformPrior Skill z *
      ∑ st, stateExperiment P θ z st * ent ((P z st).1) := by
  unfold actionEntropy
  apply sum_congr rfl
  intro z _
  exact congrArg (fun v => uniformPrior Skill z * v)
    (finiteConditionalEntropy_kernel (stateExperiment P θ z)
      (fun st => (P z st).1) (fun st => (P z st).2))

theorem witness_actionEntropy (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1/2) (θ : World) :
    actionEntropy (witness s hs0 hs1) θ = Real.log 3 := by
  rw [actionEntropy_eq]
  have ht (z : Skill) (st : State) :
      stateExperiment (witness s hs0 hs1) θ z st * ent ((witness s hs0 hs1 z st).1) =
      stateExperiment (witness s hs0 hs1) θ z st * Real.log 3 := by
    cases st with
    | none => simp [stateExperiment_none]
    | some x => simp [witness, ent_uniformPrior]
  simp only [ht, ← sum_mul, (stateExperiment_valid _ _ _).2, one_mul,
    isDist_uniformPrior.2]

theorem witness_objective (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1/2)
    (θ : World) (α : ℝ) :
    objective (witness s hs0 hs1) θ α = Real.log 2 + α * Real.log 3 := by
  rw [objective, witness_information, witness_actionEntropy]

/-- Optimization is over all stationary, randomized state-conditioned skill policies. -/
def Maximizes (P : Policy) (θ : World) (α : ℝ) : Prop :=
  ∀ Q : Policy, objective Q θ α ≤ objective P θ α

theorem maximizes_iff (P : Policy) (θ : World) {α : ℝ} (hα : 0 ≤ α) :
    Maximizes P θ α ↔ objective P θ α = Real.log 2 + α * Real.log 3 := by
  constructor
  · intro h
    apply le_antisymm (objective_le P θ hα)
    simpa [witness_objective] using h (witness 0 (by norm_num) (by norm_num))
  · intro h Q
    rw [h]
    exact objective_le Q θ hα

theorem witness_maximizes (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1/2)
    (θ : World) {α : ℝ} (hα : 0 ≤ α) : Maximizes (witness s hs0 hs1) θ α :=
  (maximizes_iff _ _ hα).2 (witness_objective s hs0 hs1 θ α)

theorem maximizer_information (P : Policy) (θ : World) {α : ℝ} (hα : 0 < α)
    (hP : Maximizes P θ α) : stateInformation P θ = Real.log 2 := by
  have h := (maximizes_iff P θ hα.le).1 hP
  have hi := stateInformation_le P θ
  have he := actionEntropy_le P θ
  unfold objective at h
  nlinarith

theorem maximizer_root_disjoint (P : Policy) (θ : World) {α : ℝ} (hα : 0 < α)
    (hP : Maximizes P θ α) : ∀ a, rootExperiment P 0 a = 0 ∨ rootExperiment P 1 a = 0 := by
  apply (binary_information_max_iff_disjoint _ (rootExperiment_valid P)).1
  rw [← stateInformation_eq_root P θ]
  exact maximizer_information P θ hα hP

theorem maximizer_root_read_bound (P : Policy) (θ : World) {α : ℝ} (hα : 0 < α)
    (hP : Maximizes P θ α) : rootExperiment P 0 0 + rootExperiment P 1 0 ≤ 1 := by
  have hu (z : Skill) : rootExperiment P z 0 ≤ 1 := by
    exact (single_le_sum (fun a _ => (rootExperiment_valid P z).1 a) (mem_univ 0)).trans_eq
      (rootExperiment_valid P z).2
  rcases maximizer_root_disjoint P θ hα hP 0 with h | h
  · simpa [h] using hu 1
  · simpa [h] using hu 0

end
end IdExp.DIAYNState
