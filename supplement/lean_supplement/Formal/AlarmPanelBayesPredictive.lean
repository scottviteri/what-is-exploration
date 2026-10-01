import Formal.AlarmPanelPosterior
import Formal.AlarmPanelControl
import Formal.SurprisalDecomposition
import Formal.KnownNoisePredictionError

/-! Exact Bayesian next-observation prediction on the alarm/panel interface.
Predictive masses integrate actual full records under the fixed countable prior.
The action is conditioned on. Coordinates are raw observation labels, not a
freely optimized encoder. Null prefixes receive an irrelevant uniform fallback. -/
namespace IdExp.AlarmPanelBayes
open MeasureTheory Finset
open AlarmPanel
noncomputable section
abbrev prior := AlarmPanelPrior.prior
abbrev record (π : ValidCausalPolicy Action Observation) (n : ℕ) := experiment π.1 n
abbrev Trace (n : ℕ) := CausalFiniteTrace Action Observation n

theorem record_valid (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    IsFiniteExperiment (record π n) := experiment_valid π.1 π.2 n

theorem record_integrable (π : ValidCausalPolicy Action Observation) (n : ℕ) (u : Trace n) :
    Integrable (fun θ => record π n θ u) prior :=
  integrable_measurableFiniteExperiment_coordinate prior _ (record_valid π n)
    (fun _ => measurable_of_countable _) u

def mass (π : ValidCausalPolicy Action Observation) (n : ℕ) : Trace n → ℝ :=
  priorSignalMass prior (record π n)

theorem mass_valid (π : ValidCausalPolicy Action Observation) (n : ℕ) : IsDist (mass π n) :=
  priorSignalMass_isDist prior _ (record_valid π n) (record_integrable π n)

/-- Joint prefix/next-observation mass, before the next action probability. -/
def joint (π : ValidCausalPolicy Action Observation) (n : ℕ) (u : Trace n)
    (a : Action) (o : Observation) : ℝ :=
  ∫ θ, record π n θ u * response θ (List.ofFn u) a o ∂prior

theorem joint_integrable (π : ValidCausalPolicy Action Observation) (n : ℕ)
    (u : Trace n) (a : Action) (o : Observation) :
    Integrable (fun θ => record π n θ u * response θ (List.ofFn u) a o) prior := by
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
  filter_upwards [] with θ
  have hk := (record_valid π n θ).1 u
  have hq := (response_valid θ (List.ofFn u) a).1 o
  have hk1 : record π n θ u ≤ 1 :=
    (single_le_sum (fun v _ => (record_valid π n θ).1 v) (mem_univ u)).trans_eq
      (record_valid π n θ).2
  have hq1 : response θ (List.ofFn u) a o ≤ 1 :=
    (single_le_sum (fun v _ => (response_valid θ (List.ofFn u) a).1 v) (mem_univ o)).trans_eq
      (response_valid θ (List.ofFn u) a).2
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hk hq)]
  nlinarith

theorem joint_nonneg (π : ValidCausalPolicy Action Observation) (n : ℕ)
    (u : Trace n) (a : Action) (o : Observation) : 0 ≤ joint π n u a o :=
  integral_nonneg fun θ => mul_nonneg ((record_valid π n θ).1 u)
    ((response_valid θ (List.ofFn u) a).1 o)

theorem joint_sum (π : ValidCausalPolicy Action Observation) (n : ℕ)
    (u : Trace n) (a : Action) : ∑ o, joint π n u a o = mass π n u := by
  unfold joint mass priorSignalMass
  rw [← integral_finsetSum _ (fun o _ => joint_integrable π n u a o)]
  simp_rw [← mul_sum, (response_valid _ _ _).2, mul_one]

theorem mass_snoc (π : ValidCausalPolicy Action Observation) (n : ℕ)
    (u : Trace n) (a : Action) (o : Observation) :
    mass π (n+1) (Fin.snoc u (a,o)) = π.1 (List.ofFn u) a * joint π n u a o := by
  unfold mass priorSignalMass joint
  simp_rw [record, experiment, causalFiniteExperiment_snoc]
  rw [← integral_const_mul]
  congr 1
  funext θ
  ring

/-- Bayes' rule for the next raw observation. -/
def predictive (π : ValidCausalPolicy Action Observation) (n : ℕ) (u : Trace n)
    (a : Action) (o : Observation) : ℝ :=
  if mass π n u = 0 then uniformDist o else joint π n u a o / mass π n u

theorem predictive_valid (π : ValidCausalPolicy Action Observation) (n : ℕ)
    (u : Trace n) (a : Action) : IsDist (predictive π n u a) := by
  by_cases hm : mass π n u = 0
  · change IsDist (fun o => if mass π n u = 0 then uniformDist o else _)
    simp only [hm, if_true]
    exact uniformDist_valid
  · constructor
    · intro o
      simpa [predictive, hm] using
        div_nonneg (joint_nonneg π n u a o) ((mass_valid π n).1 u)
    · simp only [predictive, hm, if_false, ← sum_div, joint_sum, div_self hm]

theorem mass_mul_predictive (π : ValidCausalPolicy Action Observation) (n : ℕ)
    (u : Trace n) (a : Action) (o : Observation) :
    mass π n u * predictive π n u a o = joint π n u a o := by
  by_cases hm : mass π n u = 0
  · have hj : joint π n u a o = 0 := by
      have h := single_le_sum (fun v _ => joint_nonneg π n u a v) (mem_univ o)
      rw [joint_sum, hm] at h
      exact le_antisymm h (joint_nonneg π n u a o)
    simp [hm, hj]
  · simp [predictive, hm, mul_div_cancel₀]

/-- Literal expected loss on the newest observation of the actual record. -/
def stage (loss : (Observation → ℝ) → Observation → ℝ)
    (π : ValidCausalPolicy Action Observation) (n : ℕ) : ℝ :=
  ∑ u : Trace n, ∑ a, ∑ o,
    mass π (n+1) (Fin.snoc u (a,o)) * loss (predictive π n u a) o

theorem stage_eq (loss : (Observation → ℝ) → Observation → ℝ)
    (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    stage loss π n = ∑ u : Trace n, mass π n u * ∑ a, π.1 (List.ofFn u) a *
      ∑ o, predictive π n u a o * loss (predictive π n u a) o := by
  simp only [stage, mul_sum, mass_snoc, ← mass_mul_predictive π n]
  apply sum_congr rfl; intro u _
  apply sum_congr rfl; intro a _
  apply sum_congr rfl; intro o _
  ring

def logLoss (q : Observation → ℝ) (o : Observation) : ℝ := -Real.log (q o)
def logStage := stage logLoss
def squaredStage := stage oneHotSquaredError

theorem logStage_eq (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    logStage π n = ∑ u : Trace n, mass π n u * ∑ a, π.1 (List.ofFn u) a *
      ent (predictive π n u a) := by
  rw [logStage, stage_eq]
  simp only [logLoss, ent, Real.negMulLog, mul_neg, neg_mul]

theorem squaredStage_eq (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    squaredStage π n = ∑ u : Trace n, mass π n u * ∑ a, π.1 (List.ofFn u) a *
      (1 - ∑ o, predictive π n u a o ^ 2) := by
  rw [squaredStage, stage_eq]
  apply sum_congr rfl; intro u _
  congr 1
  apply sum_congr rfl; intro a _
  congr 1
  exact expectedOneHotSquaredError_self _ (predictive_valid π n u a)

theorem logStage_nonneg (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    0 ≤ logStage π n := by
  rw [logStage_eq]
  apply sum_nonneg; intro u _
  apply mul_nonneg ((mass_valid π n).1 u)
  apply sum_nonneg; intro a _
  exact mul_nonneg ((π.2 _).1 a) (ent_nonneg_of_isDist _ (predictive_valid π n u a))

theorem squaredStage_nonneg (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    0 ≤ squaredStage π n := by
  apply sum_nonneg; intro u _
  apply sum_nonneg; intro a _
  apply sum_nonneg; intro o _
  exact mul_nonneg ((mass_valid π (n+1)).1 _) (sum_nonneg fun _ _ => sq_nonneg _)

end
end IdExp.AlarmPanelBayes
