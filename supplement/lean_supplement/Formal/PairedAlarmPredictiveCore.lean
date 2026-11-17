import Formal.PairedAlarmNativeExtraction
import Formal.AlarmPanelPrior
import Formal.SurprisalDecomposition
import Formal.ControlEntropy
import Formal.MeasurableInformationForms

/-!
# Exact Bayesian next-observation prediction on the paired alarm

On the paired interface (`Formal.PairedAlarm`), the forecast
`q(o | h, a)` of the next raw observation `o = (display, monitor)` is the
literal Bayes predictive law under the fixed countable geometric prior: the
joint prior mass of the full retained record `h` followed by the proposed action
`a` and observation `o`, divided by the prior mass of `h`. The action is
conditioned on, the whole action-observation record is retained, and the
scored variable is the raw observation pair. Null records receive an irrelevant
uniform fallback.

The per-step Shannon utility is `-log₂ q(o | h, a)` and the per-step Square
utility is `-q(o | h, a)` (Aslanides 2016, Definitions 16-17). A stage value is
the expectation of the utility of the newest observation under the joint law of
prior, environment, and an arbitrary randomized history policy.

All declarations live in `IdExp.PairedAlarm.Predictive`.
-/

noncomputable section
namespace IdExp.PairedAlarm.Predictive
open MeasureTheory Finset

/-- The fixed countable full-support prior: `α(none) = 1/2`, `α(some k) = 2^{-(k+2)}`. -/
abbrev prior := AlarmPanelPrior.prior
/-- The literal collected experiment of a valid policy at horizon `n`. -/
abbrev record (π : ValidCausalPolicy Action Observation) (n : ℕ) := experiment π.1 n
abbrev Trace (n : ℕ) := CausalFiniteTrace Action Observation n

theorem record_valid (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    IsFiniteExperiment (record π n) := experiment_valid π.1 π.2 n

theorem record_integrable (π : ValidCausalPolicy Action Observation) (n : ℕ) (u : Trace n) :
    Integrable (fun θ => record π n θ u) prior :=
  integrable_measurableFiniteExperiment_coordinate prior _ (record_valid π n)
    (fun _ => measurable_of_countable _) u

/-- Prior-predictive mass of a full retained record. -/
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

/-- An irrelevant uniform forecast, used only at null records. -/
def fallback (_ : Observation) : ℝ := 1/8

theorem fallback_valid : IsDist fallback := by
  constructor
  · intro o; norm_num [fallback]
  · simp only [fallback, sum_const, card_univ, Fintype.card_prod, Fintype.card_fin]
    norm_num

/-- Bayes' rule for the next raw observation pair, given the full retained
record and the proposed action. -/
def predictive (π : ValidCausalPolicy Action Observation) (n : ℕ) (u : Trace n)
    (a : Action) (o : Observation) : ℝ :=
  if mass π n u = 0 then fallback o else joint π n u a o / mass π n u

theorem predictive_valid (π : ValidCausalPolicy Action Observation) (n : ℕ)
    (u : Trace n) (a : Action) : IsDist (predictive π n u a) := by
  by_cases hm : mass π n u = 0
  · change IsDist (fun o => if mass π n u = 0 then fallback o else _)
    simp only [hm, if_true]
    exact fallback_valid
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

/-- Away from null records, the forecast averages the worlds' response laws under the
actual countable-prior posterior given the full retained record. -/
theorem predictive_eq_posterior_average (π : ValidCausalPolicy Action Observation) (n : ℕ)
    (u : Trace n) (hm : mass π n u ≠ 0) (a : Action) (o : Observation) :
    predictive π n u a o =
      ∫ θ, response θ (List.ofFn u) a o ∂(priorPosteriorMeasure prior (record π n) u) := by
  rw [priorPosteriorMeasure, integral_withDensity_eq_integral_toReal_smul
    (measurable_of_countable _) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (priorSignalDensity_nonneg prior _ (record_valid π n) u _),
    smul_eq_mul]
  have hm' : priorSignalMass prior (record π n) u ≠ 0 := hm
  simp only [priorSignalDensity, if_neg hm', predictive, if_neg hm, joint]
  rw [← integral_div]
  congr 1
  funext θ
  change _ = record π n θ u / mass π n u * _
  ring

/-- Literal expected utility of the newest observation of the actual record:
`E[r(H_n, A_{n+1}, O_{n+1})]` under prior, environment, and policy. -/
def stage (utility : (Observation → ℝ) → Observation → ℝ)
    (π : ValidCausalPolicy Action Observation) (n : ℕ) : ℝ :=
  ∑ u : Trace n, ∑ a, ∑ o,
    mass π (n+1) (Fin.snoc u (a,o)) * utility (predictive π n u a) o

theorem stage_eq (utility : (Observation → ℝ) → Observation → ℝ)
    (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    stage utility π n = ∑ u : Trace n, mass π n u * ∑ a, π.1 (List.ofFn u) a *
      ∑ o, predictive π n u a o * utility (predictive π n u a) o := by
  simp only [stage, mul_sum, mass_snoc, ← mass_mul_predictive π n]
  apply sum_congr rfl; intro u _
  apply sum_congr rfl; intro a _
  apply sum_congr rfl; intro o _
  ring

/-- The source's per-step Shannon utility, in bits. -/
def shannonUtility (q : Observation → ℝ) (o : Observation) : ℝ := -Real.logb 2 (q o)

/-- The source's per-step Square utility (not whole-history Square-KSA). -/
def squareUtility (q : Observation → ℝ) (o : Observation) : ℝ := -q o

def shannonStage (π : ValidCausalPolicy Action Observation) (n : ℕ) : ℝ :=
  stage shannonUtility π n

def squareStage (π : ValidCausalPolicy Action Observation) (n : ℕ) : ℝ :=
  stage squareUtility π n

/-- The expected Shannon utility of a forecast under itself is its entropy in bits. -/
theorem expected_shannonUtility (q : Observation → ℝ) :
    ∑ o, q o * shannonUtility q o = ent q / Real.log 2 := by
  simp only [shannonUtility, ent, Real.negMulLog, Real.logb, sum_div]
  apply sum_congr rfl; intro o _
  ring

theorem expected_squareUtility (q : Observation → ℝ) :
    ∑ o, q o * squareUtility q o = -∑ o, q o ^ 2 := by
  simp only [squareUtility, ← sum_neg_distrib]
  apply sum_congr rfl; intro o _
  ring

theorem shannonStage_eq (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    shannonStage π n = ∑ u : Trace n, mass π n u * ∑ a, π.1 (List.ofFn u) a *
      (ent (predictive π n u a) / Real.log 2) := by
  simp only [shannonStage, stage_eq, expected_shannonUtility]

theorem squareStage_eq (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    squareStage π n = ∑ u : Trace n, mass π n u * ∑ a, π.1 (List.ofFn u) a *
      (-∑ o, predictive π n u a o ^ 2) := by
  simp only [squareStage, stage_eq, expected_squareUtility]

/-- A bound on every history/action value bounds its policy average. -/
theorem average_le (π : ValidCausalPolicy Action Observation) (n : ℕ)
    (f : Trace n → Action → ℝ) (c : ℝ) (hf : ∀ u a, f u a ≤ c) :
    ∑ u : Trace n, mass π n u * ∑ a, π.1 (List.ofFn u) a * f u a ≤ c := by
  calc
    _ ≤ ∑ u : Trace n, mass π n u * ∑ a, π.1 (List.ofFn u) a * c := by
      apply sum_le_sum; intro u _
      apply mul_le_mul_of_nonneg_left _ ((mass_valid π n).1 u)
      apply sum_le_sum; intro a _
      exact mul_le_mul_of_nonneg_left (hf u a) ((π.2 _).1 a)
    _ = c := by simp only [← sum_mul, (π.2 _).2, one_mul, (mass_valid π n).2]

theorem le_average (π : ValidCausalPolicy Action Observation) (n : ℕ)
    (f : Trace n → Action → ℝ) (c : ℝ) (hf : ∀ u a, c ≤ f u a) :
    c ≤ ∑ u : Trace n, mass π n u * ∑ a, π.1 (List.ofFn u) a * f u a := by
  calc
    c = ∑ u : Trace n, mass π n u * ∑ a, π.1 (List.ofFn u) a * c := by
      simp only [← sum_mul, (π.2 _).2, one_mul, (mass_valid π n).2]
    _ ≤ _ := by
      apply sum_le_sum; intro u _
      apply mul_le_mul_of_nonneg_left _ ((mass_valid π n).1 u)
      apply sum_le_sum; intro a _
      exact mul_le_mul_of_nonneg_left (hf u a) ((π.2 _).1 a)

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem shannonStage_nonneg (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    0 ≤ shannonStage π n := by
  rw [shannonStage_eq]
  exact le_average π n _ 0 fun u a =>
    div_nonneg (ent_nonneg_of_isDist _ (predictive_valid π n u a)) log_two_pos.le

/-- There are eight raw labels, so the expected Shannon stage is at most three bits. -/
theorem shannonStage_le_three (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    shannonStage π n ≤ 3 := by
  rw [shannonStage_eq]
  apply average_le π n _ 3
  intro u a
  have he := ent_le_log_card _ (predictive_valid π n u a)
  have hc : (Fintype.card Observation : ℝ) = 2^3 := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    norm_num
  rw [hc, Real.log_pow] at he
  rw [div_le_iff₀ log_two_pos]
  push_cast at he
  linarith

theorem sum_sq_le_one (q : Observation → ℝ) (hq : IsDist q) : ∑ o, q o ^ 2 ≤ 1 := by
  calc
    ∑ o, q o ^ 2 ≤ ∑ o, q o := by
      apply sum_le_sum; intro o _
      have h0 := hq.1 o
      have h1 : q o ≤ 1 :=
        (single_le_sum (fun v _ => hq.1 v) (mem_univ o)).trans_eq hq.2
      nlinarith
    _ = 1 := hq.2

theorem squareStage_nonpos (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    squareStage π n ≤ 0 := by
  rw [squareStage_eq]
  exact average_le π n _ 0 fun u a =>
    neg_nonpos.mpr (sum_nonneg fun o _ => sq_nonneg _)

theorem neg_one_le_squareStage (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    -1 ≤ squareStage π n := by
  rw [squareStage_eq]
  exact le_average π n _ (-1) fun u a =>
    neg_le_neg (sum_sq_le_one _ (predictive_valid π n u a))

end IdExp.PairedAlarm.Predictive
