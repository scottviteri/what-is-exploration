import Formal.KnownNoiseMisranking
import Formal.ProperScoringRules

/-!
# Ideal one-hot prediction error prefers known noise

Squared error for a categorical observation is an affine transform of the
existing Brier report score. Its exact minimum over all real prediction vectors
is `1 - ∑ o, p o ^ 2`, attained by reporting `p`. This is irreducible observation
uncertainty, not posterior information about the world.

On the existing literal READ/NOISE causal interface, every action-conditioned
ideal predictor gives expected error `3/4 - P(READ)/4`. Rewarding that error
therefore makes every randomized policy optimum choose NOISE, whose full causal
record has deficiency one half against READ. The same causal experiment and
strict comparison endpoints are reused from `KnownNoiseMisranking`.
-/

namespace IdExp

open Finset
noncomputable section

/-- Squared Euclidean error against the observed categorical unit vector. -/
def oneHotSquaredError {O : Type*} [Fintype O] [DecidableEq O]
    (q : O → ℝ) (o : O) : ℝ :=
  ∑ x, (q x - if x = o then 1 else 0) ^ 2

/-- This loss and the existing Brier report score differ by a constant and sign. -/
theorem oneHotSquaredError_eq_one_sub_brierScore
    {O : Type*} [Fintype O] [DecidableEq O] (q : O → ℝ) (o : O) :
    oneHotSquaredError q o = 1 - brierScore q o := by
  have hh (x : O) : (q x - if x = o then 1 else 0) ^ 2 =
      q x ^ 2 + if x = o then 1 - 2 * q x else 0 := by
    split_ifs <;> ring
  simp only [oneHotSquaredError, hh, Finset.sum_add_distrib]
  simp [brierScore, posteriorQuadraticPotential]
  ring

/-- Expected categorical squared prediction error under the true law `p`. -/
def expectedOneHotSquaredError {O : Type*} [Fintype O] [DecidableEq O]
    (p q : O → ℝ) : ℝ := ∑ o, p o * oneHotSquaredError q o

/-- Exact Bayes risk plus squared prediction error from misspecifying the law.
The prediction vector may be any real vector, without a simplex restriction. -/
theorem expectedOneHotSquaredError_eq
    {O : Type*} [Fintype O] [DecidableEq O]
    (p : O → ℝ) (hp : IsDist p) (q : O → ℝ) :
    expectedOneHotSquaredError p q =
      1 - posteriorQuadraticPotential p + posteriorQuadraticPotential (p - q) := by
  have he : expectedOneHotSquaredError p q = 1 - expectedScore brierScore p q := by
    simp only [expectedOneHotSquaredError, oneHotSquaredError_eq_one_sub_brierScore,
      mul_sub, mul_one, Finset.sum_sub_distrib, hp.2, expectedScore]
  rw [he, expectedScore_brier hp]
  ring

/-- The minimum is attained by the true predictive law. -/
theorem expectedOneHotSquaredError_self
    {O : Type*} [Fintype O] [DecidableEq O] (p : O → ℝ) (hp : IsDist p) :
    expectedOneHotSquaredError p p = 1 - ∑ o, p o ^ 2 := by
  rw [expectedOneHotSquaredError_eq p hp]
  simp [posteriorQuadraticPotential]

theorem expectedOneHotSquaredError_minimized
    {O : Type*} [Fintype O] [DecidableEq O]
    (p : O → ℝ) (hp : IsDist p) (q : O → ℝ) :
    expectedOneHotSquaredError p p ≤ expectedOneHotSquaredError p q := by
  rw [expectedOneHotSquaredError_eq p hp, expectedOneHotSquaredError_eq p hp]
  have hn : 0 ≤ posteriorQuadraticPotential (p - q) :=
    Finset.sum_nonneg fun o _ => sq_nonneg _
  simpa [posteriorQuadraticPotential] using hn

namespace KnownNoise

/-- True predictive observation law conditional on the selected root action.
The action choice is independent of the world before the first observation. -/
def rootPredictive (a : Action) : Observation → ℝ :=
  finiteBayesMass prior (fun θ => response θ [] a)

theorem rootPredictive_valid (a : Action) : IsDist (rootPredictive a) :=
  finiteBayesMass_isDist prior prior_valid _ (fun θ => response_valid θ [] a)

/-- Expected squared error, integrated against the literal full causal record,
for an arbitrary action-indexed predictor. -/
def predictionErrorUsing (π : ValidCausalPolicy Action Observation)
    (q : Action → Observation → ℝ) : ℝ :=
  ∑ w : CausalFiniteTrace Action Observation 1,
    finiteBayesMass prior (causalFiniteExperiment π.1 response 1) w *
      oneHotSquaredError (q (w 0).1) (w 0).2

/-- Summing full retained records gives the action-conditioned prediction risks. -/
theorem predictionErrorUsing_eq (π : ValidCausalPolicy Action Observation)
    (q : Action → Observation → ℝ) :
    predictionErrorUsing π q =
      ∑ a, π.1 [] a * expectedOneHotSquaredError (rootPredictive a) (q a) := by
  unfold predictionErrorUsing
  rw [sum_trace_succ]
  simp_rw [finiteBayesMass, record_one π]
  norm_num [rootPredictive, finiteBayesMass, expectedOneHotSquaredError, prior,
    response, Fin.sum_univ_succ, Fintype.sum_prod_type, Fin.snoc_zero]
  ring

/-- Reward under the optimal observation predictor, including null actions. -/
def expectedPredictionError (π : ValidCausalPolicy Action Observation) : ℝ :=
  predictionErrorUsing π rootPredictive

/-- The chosen ideal predictor really minimizes error for every policy, even
against arbitrary real action-indexed prediction vectors. -/
theorem rootPredictive_minimizes_error (π : ValidCausalPolicy Action Observation)
    (q : Action → Observation → ℝ) :
    expectedPredictionError π ≤ predictionErrorUsing π q := by
  unfold expectedPredictionError
  rw [predictionErrorUsing_eq, predictionErrorUsing_eq]
  apply Finset.sum_le_sum
  intro a _
  exact mul_le_mul_of_nonneg_left
    (expectedOneHotSquaredError_minimized _ (rootPredictive_valid a) (q a)) ((π.2 []).1 a)

/-- The exact ideal prediction-error reward for every randomized policy. -/
theorem expectedPredictionError_eq (π : ValidCausalPolicy Action Observation) :
    expectedPredictionError π = 3 / 4 - π.1 [] 0 / 4 := by
  unfold expectedPredictionError
  rw [predictionErrorUsing_eq]
  simp_rw [expectedOneHotSquaredError_self _ (rootPredictive_valid _)]
  have hr : π.1 [] 0 + π.1 [] 1 = 1 := by
    simpa [Fin.sum_univ_succ] using (π.2 []).2
  norm_num [rootPredictive, finiteBayesMass, prior, response, Fin.sum_univ_succ]
  linear_combination 3 / 4 * hr

/-- The informative bit scores one half; four-symbol known noise scores three quarters. -/
theorem pure_predictionError_scores :
    expectedPredictionError (purePolicy 0) = 1 / 2 ∧
    expectedPredictionError (purePolicy 1) = 3 / 4 := by
  norm_num [expectedPredictionError_eq, purePolicy, detPolicy]

/-- Rewarding irreducible prediction error makes every optimum choose NOISE. -/
theorem predictionError_maximizers (π : ValidCausalPolicy Action Observation) :
    (∀ ρ : ValidCausalPolicy Action Observation,
      expectedPredictionError ρ ≤ expectedPredictionError π) ↔ π.1 [] 0 = 0 := by
  constructor
  · intro h
    have hh := h (purePolicy 1)
    rw [expectedPredictionError_eq, expectedPredictionError_eq] at hh
    norm_num [purePolicy, detPolicy] at hh
    linarith [(π.2 []).1 0]
  · intro hπ ρ
    rw [expectedPredictionError_eq, expectedPredictionError_eq, hπ]
    linarith [(ρ.2 []).1 0]

/-- Every prediction-error optimum is strictly less informative on the full
retained action-observation record than the available revealing policy. -/
theorem every_predictionError_optimum_strictly_misranks
    (π : ValidCausalPolicy Action Observation)
    (hopt : ∀ ρ : ValidCausalPolicy Action Observation,
      expectedPredictionError ρ ≤ expectedPredictionError π) :
    π.1 [] 0 = 0 ∧
    finiteDeficiency (pureRecord 0) (causalFiniteExperiment π.1 response 1) = 0 ∧
    finiteDeficiency (causalFiniteExperiment π.1 response 1) (pureRecord 0) = 1 / 2 :=
  every_surprisal_optimum_strictly_misranks π
    ((surprisal_maximizers π).mpr ((predictionError_maximizers π).mp hopt))

end KnownNoise
end
end IdExp
