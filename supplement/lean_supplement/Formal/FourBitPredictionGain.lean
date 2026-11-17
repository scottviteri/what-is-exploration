import Formal.CausalBayesianPredictionGain
import Formal.FourBitInformationMovement

/-! # Bayesian prediction gain on the actual four-bit response
FULL and PARTIAL both have deterministic response likelihoods. Rescoring the
same response with the updated exact posterior therefore agrees pointwise with
posterior KL; the response variable and full retained histories are unchanged.
-/
namespace IdExp.FourBitPosterior
noncomputable section
open BayesianPredictionGain

theorem response_likelihood_cell (h : CausalHistory Action Observation)
    (a : Action) (o : Observation) :
    (fun θ => response θ h a o) =
      cellLikelihood {θ | o = signal θ (ScheduledReveal.mode h a) h.length} 1 := by
  classical
  funext θ
  simp [response, ScheduledReveal.response, cellLikelihood]

theorem replayGain_eq_informationGain (h : CausalHistory Action Observation)
    (a : Action) (o : Observation)
    (hz : predictive (historyPosterior prior response h) (fun θ => response θ h a o) ≠ 0) :
    historyReplayGain prior response h a o =
      ∑ θ, historyPosterior prior response (h ++ [(a,o)]) θ *
        Real.logb 2 (historyPosterior prior response (h ++ [(a,o)]) θ /
          historyPosterior prior response h θ) := by
  simpa only [tsum_fintype] using
    historyReplayGain_eq_informationGain_of_cell prior response h a o _ 1
      (response_likelihood_cell h a o) hz

theorem oneStepGain_eq_informationGain (q : World → ℝ)
    (h : CausalHistory Action Observation) (a : Action) (o : Observation) :
    gain q (fun θ => response θ h a o) = informationGain q (fun θ => response θ h a o) := by
  rw [response_likelihood_cell]
  exact gain_eq_informationGain_cell_total q _ 1


/-- The probability of an actual full record factors at its last interaction. -/
theorem record_append (π : Policy) (n : ℕ)
    (h : CausalFiniteTrace Action Observation (n+1)) (θ : World) :
    record π (n+1) θ h = record π n θ (Fin.init h) *
      π.1 (List.ofFn (Fin.init h)) (h (Fin.last n)).1 *
      response θ (List.ofFn (Fin.init h)) (h (Fin.last n)).1 (h (Fin.last n)).2 := by
  simp only [record, ScheduledReveal.record, causalFiniteExperiment,
    List.ofFn_succ_last, causalTraceProb_append_singleton]
  rfl

/-- Bayes' update using the literal successive retained-record posteriors. -/
theorem record_posterior_update (π : Policy) (n : ℕ)
    (h : CausalFiniteTrace Action Observation (n+1))
    (hh : 0 < finiteBayesMass prior (record π (n+1)) h) :
    posterior π (n+1) h = BayesianPredictionGain.posterior (posterior π n (Fin.init h))
      (fun θ => response θ (List.ofFn (Fin.init h)) (h (Fin.last n)).1 (h (Fin.last n)).2) := by
  classical
  obtain ⟨θ,hθ⟩ : ∃ θ, record π (n+1) θ h ≠ 0 := by
    by_contra! hz
    simp [finiteBayesMass, hz] at hh
  have hf := record_append π n h θ
  rw [hf] at hθ
  have hc : π.1 (List.ofFn (Fin.init h)) (h (Fin.last n)).1 ≠ 0 :=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hθ).1).2
  have hE : record π n θ (Fin.init h) ≠ 0 :=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hθ).1).1
  have hEpos : 0 < record π n θ (Fin.init h) :=
    lt_of_le_of_ne ((record_valid π n θ).1 _) (Ne.symm hE)
  have hNpos : 0 < finiteBayesMass prior (record π n) (Fin.init h) := by
    apply lt_of_lt_of_le (mul_pos (prior_pos θ) hEpos)
    unfold finiteBayesMass
    exact Finset.single_le_sum
      (fun η _ => mul_nonneg (prior_valid.1 η) ((record_valid π n η).1 _))
      (Finset.mem_univ θ)
  have hN : predictive prior (fun θ => record π n θ (Fin.init h)) ≠ 0 := by
    simpa only [predictive, tsum_fintype, finiteBayesMass] using ne_of_gt hNpos
  have hold : posterior π n (Fin.init h) =
      BayesianPredictionGain.posterior prior (fun θ => record π n θ (Fin.init h)) := by
    funext θ
    simp only [posterior, finiteBayesPosterior, BayesianPredictionGain.posterior,
      predictive, tsum_fintype]
  rw [hold, posterior_update _ _ _ hN]
  have hnew : posterior π (n+1) h = BayesianPredictionGain.posterior prior
      (fun θ => (record π n θ (Fin.init h) *
        response θ (List.ofFn (Fin.init h)) (h (Fin.last n)).1 (h (Fin.last n)).2) *
        π.1 (List.ofFn (Fin.init h)) (h (Fin.last n)).1) := by
    funext η
    simp only [posterior, finiteBayesPosterior, BayesianPredictionGain.posterior,
      predictive, tsum_fintype, record_append]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro θ _
      ring
  rw [hnew, posterior_scale _ _ _ hc]

/-- Actual expected one-step Bayesian replay PG in bits. -/
def expectedPredictionGain (π : Policy) (n : ℕ) : ℝ :=
  ∑ h : CausalFiniteTrace Action Observation (n+1),
    finiteBayesMass prior (record π (n+1)) h *
      gain (posterior π n (Fin.init h))
        (fun θ => response θ (List.ofFn (Fin.init h)) (h (Fin.last n)).1 (h (Fin.last n)).2)

theorem expectedPredictionGain_eq (π : Policy) (n : ℕ) :
    expectedPredictionGain π n = expectedInformationMovementBits π n := by
  unfold expectedPredictionGain expectedInformationMovementBits
  apply Finset.sum_congr rfl
  intro h _
  rcases (finiteBayesMass_nonneg prior (record π (n+1)) prior_valid.1
    (fun θ h => (record_valid π (n+1) θ).1 h) h).lt_or_eq with hp | hz
  · rw [oneStepGain_eq_informationGain, record_posterior_update π n h hp]
    simp only [informationGain, informationRewardBits, tsum_fintype]
  · rw [← hz]
    simp

/-- Complete return. All rewards after the third interaction vanish. -/
def completePredictionGain (π : Policy) : ℝ := ∑' n, expectedPredictionGain π n

theorem completePredictionGain_eq (π : Policy) :
    completePredictionGain π = fullProbability π * 4 + (1-fullProbability π)*3 := by
  have he : completePredictionGain π = informationKLObjectiveBits 1 π := by
    simp only [completePredictionGain, expectedPredictionGain_eq, informationKLObjectiveBits,
      one_pow, one_mul]
  rw [he, informationKLObjectiveBits_eq]
  ring

theorem completePredictionGain_maximizer_iff (π : Policy) :
    (∀ ρ : Policy, completePredictionGain ρ ≤ completePredictionGain π) ↔
      fullProbability π = 1 := by
  have he (ρ : Policy) : completePredictionGain ρ = informationKLObjectiveBits 1 ρ := by
    simp only [completePredictionGain, expectedPredictionGain_eq, informationKLObjectiveBits,
      one_pow, one_mul]
  simp only [he]
  exact informationKLBits_maximizer_iff 1 (by norm_num) (by norm_num) π


/-- The series defining the complete PG return is a finite, convergent sum. -/
theorem predictionGain_hasSum (π : Policy) :
    HasSum (expectedPredictionGain π) (∑ n ∈ Finset.range 3, expectedPredictionGain π n) := by
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  rw [expectedPredictionGain_eq, expectedInformationMovementBits_eq,
    expectedInformationMovement_after_three π n (by simpa only [Finset.mem_range, not_lt] using hn),
    zero_div]

/-- Any discounted aggregation has exactly the existing bit-valued information return. -/
theorem discountedPredictionGain_eq (γ : ℝ) (π : Policy) :
    (∑' n, γ^n * expectedPredictionGain π n) = informationKLObjectiveBits γ π := by
  simp only [expectedPredictionGain_eq, informationKLObjectiveBits]

theorem discountedPredictionGain_maximizer_iff (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (π : Policy) :
    (∀ ρ : Policy, (∑' n, γ^n * expectedPredictionGain ρ n) ≤
      ∑' n, γ^n * expectedPredictionGain π n) ↔ fullProbability π = 1 := by
  simp only [discountedPredictionGain_eq]
  exact informationKLBits_maximizer_iff γ hγ hγ1 π

theorem completePredictionGain_optimum_eventual_loss_zero (π : Policy)
    (hopt : ∀ ρ : Policy, completePredictionGain ρ ≤ completePredictionGain π) :
    sInf (Set.range (fun t => finiteDeficiency (record π t) fullTarget)) = 0 := by
  rw [eventual_native_deficiency, (completePredictionGain_maximizer_iff π).mp hopt]
  norm_num


/-- Each deterministic-cell replay reward is nonnegative, including null responses. -/
theorem oneStepGain_nonneg (q : World → ℝ) (hq : IsDist q)
    (h : CausalHistory Action Observation) (a : Action) (o : Observation) :
    0 ≤ gain q (fun θ => response θ h a o) := by
  classical
  rw [response_likelihood_cell]
  let S : Set World := {θ | o = signal θ (ScheduledReveal.mode h a) h.length}
  change 0 ≤ gain q (cellLikelihood S 1)
  have hm0 : 0 ≤ BayesianPredictionGain.cellMass q S := by
    exact tsum_nonneg fun θ => by split_ifs; exact hq.1 θ; exact le_rfl
  have hm1 : BayesianPredictionGain.cellMass q S ≤ 1 := by
    unfold BayesianPredictionGain.cellMass
    rw [tsum_fintype, ← hq.2]
    apply Finset.sum_le_sum
    intro θ _
    split_ifs
    · exact le_rfl
    · exact hq.1 θ
  by_cases hm : BayesianPredictionGain.cellMass q S = 0
  · have hz : predictive q (cellLikelihood S 1) = 0 := by rw [predictive_cell, hm, mul_zero]
    simp [gain, hz]
  · rw [gain_cell q S 1 (by norm_num) hm]
    exact neg_nonneg.mpr (Real.logb_nonpos (by norm_num) hm0 hm1)

/-- Literal reward nonnegativity for the preceding full-record posterior,
including unreachable prefixes under the zero-vector convention. -/
theorem recordGain_nonneg (π : Policy) (n : ℕ)
    (h : CausalFiniteTrace Action Observation n) (a : Action) (o : Observation) :
    0 ≤ gain (posterior π n h) (fun θ => response θ (List.ofFn h) a o) := by
  by_cases hm : finiteBayesMass prior (record π n) h = 0
  · have hq : posterior π n h = fun _ => 0 := by
      funext θ
      simpa only [posterior, finiteBayesPosterior, finiteBayesMass] using
        (show prior θ * record π n θ h / finiteBayesMass prior (record π n) h = 0 by rw [hm, div_zero])
    simp [hq, gain, predictive]
  · apply oneStepGain_nonneg
    exact finiteBayesPosterior_mem_simplex prior (record π n) prior_valid.1
      (fun θ h => (record_valid π n θ).1 h) h hm

theorem expectedPredictionGain_nonneg (π : Policy) (n : ℕ) : 0 ≤ expectedPredictionGain π n := by
  apply Finset.sum_nonneg
  intro h _
  exact mul_nonneg
    (finiteBayesMass_nonneg prior (record π (n+1)) prior_valid.1
      (fun θ h => (record_valid π (n+1) θ).1 h) h)
    (recordGain_nonneg π n (Fin.init h) (h (Fin.last n)).1 (h (Fin.last n)).2)

end
end IdExp.FourBitPosterior
