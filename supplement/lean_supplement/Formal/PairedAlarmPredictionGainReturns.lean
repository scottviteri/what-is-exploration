import Formal.PairedAlarmPredictionGain
import Formal.PairedAlarmMovementSequential
import Formal.PairedAlarmInformationDiscount

/-! # Literal Bayesian prediction-gain returns on retained alarm records
This module transfers the actual observation-level PG reward to the already
checked successive-posterior information reward, including record probabilities,
null-record conventions, finite sums and the convergent complete series.
-/
namespace IdExp.BayesianPredictionGain
noncomputable section
open MeasureTheory
variable {Θ S : Type*} [Countable Θ] [MeasurableSpace Θ]
  [MeasurableSingletonClass Θ] [Fintype S] [Nonempty S]

theorem predictive_atoms (μ : Measure Θ) [IsProbabilityMeasure μ]
    (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E) (s : S) :
    predictive (fun θ => μ.real {θ}) (fun θ => E θ s) = priorSignalMass μ E s := by
  rw [priorSignalMass, integral_countable (CountableBrier.likelihood_integrable μ E hE s)]
  simp only [predictive, smul_eq_mul]

theorem posterior_atoms (μ : Measure Θ) [IsProbabilityMeasure μ]
    (E : FiniteExperiment Θ S) (hE : IsFiniteExperiment E) (s : S)
    (hm : priorSignalMass μ E s ≠ 0) :
    posterior (fun θ => μ.real {θ}) (fun θ => E θ s) = CountableBrier.posterior μ E hE s := by
  funext θ
  rw [posterior, predictive_atoms μ E hE s, CountableBrier.posterior_apply]
  simp only [priorSignalDensity, if_neg hm]
  ring
end
end IdExp.BayesianPredictionGain

namespace IdExp.PairedAlarm.PredictionGain
noncomputable section
open MeasureTheory Finset BayesianPredictionGain
open Movement (posteriorMeasure)

abbrev Policy := ValidCausalPolicy Action Observation

/-- Exact current posterior atoms, retaining every action and observation. -/
def posteriorAtoms (π : Policy) (t : ℕ) (h : CausalFiniteTrace Action Observation t) : World → ℝ :=
  fun θ => (posteriorMeasure π t h).real {θ}

theorem record_posterior_update (π : Policy) (t : ℕ)
    (h : CausalFiniteTrace Action Observation t) (a : Action) (o : Observation)
    (hn : Predictive.mass π (t+1) (Fin.snoc h (a,o)) ≠ 0) :
    BayesianPredictionGain.posterior (posteriorAtoms π t h)
      (fun θ => response θ (List.ofFn h) a o) = posteriorAtoms π (t+1) (Fin.snoc h (a,o)) := by
  have hm : priorSignalMass (posteriorMeasure π t h)
      (fun θ => response θ (List.ofFn h) a) o ≠ 0 := by
    intro hz
    apply hn
    rw [Movement.mass_snoc_eq_posterior_predictive, hz, mul_zero]
  change BayesianPredictionGain.posterior (fun θ => (posteriorMeasure π t h).real {θ})
    (fun θ => response θ (List.ofFn h) a o) = _
  rw [posterior_atoms (posteriorMeasure π t h)
    (fun θ => response θ (List.ofFn h) a) (fun θ => response_valid θ (List.ofFn h) a) o hm]
  funext θ
  exact Movement.sequential_posterior_atom π t h a o hn θ

/-- The expected actual replay reward, in bits, at interaction `t+1`. -/
def expected (π : Policy) (t : ℕ) : ℝ :=
  ∑ h : CausalFiniteTrace Action Observation (t+1),
    Predictive.mass π (t+1) h * gain (posteriorAtoms π t (Fin.init h))
      (fun θ => response θ (List.ofFn (Fin.init h)) (h (Fin.last t)).1 (h (Fin.last t)).2)

theorem expected_eq_information (π : Policy) (t : ℕ) :
    expected π t = Information.expectedInformationMovement π t / Real.log 2 := by
  unfold expected Information.expectedInformationMovement
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro h _
  change Predictive.mass π (t+1) h * _ = Predictive.mass π (t+1) h * _ / _
  by_cases hz : Predictive.mass π (t+1) h = 0
  · simp [hz]
  · have hn : Predictive.mass π (t+1) (Fin.snoc (Fin.init h) (h (Fin.last t))) ≠ 0 := by
      simpa only [Fin.snoc_init_self] using hz
    have hup := record_posterior_update π t (Fin.init h) (h (Fin.last t)).1
      (h (Fin.last t)).2 hn
    simp only [Prod.mk.eta, Fin.snoc_init_self] at hup
    rw [oneStepGain_eq_informationGain]
    unfold informationGain
    rw [hup]
    simp only [posteriorAtoms, CountableBrier.posterior, FullLabelBrierReport.ofMeasure,
      Movement.posteriorMeasure, Real.logb, ← mul_div_assoc, tsum_div_const,
      Information.record, PulseBrierScore.prior]



/-- The actual expected replay rewards are nonnegative. -/
theorem expected_nonneg (π : Policy) (t : ℕ) : 0 ≤ expected π t := by
  rw [expected_eq_information]
  exact div_nonneg (Information.expectedInformationMovement_nonneg π t)
    (le_of_lt (Real.log_pos (by norm_num)))


/-- The finite PG sum is exactly finite information in bits. -/
theorem finite_sum (π : Policy) (H : ℕ) :
    (∑ t ∈ range H, expected π t) = Information.prefixInformation π H / Real.log 2 := by
  simp only [expected_eq_information, ← Finset.sum_div]
  rw [Information.finite_information_movement_telescope]

/-- Actual PG rewards form a convergent nonnegative complete series of two bits. -/
theorem hasSum_two (π : Policy) : HasSum (expected π) 2 := by
  have h := (Information.informationMovement_hasSum π).div_const (Real.log 2)
  have hl : Real.log (2:ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have he : expected π = fun t => Information.expectedInformationMovement π t / Real.log 2 :=
    funext (expected_eq_information π)
  rw [he]
  simpa only [mul_div_cancel_right₀ _ hl] using h

theorem complete_eq_two (π : Policy) : (∑' t, expected π t) = 2 := (hasSum_two π).tsum_eq

theorem finite_maximizer_iff (H : ℕ) (π : Policy) :
    (∀ ρ : Policy, (∑ t ∈ range (H+1), expected ρ t) ≤
      ∑ t ∈ range (H+1), expected π t) ↔ inspectionProbability π.1 = 1 := by
  have hl : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  simp only [finite_sum, div_le_div_iff_of_pos_right hl]
  exact Information.finiteInformation_maximizer_iff H π

theorem discounted_maximizer_iff (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1) (π : Policy) :
    (∀ ρ : Policy, (∑' t, γ^t * expected ρ t) ≤ ∑' t, γ^t * expected π t) ↔
      inspectionProbability π.1 = 1 := by
  simp only [expected_eq_information]
  exact Information.discountedInformationMovementBits_maximizer_iff γ hγ hγ1 π

end
end IdExp.PairedAlarm.PredictionGain
