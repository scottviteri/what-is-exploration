import Formal.PairedAlarmMovementOptima
import Formal.PairedAlarmPredictiveCore

/-! The sequential Bayes bridge for the literal successive-full-record
Hellinger and Absolute rewards. The recorded next action has the same
conditional probability in every world and cancels from Bayes' rule. -/

noncomputable section
namespace IdExp.PairedAlarm.Movement
open MeasureTheory Finset
open Predictive (mass joint predictive)

/-- A supported next full record has a supported prefix and proposed action. -/
theorem prefix_mass_ne_zero (π : ValidCausalPolicy Action Observation) (t : ℕ)
    (h : CausalFiniteTrace Action Observation t) (a : Action) (o : Observation)
    (hn : mass π (t+1) (Fin.snoc h (a,o)) ≠ 0) : mass π t h ≠ 0 := by
  have hj : joint π t h a o ≠ 0 :=
    right_ne_zero_of_mul (by simpa only [Predictive.mass_snoc] using hn)
  intro hm
  have hle := single_le_sum (fun x _ => Predictive.joint_nonneg π t h a x) (mem_univ o)
  rw [Predictive.joint_sum, hm] at hle
  exact hj (le_antisymm hle (Predictive.joint_nonneg π t h a o))

/-- At every positive-probability new record, updating the current full-record
posterior by the raw observation gives the next full-record posterior. -/
theorem sequential_posterior_atom (π : ValidCausalPolicy Action Observation) (t : ℕ)
    (h : CausalFiniteTrace Action Observation t) (a : Action) (o : Observation)
    (hn : mass π (t+1) (Fin.snoc h (a,o)) ≠ 0) (θ : World) :
    CountableBrier.posterior (posteriorMeasure π t h)
      (fun η => response η (List.ofFn h) a) (fun η => response_valid η (List.ofFn h) a) o θ =
      (posteriorMeasure π (t+1) (Fin.snoc h (a,o))).real {θ} := by
  have hm := prefix_mass_ne_zero π t h a o hn
  have ha : π.1 (List.ofFn h) a ≠ 0 :=
    left_ne_zero_of_mul (by simpa only [Predictive.mass_snoc] using hn)
  have hj : joint π t h a o ≠ 0 :=
    right_ne_zero_of_mul (by simpa only [Predictive.mass_snoc] using hn)
  have hq : priorSignalMass (posteriorMeasure π t h)
      (fun η => response η (List.ofFn h) a) o = joint π t h a o / mass π t h := by
    exact (Predictive.predictive_eq_posterior_average π t h hm a o).symm.trans
      (by simp [predictive, hm])
  have hq0 : priorSignalMass (posteriorMeasure π t h)
      (fun η => response η (List.ofFn h) a) o ≠ 0 := by rw [hq]; exact div_ne_zero hj hm
  have hp := CountableBrier.posterior_apply AlarmPanelPrior.prior (experiment π.1 t)
    (experiment_valid π.1 π.2 t) h θ
  change (posteriorMeasure π t h).real {θ} = _ at hp
  have hp' := CountableBrier.posterior_apply AlarmPanelPrior.prior (experiment π.1 (t+1))
    (experiment_valid π.1 π.2 (t+1)) (Fin.snoc h (a,o)) θ
  change (posteriorMeasure π (t+1) (Fin.snoc h (a,o))).real {θ} = _ at hp'
  rw [CountableBrier.posterior_apply (posteriorMeasure π t h)
    (fun η => response η (List.ofFn h) a)
    (fun η => response_valid η (List.ofFn h) a) o θ, hp, hp']
  simp only [priorSignalDensity, if_neg hq0]
  change _ = (if mass π (t+1) (Fin.snoc h (a,o)) = 0 then 1 else
      experiment π.1 (t+1) θ (Fin.snoc h (a,o)) / mass π (t+1) (Fin.snoc h (a,o))) * _
  simp only [if_neg hn]
  change response θ (List.ofFn h) a o / _ *
      ((if mass π t h = 0 then 1 else experiment π.1 t θ h / mass π t h) * _) = _
  rw [if_neg hm, hq, Predictive.mass_snoc]
  simp only [experiment, causalFiniteExperiment_snoc]
  field_simp


/-- The next retained action contributes its policy probability, which is
world-independent conditional on the recorded prefix. This includes null prefixes. -/
theorem mass_snoc_eq_posterior_predictive (π : ValidCausalPolicy Action Observation) (t : ℕ)
    (h : CausalFiniteTrace Action Observation t) (a : Action) (o : Observation) :
    mass π (t+1) (Fin.snoc h (a,o)) = mass π t h * π.1 (List.ofFn h) a *
      priorSignalMass (posteriorMeasure π t h) (fun η => response η (List.ofFn h) a) o := by
  by_cases hm : mass π t h = 0
  · have hn : mass π (t+1) (Fin.snoc h (a,o)) = 0 := by
      by_contra hn
      exact prefix_mass_ne_zero π t h a o hn hm
    simp [hm, hn]
  · have hp := Predictive.predictive_eq_posterior_average π t h hm a o
    change predictive π t h a o = priorSignalMass (posteriorMeasure π t h)
      (fun η => response η (List.ofFn h) a) o at hp
    rw [← hp, Predictive.mass_snoc]
    rw [show mass π t h * π.1 (List.ofFn h) a * predictive π t h a o =
      π.1 (List.ofFn h) a * (mass π t h * predictive π t h a o) by ring]
    rw [Predictive.mass_mul_predictive]

/-- Literal movement between the two successive complete-record posteriors,
weighted by the actual prior-predictive law of the next action-observation record. -/
def expectedFullRecordMovement (kind : PosteriorMovement.Kind)
    (π : ValidCausalPolicy Action Observation) (t : ℕ) : ℝ :=
  ∑ h : CausalFiniteTrace Action Observation t, ∑ a : Action, ∑ o : Observation,
    mass π (t+1) (Fin.snoc h (a,o)) *
      ∑' θ : World, PosteriorMovement.loss kind
        ((posteriorMeasure π (t+1) (Fin.snoc h (a,o))).real {θ})
        ((posteriorMeasure π t h).real {θ})

theorem fullRecordMovement_summable (kind : PosteriorMovement.Kind)
    (π : ValidCausalPolicy Action Observation) (t : ℕ)
    (h : CausalFiniteTrace Action Observation t) (a : Action) (o : Observation) :
    Summable (fun θ : World => PosteriorMovement.loss kind
      ((posteriorMeasure π (t+1) (Fin.snoc h (a,o))).real {θ})
      ((posteriorMeasure π t h).real {θ})) :=
  PosteriorMovement.posterior_distance_summable kind
    (FullLabelBrierReport.ofMeasure (posteriorMeasure π (t+1) (Fin.snoc h (a,o))))
    (FullLabelBrierReport.ofMeasure (posteriorMeasure π t h))

/-- Exact all-policy bridge from literal successive-full-record movement to
the conditional expected reward whose returns and optimizers were computed. -/
theorem expectedFullRecordMovement_eq (kind : PosteriorMovement.Kind)
    (π : ValidCausalPolicy Action Observation) (t : ℕ) :
    expectedFullRecordMovement kind π t = stage kind π t := by
  unfold expectedFullRecordMovement stage
  apply sum_congr rfl
  intro h _
  rw [mul_sum]
  apply sum_congr rfl
  intro a _
  rw [← localReward_eq_expected_movement kind π t h a, mul_sum, mul_sum]
  apply sum_congr rfl
  intro o _
  by_cases hn : mass π (t+1) (Fin.snoc h (a,o)) = 0
  · have hz := mass_snoc_eq_posterior_predictive π t h a o
    rw [hn] at hz
    change _ = mass π t h * (π.1 (List.ofFn h) a * (_ * _))
    rw [hn, zero_mul]
    simp only [← mul_assoc, ← hz, zero_mul]
  · have he : (fun θ : World => PosteriorMovement.loss kind
        ((posteriorMeasure π (t+1) (Fin.snoc h (a,o))).real {θ})
        ((posteriorMeasure π t h).real {θ})) =
      (fun θ : World => PosteriorMovement.loss kind
        (CountableBrier.posterior (posteriorMeasure π t h)
          (fun η => response η (List.ofFn h) a)
          (fun η => response_valid η (List.ofFn h) a) o θ)
        ((posteriorMeasure π t h).real {θ})) := by
      funext θ
      rw [sequential_posterior_atom π t h a o hn θ]
    rw [he, mass_snoc_eq_posterior_predictive]
    change _ = mass π t h * (π.1 (List.ofFn h) a * (_ * _))
    ring

/-- Every weighted return is unchanged when written using the literal
successive-full-record posterior distances. -/
theorem fullRecord_discounted_eq (kind : PosteriorMovement.Kind) (γ : ℝ)
    (π : ValidCausalPolicy Action Observation) :
    (∑' t, γ^t * expectedFullRecordMovement kind π t) = discounted kind γ π := by
  simp only [expectedFullRecordMovement_eq, discounted]


/-- Summability of the literal discounted movement, including the complete
undiscounted case gamma=1. -/
theorem fullRecord_discounted_summable (kind : PosteriorMovement.Kind) (γ : ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (π : ValidCausalPolicy Action Observation) :
    Summable (fun t => γ^t * expectedFullRecordMovement kind π t) := by
  simp only [expectedFullRecordMovement_eq]
  exact discounted_summable kind π γ hγ hγ1

/-- Exact global optimizer set of the literal successive-full-record
Hellinger or Absolute return; gamma=1 is the complete return. -/
theorem fullRecord_isMaximizer_iff (kind : PosteriorMovement.Kind) (γ : ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (π : ValidCausalPolicy Action Observation) :
    (∀ ρ : ValidCausalPolicy Action Observation,
      (∑' t, γ^t * expectedFullRecordMovement kind ρ t) ≤
        ∑' t, γ^t * expectedFullRecordMovement kind π t) ↔
      inspectionProbability π.1 = 1 := by
  simp only [fullRecord_discounted_eq]
  exact isMaximizer_iff kind γ hγ hγ1 π

end IdExp.PairedAlarm.Movement
