import Formal.AlarmPanelBayesPredictive
import Formal.AlarmPanelControlMOP

/-! The countable-prior predictive entropy identity on actual causal records.
The policy's action entropy cancels; only observation prediction is rewarded. -/
namespace IdExp.AlarmPanelBayes
open MeasureTheory Finset
open AlarmPanel
noncomputable section

/-- Entropy of an unnormalized probability row. -/
theorem sum_negMulLog_scale {X : Type*} [Fintype X] (c : ℝ) (q : X → ℝ)
    (hq : IsDist q) :
    (∑ x, Real.negMulLog (c * q x)) = Real.negMulLog c + c * ent q := by
  simp_rw [Real.negMulLog_mul]
  rw [sum_add_distrib, ← sum_mul, hq.2, one_mul, ← mul_sum]
  rfl

theorem sum_next_entropy (m : ℝ) (p : Action → ℝ) (hp : IsDist p)
    (q : Action → Observation → ℝ) (hq : ∀ a, IsDist (q a)) :
    (∑ a, ∑ o, Real.negMulLog (m * p a * q a o)) =
      Real.negMulLog m + m * ent p + m * ∑ a, p a * ent (q a) := by
  simp_rw [sum_negMulLog_scale _ _ (hq _)]
  rw [sum_add_distrib, sum_negMulLog_scale m p hp]
  simp only [mul_assoc, ← mul_sum]

def actionStage (π : ValidCausalPolicy Action Observation) (n : ℕ) : ℝ :=
  ∑ u : Trace n, mass π n u * ent (π.1 (List.ofFn u))

theorem mass_entropy_succ (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    ent (mass π (n+1)) = ent (mass π n) + actionStage π n + logStage π n := by
  rw [logStage_eq]
  unfold ent
  rw [sum_trace_succ]
  simp_rw [Fintype.sum_prod_type]
  have hf (u : Trace n) (a : Action) (o : Observation) :
      mass π (n+1) (Fin.snoc u (a,o)) =
        mass π n u * π.1 (List.ofFn u) a * predictive π n u a o := by
    rw [mass_snoc, ← mass_mul_predictive π n u a o]
    ring
  simp_rw [hf, sum_next_entropy _ _ (π.2 _) _ (predictive_valid π n _)]
  simp only [sum_add_distrib, actionStage, ent]

def worldAction (π : ValidCausalPolicy Action Observation) (n : ℕ) (θ : World) : ℝ :=
  ∑ u : Trace n, record π n θ u * ent (π.1 (List.ofFn u))

def worldNoise (π : ValidCausalPolicy Action Observation) (n : ℕ) (θ : World) : ℝ :=
  ∑ u : Trace n, record π n θ u * ∑ a, π.1 (List.ofFn u) a *
    ent (response θ (List.ofFn u) a)

theorem world_entropy_succ (π : ValidCausalPolicy Action Observation) (n : ℕ) (θ : World) :
    ent (record π (n+1) θ) = ent (record π n θ) + worldAction π n θ + worldNoise π n θ := by
  unfold ent
  rw [sum_trace_succ]
  simp_rw [Fintype.sum_prod_type, record, experiment, causalFiniteExperiment_snoc,
    sum_next_entropy _ _ (π.2 _) _ (response_valid θ _)]
  simp only [worldAction, worldNoise, record, experiment, ent, sum_add_distrib]

theorem worldAction_integrable (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    Integrable (worldAction π n) prior :=
  integrable_finsetSum _ fun u _ => (record_integrable π n u).mul_const _

theorem integral_worldAction (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    (∫ θ, worldAction π n θ ∂prior) = actionStage π n := by
  unfold worldAction actionStage
  rw [integral_finsetSum _ (fun u _ => (record_integrable π n u).mul_const _)]
  simp only [integral_mul_const, mass, priorSignalMass]

theorem worldNoise_integrable (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    Integrable (worldNoise π n) prior := by
  have he (k : ℕ) := integrable_finiteExperiment_ent prior (record π k)
    (record_valid π k) (fun _ => measurable_of_countable _)
  apply ((he (n+1)).sub ((he n).add (worldAction_integrable π n))).congr
  filter_upwards [] with θ
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [world_entropy_succ]
  ring

def noiseStage (π : ValidCausalPolicy Action Observation) (n : ℕ) : ℝ :=
  ∫ θ, worldNoise π n θ ∂prior

theorem information_step (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    logStage π n = AlarmPanelPosterior.prefixInformation π (n+1) -
      AlarmPanelPosterior.prefixInformation π n + noiseStage π n := by
  have he (k : ℕ) := integrable_finiteExperiment_ent prior (record π k)
    (record_valid π k) (fun _ => measurable_of_countable _)
  have hw : (∫ θ, ent (record π (n+1) θ) ∂prior) =
      (∫ θ, ent (record π n θ) ∂prior) + actionStage π n + noiseStage π n := by
    simp_rw [world_entropy_succ]
    have h1 := integral_add ((he n).add (worldAction_integrable π n)) (worldNoise_integrable π n)
    have h2 := integral_add (he n) (worldAction_integrable π n)
    simp only [Pi.add_apply] at h1 h2
    rw [h1, h2, integral_worldAction]
    rfl
  have hi (k : ℕ) : AlarmPanelPosterior.prefixInformation π k =
      ent (mass π k) - ∫ θ, ent (record π k θ) ∂prior :=
    infinitePriorInformation_eq_ent_mass_sub prior (record π k) (record_valid π k)
      (fun _ => measurable_of_countable _)
  rw [hi, hi, mass_entropy_succ]
  linarith

theorem information_zero (π : ValidCausalPolicy Action Observation) :
    AlarmPanelPosterior.prefixInformation π 0 = 0 := by
  rw [AlarmPanelPosterior.prefixInformation, infinitePriorInformation_eq_ent_mass_sub
    prior (record π 0) (record_valid π 0) (fun _ => measurable_of_countable _)]
  have hr (θ : World) (u : Trace 0) : record π 0 θ u = 1 := by
    simp [record, experiment, causalFiniteExperiment, causalTraceProb, causalTraceProbFrom]
  have hm (u : Trace 0) : priorSignalMass prior (record π 0) u = 1 := by
    simp [priorSignalMass, hr]
  simp [ent, hm, hr]

theorem logPrefix_eq (π : ValidCausalPolicy Action Observation) (H : ℕ) :
    (∑ n ∈ range H, logStage π n) = AlarmPanelPosterior.prefixInformation π H +
      ∑ n ∈ range H, noiseStage π n := by
  induction H with
  | zero => simp [information_zero]
  | succ H ih =>
    rw [sum_range_succ, sum_range_succ, ih, information_step]
    ring


theorem worldNoise_zero (π : ValidCausalPolicy Action Observation) (θ : World) :
    worldNoise π 0 θ = (2 - inspectionProbability π.1) * Real.log 2 := by
  have h := MOP.localReward_root π θ
  simp only [MOP.localReward] at h
  have he : worldNoise π 0 θ = ∑ a, π.1 [] a * ent (response θ [] a) := by
    simp [worldNoise, record, experiment, causalFiniteExperiment, causalTraceProb, causalTraceProbFrom]
  rw [he]
  simpa only [inspectionProbability, inspect] using (add_left_cancel h)

theorem worldNoise_succ (π : ValidCausalPolicy Action Observation) (θ : World) (n : ℕ) :
    worldNoise π (n+1) θ =
      if (n+1)%2 = 1 then (1-inspectionProbability π.1) * Real.log 2 else 0 := by
  have he : worldNoise π (n+1) θ = Control.empowermentStage π θ (n+1) := by
    unfold worldNoise Control.empowermentStage
    apply sum_congr rfl; intro u _
    simp only [MOP.transitionEntropy_tail θ (List.ofFn u) (by simp),
      ← sum_mul, (π.2 _).2, one_mul]
  rw [he, Control.empowermentStage_succ]
  rfl

theorem noiseStage_zero (π : ValidCausalPolicy Action Observation) :
    noiseStage π 0 = (2-inspectionProbability π.1) * Real.log 2 := by
  simp [noiseStage, worldNoise_zero]

theorem noiseStage_succ (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    noiseStage π (n+1) =
      if (n+1)%2 = 1 then (1-inspectionProbability π.1) * Real.log 2 else 0 := by
  simp [noiseStage, worldNoise_succ]

theorem noisePrefix_succ (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    (∑ t ∈ range (n+1), noiseStage π t) =
      (2-inspectionProbability π.1 + (((n+1)/2 : ℕ) : ℝ) *
        (1-inspectionProbability π.1)) * Real.log 2 := by
  induction n with
  | zero => simp [noiseStage_zero]
  | succ n ih =>
    rw [sum_range_succ, ih, noiseStage_succ]
    by_cases ho : (n+1)%2 = 1
    · have hd : (n+1+1)/2 = (n+1)/2+1 := by omega
      simp only [ho, if_true, hd, Nat.cast_add, Nat.cast_one]
      ring
    · have hd : (n+1+1)/2 = (n+1)/2 := by omega
      simp only [ho, if_false, hd]
      ring

/-- Every partial surprisal return is bounded after certain startup inspection. -/
theorem logPrefix_inspection_le (π : ValidCausalPolicy Action Observation)
    (hs : inspectionProbability π.1 = 1) (H : ℕ) :
    (∑ n ∈ range H, logStage π n) ≤ 3 * Real.log 2 := by
  cases H with
  | zero => simp; positivity
  | succ n =>
    rw [logPrefix_eq, noisePrefix_succ, hs]
    have h := AlarmPanelPosterior.prefixInformation_le π (n+1)
    norm_num at *
    linarith

/-- The Bayes categorical squared loss is bounded by predictive entropy.
This is a statement about predicting observations, not Brier gain on worlds. -/
theorem squaredRisk_le_entropy (q : Observation → ℝ) (hq : IsDist q) :
    (1 - ∑ o, q o ^ 2) ≤ ent q := by
  have ht (o : Observation) : q o - q o^2 ≤ Real.negMulLog (q o) := by
    by_cases hz : q o = 0
    · simp [hz]
    · have hp : 0 < q o := lt_of_le_of_ne (hq.1 o) (Ne.symm hz)
      have hh := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hp) (hq.1 o)
      simp only [Real.negMulLog]
      nlinarith
  have h := sum_le_sum (s := univ) (fun o _ => ht o)
  simpa only [sum_sub_distrib, hq.2, ent] using h

theorem squaredStage_le_logStage (π : ValidCausalPolicy Action Observation) (n : ℕ) :
    squaredStage π n ≤ logStage π n := by
  rw [squaredStage_eq, logStage_eq]
  apply sum_le_sum; intro u _
  apply mul_le_mul_of_nonneg_left _ ((mass_valid π n).1 u)
  apply sum_le_sum; intro a _
  exact mul_le_mul_of_nonneg_left (squaredRisk_le_entropy _ (predictive_valid π n u a))
    ((π.2 _).1 a)

/-- In particular the complete squared-loss return of inspection is finite. -/
theorem squaredPrefix_inspection_le (π : ValidCausalPolicy Action Observation)
    (hs : inspectionProbability π.1 = 1) (H : ℕ) :
    (∑ n ∈ range H, squaredStage π n) ≤ 3 * Real.log 2 :=
  (sum_le_sum (fun n _ => squaredStage_le_logStage π n)).trans
    (logPrefix_inspection_le π hs H)

end
end IdExp.AlarmPanelBayes
