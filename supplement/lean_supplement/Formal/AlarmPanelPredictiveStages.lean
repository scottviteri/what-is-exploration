import Formal.AlarmPanelBayesPanel
import Formal.AlarmPanelPosteriorMovement
import Formal.AlarmPanelVariantThreeStep

/-! Literal history-conditioned Shannon and per-step Square source rewards.
All predictions use the existing full-record Bayesian predictive law on the
unchanged alarm/panel, with every adaptive randomized continuation allowed. -/
noncomputable section
namespace IdExp.AlarmPanelPredictive
open AlarmPanel AlarmPanelBayes AlarmPanelVariance MeasureTheory Finset Set
set_option maxRecDepth 10000
set_option maxHeartbeats 600000

/-- Literal per-step Square-KSA utility, not posterior Brier or whole-record Square. -/
def squareUtility (q : Observation → ℝ) (o : Observation) : ℝ := -q o

def squareStage (π : ValidCausalPolicy Action Observation) (t : ℕ) : ℝ :=
  stage squareUtility π t

theorem predictive_root (π : ValidCausalPolicy Action Observation)
    (h : Trace 0) (a : Action) : predictive π 0 h a = uniformDist := by
  have hr (θ : World) : record π 0 θ h = 1 := by
    simp [record, experiment, causalFiniteExperiment, causalTraceProb, causalTraceProbFrom]
  have hm : mass π 0 h = 1 := by simp [mass, priorSignalMass, hr]
  funext o
  simp only [predictive, hm, one_ne_zero, if_false, div_one, joint, hr, one_mul,
    List.ofFn_zero]
  rw [AlarmPanelPrior.integral_none_some _ (by intro k; simp [response_root])]
  fin_cases a <;> fin_cases o <;> norm_num [response_root, inspect, pairDist, uniformDist]

theorem logStage_root (π : ValidCausalPolicy Action Observation) :
    logStage π 0 = 2 * Real.log 2 := by
  rw [logStage_eq]
  simp only [predictive_root, uniformDist_entropy, ← sum_mul, (π.2 _).2, one_mul,
    (mass_valid π 0).2]

theorem squaredStage_root (π : ValidCausalPolicy Action Observation) :
    squaredStage π 0 = 3/4 := by
  rw [squaredStage_eq]
  simp only [predictive_root]
  have hu : (1 - ∑ o : Observation, uniformDist o ^ 2) = 3/4 := by
    norm_num [uniformDist, Fin.sum_univ_succ]
  simp only [hu, ← sum_mul, (π.2 _).2, one_mul, (mass_valid π 0).2]

/-- Square and one-hot quadratic prediction error differ by one only in expectation. -/
theorem squareStage_eq (π : ValidCausalPolicy Action Observation) (t : ℕ) :
    squareStage π t = squaredStage π t - 1 := by
  rw [squareStage, stage_eq, squaredStage_eq]
  have he (q : Observation → ℝ) :
      (∑ o, q o * squareUtility q o) = (1 - ∑ o, q o^2) - 1 := by
    simp [squareUtility, ← sum_neg_distrib, pow_two]
  simp_rw [he, mul_sub, sum_sub_distrib, mul_one, (π.2 _).2]
  simp only [mul_sub, sum_sub_distrib, mul_one, (mass_valid π t).2]

/-- The posterior forecast of a monitor is the Bernoulli pulse question. -/
theorem predictive_monitor (π : ValidCausalPolicy Action Observation) (k : ℕ)
    (h : Trace (2*k+2)) (hm : mass π (2*k+2) h ≠ 0) (a : Action) :
    predictive π (2*k+2) h a =
      pulseLaw ((posteriorMeasure π (2*k+2) h).real {some k}) := by
  have he (θ : World) (o : Observation) :
      response θ (List.ofFn h) a o = pointDist (monitorLabel θ k) o := by
    rw [response_monitor θ _ a o (by simp) (by simp only [List.length_ofFn]; omega)]
    congr 2
    simp only [List.length_ofFn]
    omega
  have hj1 : joint π (2*k+2) h a 1 = alarmMass k * record π (2*k+2) (some k) h := by
    have hx : (fun θ => record π (2*k+2) θ h * response θ (List.ofFn h) a 1) =
        ({some k} : Set World).indicator (fun _ => record π (2*k+2) (some k) h) := by
      funext θ
      rw [he]
      by_cases hh : θ = some k
      · subst θ; simp [pointDist, monitorLabel]
      · simp [pointDist, monitorLabel, hh, Set.indicator_apply]
    rw [joint, hx, integral_indicator_const _ (measurableSet_singleton _)]
    simp only [smul_eq_mul, waitingQueryGeometricPrior_some]
    rfl
  have hj (o : Observation) (ho0 : o ≠ 0) (ho1 : o ≠ 1) :
      joint π (2*k+2) h a o = 0 := by
    have hz (θ : World) : pointDist (monitorLabel θ k) o = 0 := by
      by_cases hh : θ = some k <;> simp [pointDist, monitorLabel, hh, ho0, ho1]
    simp only [joint, he, hz, mul_zero, integral_zero]
  have hq1 : predictive π (2*k+2) h a 1 =
      (posteriorMeasure π (2*k+2) h).real {some k} := by
    rw [predictive, if_neg hm, hj1, posterior_monitor_atom π k h hm]
    rfl
  have hq2 : predictive π (2*k+2) h a 2 = 0 := by
    rw [predictive, if_neg hm, hj 2 (by decide) (by decide), zero_div]
  have hq3 : predictive π (2*k+2) h a 3 = 0 := by
    rw [predictive, if_neg hm, hj 3 (by decide) (by decide), zero_div]
  have hsum := (predictive_valid π (2*k+2) h a).2
  rw [sum_observation, hq1, hq2, hq3] at hsum
  funext o
  fin_cases o <;> norm_num [pulseLaw, pointDist]
  all_goals first | exact hq1 | exact hq2 | exact hq3 | linarith

/-- A generic binary forecast score at the kth actual monitor. -/
def monitorStage (f : ℝ → ℝ) (π : ValidCausalPolicy Action Observation) (k : ℕ) : ℝ :=
  ∑ h : Trace (2*k+2), mass π (2*k+2) h *
    f ((posteriorMeasure π (2*k+2) h).real {some k})

theorem monitor_weighted (f : ℝ → ℝ) (hf : f 0 = 0)
    (π : ValidCausalPolicy Action Observation) (k : ℕ) (h : Trace (2*k+2)) :
    mass π (2*k+2) h * f ((posteriorMeasure π (2*k+2) h).real {some k}) =
      experiment π.1 (2*k+2) (some k) h *
        (if (h 0).1 = inspect then 2 * alarmMass k * f (1/2)
          else silentMass k * f (alarmMass k / silentMass k)) := by
  by_cases hr : experiment π.1 (2*k+2) (some k) h = 0
  · rw [hr, zero_mul]
    by_cases hm : mass π (2*k+2) h = 0
    · rw [hm, zero_mul]
    · rw [posterior_monitor_atom π k h hm, hr]
      simp [hf]
  · have hmass := monitor_predictive_mass π k h hr
    have ha := alarmMass_pos k
    have hs := silentMass_pos k
    have hm : mass π (2*k+2) h ≠ 0 := by
      change priorSignalMass _ _ _ ≠ 0
      rw [hmass]; apply mul_ne_zero hr; split <;> positivity
    rw [posterior_monitor_atom π k h hm]
    change priorSignalMass _ _ _ * f _ = _
    rw [hmass]
    by_cases hi : (h 0).1 = inspect
    · rw [if_pos hi, if_pos hi]
      have he : alarmMass k * experiment π.1 (2*k+2) (some k) h /
          (experiment π.1 (2*k+2) (some k) h * (2*alarmMass k)) = (1/2:ℝ) := by
        field_simp
      rw [he]; ring
    · rw [if_neg hi, if_neg hi]
      have he : alarmMass k * experiment π.1 (2*k+2) (some k) h /
          (experiment π.1 (2*k+2) (some k) h * silentMass k) = alarmMass k / silentMass k := by
        field_simp
      rw [he]; ring

theorem monitorStage_eq (f : ℝ → ℝ) (hf : f 0 = 0)
    (π : ValidCausalPolicy Action Observation) (k : ℕ) :
    monitorStage f π k = inspectionProbability π.1 * (2*alarmMass k*f (1/2)) +
      (1-inspectionProbability π.1) * (silentMass k*f (alarmMass k/silentMass k)) := by
  simp only [monitorStage, monitor_weighted f hf]
  let I := 2*alarmMass k*f (1/2)
  let P := silentMass k*f (alarmMass k/silentMass k)
  have hd (h : Trace (2*k+2)) :
      experiment π.1 (2*k+2) (some k) h * (if (h 0).1 = inspect then I else P) =
      (if (h 0).1 = inspect then experiment π.1 (2*k+2) (some k) h else 0) *
        (I-P) + experiment π.1 (2*k+2) (some k) h * P := by split <;> ring
  change (∑ h, experiment π.1 (2*k+2) (some k) h *
    (if (h 0).1 = inspect then I else P)) = _
  simp_rw [hd]
  rw [sum_add_distrib, ← sum_mul, ← sum_mul,
    rootInspection_mass π.1 π.2 (some k) (2*k+1), (experiment_valid π.1 π.2 _ (some k)).2]
  dsimp [I, P]; ring

theorem logStage_monitor (π : ValidCausalPolicy Action Observation) (k : ℕ) :
    logStage π (2*k+2) = inspectionProbability π.1 * (2*alarmMass k*Real.log 2) +
      (1-inspectionProbability π.1) *
        (silentMass k * Real.binEntropy (alarmMass k/silentMass k)) := by
  have he : logStage π (2*k+2) = monitorStage Real.binEntropy π k := by
    rw [logStage_eq, monitorStage]
    apply sum_congr rfl; intro h _
    by_cases hm : mass π (2*k+2) h = 0
    · simp [hm]
    · simp_rw [predictive_monitor π k h hm, pulseLaw_entropy, ← sum_mul, (π.2 _).2, one_mul]
  rw [he, monitorStage_eq _ Real.binEntropy_zero]
  have hh : Real.binEntropy (1/2 : ℝ) = Real.log 2 := by
    simpa only [one_div] using Real.binEntropy_two_inv
  rw [hh]

theorem squaredStage_monitor (π : ValidCausalPolicy Action Observation) (k : ℕ) :
    squaredStage π (2*k+2) = inspectionProbability π.1 * alarmMass k +
      (1-inspectionProbability π.1) * playTerm k := by
  have he : squaredStage π (2*k+2) = monitorStage (fun p => 2*p*(1-p)) π k := by
    rw [squaredStage_eq, monitorStage]
    apply sum_congr rfl; intro h _
    by_cases hm : mass π (2*k+2) h = 0
    · simp [hm]
    · simp_rw [predictive_monitor π k h hm]
      have hr : 1 - ∑ o, pulseLaw ((posteriorMeasure π (2*k+2) h).real {some k}) o ^ 2 =
          2*((posteriorMeasure π (2*k+2) h).real {some k}) *
            (1-((posteriorMeasure π (2*k+2) h).real {some k})) := by
        rw [← oneHotRisk_eq_one_sub_sum_sq _ (pulseLaw_sum _), pulseLaw_oneHotRisk]
      simp_rw [hr, ← sum_mul, (π.2 _).2, one_mul]
  rw [he, monitorStage_eq _ (by norm_num)]
  have hs := ne_of_gt (silentMass_pos k)
  unfold playTerm
  field_simp
  ring

end IdExp.AlarmPanelPredictive
