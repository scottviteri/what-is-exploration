import Formal.AlarmPanelVarianceSeries
import Formal.AlarmPanelPosteriorCore
import Formal.AlarmPanelNativeAudit

/-!
# Actual posterior predictive-coordinate variance on the alarm/panel interface

Coordinate variance is computed under the genuine Bayes posterior of the complete
retained history, with the prior assigned at null records. Actions are conditioned
on, and the four raw sensor coordinates are retained.
-/
noncomputable section
namespace IdExp.AlarmPanelVariance
open AlarmPanel MeasureTheory Finset Set Filter Topology

/-- Sum of coordinate variances of the world-specific response probability vector. -/
def coordinateVariance (μ : Measure World) (q : World → Observation → ℝ) : ℝ :=
  ∑ o : Observation, ((∫ θ, (q θ o)^2 ∂μ) - (∫ θ, q θ o ∂μ)^2)

def posteriorMeasure (π : ValidCausalPolicy Action Observation) (t : ℕ)
    (h : CausalFiniteTrace Action Observation t) : Measure World :=
  priorPosteriorMeasure AlarmPanelPrior.prior (experiment π.1 t) h

instance posteriorMeasure_probability (π : ValidCausalPolicy Action Observation) (t : ℕ)
    (h : CausalFiniteTrace Action Observation t) : IsProbabilityMeasure (posteriorMeasure π t h) :=
  priorPosteriorMeasure_probability AlarmPanelPrior.prior (experiment π.1 t)
    (experiment_valid π.1 π.2 t)
    (PulseBrierScore.likelihood_integrable _ (experiment_valid π.1 π.2 t)) h

def localVariance (π : ValidCausalPolicy Action Observation) (t : ℕ)
    (h : CausalFiniteTrace Action Observation t) (a : Action) : ℝ :=
  coordinateVariance (posteriorMeasure π t h) (fun θ => response θ (List.ofFn h) a)

def stageVariance (π : ValidCausalPolicy Action Observation) (t : ℕ) : ℝ :=
  ∑ h : CausalFiniteTrace Action Observation t,
    priorSignalMass AlarmPanelPrior.prior (experiment π.1 t) h *
      ∑ a : Action, π.1 (List.ofFn h) a * localVariance π t h a

def objective (π : ValidCausalPolicy Action Observation) : ℝ := ∑' t, stageVariance π t

theorem sum_observation (f : Observation → ℝ) : (∑ o, f o) = f 0 + f 1 + f 2 + f 3 := by
  norm_num [Fin.sum_univ_succ]
  change f 0 + (f 1 + (f 2 + f 3)) = _
  ring

theorem coordinateVariance_constant (μ : Measure World) [IsProbabilityMeasure μ]
    (q : Observation → ℝ) : coordinateVariance μ (fun _ => q) = 0 := by
  simp [coordinateVariance]

theorem singleton_indicator_integral (μ : Measure World) (k : ℕ) :
    (∫ θ, (if θ = some k then (1 : ℝ) else 0) ∂μ) = μ.real {some k} := by
  have he : (fun θ : World => if θ = some k then (1:ℝ) else 0) =
      ({some k} : Set World).indicator (fun _ => (1:ℝ)) := by funext θ; simp [Set.indicator_apply]
  rw [he, integral_indicator_const _ (measurableSet_singleton _)]
  simp

theorem complement_indicator_integral (μ : Measure World) [IsProbabilityMeasure μ] (k : ℕ) :
    (∫ θ, (if θ = some k then (0 : ℝ) else 1) ∂μ) = 1 - μ.real {some k} := by
  have he : (fun θ : World => if θ = some k then (0:ℝ) else 1) =
      ({some k}ᶜ : Set World).indicator (fun _ => (1:ℝ)) := by
    funext θ; by_cases h : θ = some k <;> simp [h]
  rw [he, integral_indicator_const _ (measurableSet_singleton _).compl]
  simp [measureReal_compl (measurableSet_singleton _)]

/-- The monitor is a Bernoulli coordinate pair under any posterior, regardless of history size. -/
theorem coordinateVariance_monitor (μ : Measure World) [IsProbabilityMeasure μ] (k : ℕ) :
    coordinateVariance μ (fun θ => pointDist (monitorLabel θ k)) =
      2 * μ.real {some k} * (1 - μ.real {some k}) := by
  have h0 : (fun θ : World => pointDist (monitorLabel θ k) 0) =
      (fun θ => if θ = some k then (0:ℝ) else 1) := by
    funext θ; by_cases h : θ = some k <;>
      simp [pointDist, monitorLabel, h, show (0 : Observation) ≠ 1 by decide]
  have h1 : (fun θ : World => pointDist (monitorLabel θ k) 1) =
      (fun θ => if θ = some k then (1:ℝ) else 0) := by
    funext θ; by_cases h : θ = some k <;>
      simp [pointDist, monitorLabel, h, show (1 : Observation) ≠ 0 by decide]
  have h2 : (fun θ : World => pointDist (monitorLabel θ k) 2) = (fun _ => (0:ℝ)) := by
    funext θ; by_cases h : θ = some k <;>
      simp [pointDist, monitorLabel, h, show (2 : Observation) ≠ 1 by decide,
        show (2 : Observation) ≠ 0 by decide]
  have h3 : (fun θ : World => pointDist (monitorLabel θ k) 3) = (fun _ => (0:ℝ)) := by
    funext θ; by_cases h : θ = some k <;>
      simp [pointDist, monitorLabel, h, show (3 : Observation) ≠ 1 by decide,
        show (3 : Observation) ≠ 0 by decide]
  have hs (x : Observation) (θ : World) : (pointDist (monitorLabel θ k) x)^2 =
      pointDist (monitorLabel θ k) x := by unfold pointDist; split <;> norm_num
  simp only [coordinateVariance, hs, sum_observation]
  rw [h0, h1, h2, h3, singleton_indicator_integral, complement_indicator_integral]
  simp
  ring

/-- Known panel colors carry zero across-world predictive variance, including at null signals. -/
theorem localVariance_panel (π : ValidCausalPolicy Action Observation) (k : ℕ)
    (h : CausalFiniteTrace Action Observation (2*k+1)) (a : Action) :
    localVariance π (2*k+1) h a = 0 := by
  have hp : (List.ofFn h).length % 2 = 1 := by simp only [List.length_ofFn]; omega
  have he : (fun θ => response θ (List.ofFn h) a) = (fun _ =>
      if inspected (List.ofFn h) then pointDist 0 else pairDist (a == play1)) := by
    funext θ o; simpa only [ite_apply] using response_panel θ _ a o hp
  rw [localVariance, he]
  exact coordinateVariance_constant _ _

/-- Actual Bayes monitor variance; the posterior is on the complete retained record. -/
theorem localVariance_monitor (π : ValidCausalPolicy Action Observation) (k : ℕ)
    (h : CausalFiniteTrace Action Observation (2*k+2)) (a : Action) :
    localVariance π (2*k+2) h a =
      2 * (posteriorMeasure π (2*k+2) h).real {some k} *
        (1 - (posteriorMeasure π (2*k+2) h).real {some k}) := by
  have hn : List.ofFn h ≠ [] := by simp
  have hp : (List.ofFn h).length % 2 ≠ 1 := by simp only [List.length_ofFn]; omega
  have hk : ((List.ofFn h).length - 2)/2 = k := by simp only [List.length_ofFn]; omega
  have he : (fun θ => response θ (List.ofFn h) a) =
      (fun θ => pointDist (monitorLabel θ k)) := by
    funext θ o; rw [response_monitor θ _ a o hn hp, hk]
  rw [localVariance, he]
  exact coordinateVariance_monitor _ _

theorem stageVariance_panel (π : ValidCausalPolicy Action Observation) (k : ℕ) :
    stageVariance π (2*k+1) = 0 := by simp [stageVariance, localVariance_panel]

@[simp] theorem posteriorMeasure_root (π : ValidCausalPolicy Action Observation)
    (h : CausalFiniteTrace Action Observation 0) : posteriorMeasure π 0 h = AlarmPanelPrior.prior := by
  have he (θ : World) : experiment π.1 0 θ h = 1 := by
    simp [experiment, causalFiniteExperiment, causalTraceProb, causalTraceProbFrom, List.ofFn_zero]
  simp [posteriorMeasure, priorPosteriorMeasure, priorSignalDensity, priorSignalMass, he]

theorem coordinateVariance_root (a : Action) :
    coordinateVariance AlarmPanelPrior.prior (fun θ => response θ [] a) =
      if a = inspect then 1/4 else 0 := by
  have hm (o : Observation) : (∫ θ, response θ [] a o ∂AlarmPanelPrior.prior) =
      (1/2 : ℝ) * response none [] a o + (1/2 : ℝ) * response (some 0) [] a o :=
    AlarmPanelPrior.integral_none_some _ (by intro k; simp [response_root])
  have hs (o : Observation) : (∫ θ, (response θ [] a o)^2 ∂AlarmPanelPrior.prior) =
      (1/2 : ℝ) * (response none [] a o)^2 + (1/2 : ℝ) * (response (some 0) [] a o)^2 :=
    AlarmPanelPrior.integral_none_some _ (by intro k; simp [response_root])
  simp only [coordinateVariance, hm, hs]
  by_cases hi : a = inspect
  · subst a
    norm_num [response_root, pairDist, sum_observation]
  · norm_num [response_root, hi, uniformDist, sum_observation]

theorem localVariance_root (π : ValidCausalPolicy Action Observation)
    (h : CausalFiniteTrace Action Observation 0) (a : Action) :
    localVariance π 0 h a = if a = inspect then 1/4 else 0 := by
  simp only [localVariance, List.ofFn_zero, posteriorMeasure_root]
  exact coordinateVariance_root a

theorem stageVariance_root (π : ValidCausalPolicy Action Observation) :
    stageVariance π 0 = inspectionProbability π.1 / 4 := by
  have hm (h : CausalFiniteTrace Action Observation 0) :
      priorSignalMass AlarmPanelPrior.prior (experiment π.1 0) h = 1 := by
    simp [priorSignalMass, experiment, causalFiniteExperiment, causalTraceProb, causalTraceProbFrom,
      List.ofFn_zero]
  simp [stageVariance, hm, localVariance_root, List.ofFn_zero, mul_ite,
    inspectionProbability, div_eq_mul_inv]

theorem late_finite_monitorEquivalent (k j : ℕ) (hj : k ≤ j) :
    MonitorEquivalent (2*k+2) (some j) (some k) := by
  intro i hi
  have hik : i < k := by omega
  simp only [Option.some.injEq]
  omega

theorem none_monitorEquivalent (k : ℕ) : MonitorEquivalent (2*k+2) none (some k) := by
  intro i hi
  have hik : i < k := by omega
  simp only [Option.some.injEq, reduceCtorEq, false_iff]
  omega

theorem finiteTail_mass (k : ℕ) :
    AlarmPanelPrior.prior.real (waitingQueryTailSet (k+1)) = 2 * alarmMass k := by
  change waitingQueryTail AlarmPanelPrior.prior (k+1) = _
  rw [waitingQueryGeometric_tail _ (by omega)]
  unfold alarmMass
  rw [show k+2 = (k+1)+1 by omega, pow_succ]
  ring

/-- On a record compatible with pulse time k, earlier pulse worlds have zero
likelihood and every later finite world has exactly the same likelihood. -/
theorem monitor_likelihood_shape (π : ValidCausalPolicy Action Observation) (k : ℕ)
    (h : CausalFiniteTrace Action Observation (2*k+2))
    (hh : experiment π.1 (2*k+2) (some k) h ≠ 0) :
    (fun θ => experiment π.1 (2*k+2) θ h) =
      (fun θ => (waitingQueryTailSet (k+1)).indicator
        (fun _ => experiment π.1 (2*k+2) (some k) h) θ +
        ({none} : Set World).indicator
          (fun _ => if (h 0).1 = inspect then 0 else experiment π.1 (2*k+2) (some k) h) θ) := by
  funext θ
  cases θ with
  | none =>
    have hn : none ∉ waitingQueryTailSet (k+1) := by simp [waitingQueryTailSet]
    simp only [Set.indicator_of_notMem hn, zero_add, mem_singleton_iff,
      Set.indicator_of_mem (show none ∈ ({none} : Set World) by simp)]
    by_cases hi : (h 0).1 = inspect
    · rw [if_pos hi]
      by_contra hnone
      have hp := supported_inspection_bit π.1 (some k) (2*k+1) h hh hi
      have hn := supported_inspection_bit π.1 none (2*k+1) h hnone hi
      rw [hp] at hn
      contradiction
    · rw [if_neg hi]
      exact row_eq_on_monitor_equivalent π.1 (2*k+1) (none_monitorEquivalent k) h
        (fun hb => (hi hb).elim)
  | some j =>
    have hm : some j ∈ waitingQueryTailSet (k+1) ↔ k ≤ j := by
      simp only [waitingQueryTailSet, mem_setOf_eq, Option.some.injEq, exists_eq_left']
      omega
    simp only [Set.indicator_of_notMem (show some j ∉ ({none} : Set World) by simp), add_zero]
    by_cases hj : k ≤ j
    · rw [Set.indicator_of_mem (hm.mpr hj)]
      exact row_eq_on_monitor_equivalent π.1 (2*k+1) (late_finite_monitorEquivalent k j hj) h
        (fun _ => rfl)
    · rw [Set.indicator_of_notMem (mt hm.mp hj)]
      exact past_pulse_row_zero π.1 k j (by omega) h hh

/-- Exact Bayes normalizer of every positive pulse-k likelihood row. -/
theorem monitor_predictive_mass (π : ValidCausalPolicy Action Observation) (k : ℕ)
    (h : CausalFiniteTrace Action Observation (2*k+2))
    (hh : experiment π.1 (2*k+2) (some k) h ≠ 0) :
    priorSignalMass AlarmPanelPrior.prior (experiment π.1 (2*k+2)) h =
      experiment π.1 (2*k+2) (some k) h *
        (if (h 0).1 = inspect then 2 * alarmMass k else silentMass k) := by
  unfold priorSignalMass
  rw [monitor_likelihood_shape π k h hh]
  rw [integral_add ((integrable_const _).indicator (show MeasurableSet
      (waitingQueryTailSet (k+1)) from trivial))
    ((integrable_const _).indicator (measurableSet_singleton _))]
  rw [integral_indicator_const _ (show MeasurableSet (waitingQueryTailSet (k+1)) from trivial),
    integral_indicator_const _ (measurableSet_singleton _), finiteTail_mass,
    waitingQueryGeometricPrior_none]
  simp only [smul_eq_mul]
  by_cases hi : (h 0).1 = inspect <;> simp [hi, silentMass_eq] <;> ring

theorem posterior_monitor_atom (π : ValidCausalPolicy Action Observation) (k : ℕ)
    (h : CausalFiniteTrace Action Observation (2*k+2))
    (hm : priorSignalMass AlarmPanelPrior.prior (experiment π.1 (2*k+2)) h ≠ 0) :
    (posteriorMeasure π (2*k+2) h).real {some k} =
      alarmMass k * experiment π.1 (2*k+2) (some k) h /
        priorSignalMass AlarmPanelPrior.prior (experiment π.1 (2*k+2)) h := by
  have hp := PulseBrierScore.posteriorReport_bayes (experiment π.1 (2*k+2))
    (experiment_valid π.1 π.2 _) h hm (some k)
  change (posteriorMeasure π (2*k+2) h).real {some k} = _ at hp
  rw [waitingQueryGeometricPrior_some] at hp
  exact hp

/-- Bayes weighting cancels the known panel likelihood, including every null-signal case. -/
theorem monitor_weightedVariance (π : ValidCausalPolicy Action Observation) (k : ℕ)
    (h : CausalFiniteTrace Action Observation (2*k+2)) (a : Action) :
    priorSignalMass AlarmPanelPrior.prior (experiment π.1 (2*k+2)) h * localVariance π (2*k+2) h a =
      experiment π.1 (2*k+2) (some k) h *
        (if (h 0).1 = inspect then alarmMass k else playTerm k) := by
  rw [localVariance_monitor]
  by_cases hr : experiment π.1 (2*k+2) (some k) h = 0
  · rw [hr, zero_mul]
    by_cases hm : priorSignalMass AlarmPanelPrior.prior (experiment π.1 (2*k+2)) h = 0
    · rw [hm, zero_mul]
    · rw [posterior_monitor_atom π k h hm, hr]
      simp
  · have hmass := monitor_predictive_mass π k h hr
    have ha := alarmMass_pos k
    have hs := silentMass_pos k
    have hm : priorSignalMass AlarmPanelPrior.prior (experiment π.1 (2*k+2)) h ≠ 0 := by
      rw [hmass]
      apply mul_ne_zero hr
      split <;> positivity
    rw [posterior_monitor_atom π k h hm, hmass]
    by_cases hi : (h 0).1 = inspect
    · rw [if_pos hi, if_pos hi]
      field_simp [hr, ne_of_gt ha]
      ring
    · rw [if_neg hi, if_neg hi]
      unfold playTerm
      field_simp [hr, ne_of_gt hs]

/-- Exact expected kth-monitor bonus for every randomized history policy. -/
theorem stageVariance_monitor (π : ValidCausalPolicy Action Observation) (k : ℕ) :
    stageVariance π (2*k+2) = inspectionProbability π.1 * alarmMass k +
      (1-inspectionProbability π.1) * playTerm k := by
  have he (h : CausalFiniteTrace Action Observation (2*k+2)) :
      priorSignalMass AlarmPanelPrior.prior (experiment π.1 (2*k+2)) h *
        (∑ a : Action, π.1 (List.ofFn h) a * localVariance π (2*k+2) h a) =
      experiment π.1 (2*k+2) (some k) h *
        (if (h 0).1 = inspect then alarmMass k else playTerm k) := by
    simp only [mul_sum, mul_left_comm _ (π.1 (List.ofFn h) _), monitor_weightedVariance,
      ← sum_mul, (π.2 (List.ofFn h)).2, one_mul]
  simp only [stageVariance, he]
  have hd (h : CausalFiniteTrace Action Observation (2*k+2)) :
      experiment π.1 (2*k+2) (some k) h * (if (h 0).1 = inspect then alarmMass k else playTerm k) =
      (if (h 0).1 = inspect then experiment π.1 (2*k+2) (some k) h else 0) *
          (alarmMass k - playTerm k) + experiment π.1 (2*k+2) (some k) h * playTerm k := by
    split <;> ring
  simp_rw [hd]
  rw [sum_add_distrib, ← sum_mul, ← sum_mul,
    rootInspection_mass π.1 π.2 (some k) (2*k+1), (experiment_valid π.1 π.2 _ (some k)).2]
  ring

theorem monitor_summable (π : ValidCausalPolicy Action Observation) :
    Summable (fun k => stageVariance π (2*k+2)) := by
  simp_rw [stageVariance_monitor]
  exact (alarmMass_summable.mul_left _).add (playTerm_summable.mul_left _)

theorem stageVariance_summable (π : ValidCausalPolicy Action Observation) :
    Summable (stageVariance π) := by
  apply (summable_nat_add_iff 1).1
  apply Summable.even_add_odd
  · simp only [stageVariance_panel]
    exact summable_zero
  · simpa only [Nat.add_assoc, show (1:ℕ)+1=2 by decide] using monitor_summable π

/-- The complete actual posterior-coordinate objective, with all convergence
and response-law calculations discharged, is the displayed root mixture. -/
theorem objective_eq_mixture (π : ValidCausalPolicy Action Observation) :
    objective π = mixture (inspectionProbability π.1) := by
  have hz : Summable (fun k => stageVariance π (2*k+1)) := by
    simp only [stageVariance_panel]; exact summable_zero
  have hm : Summable (fun k => stageVariance π (2*k+1+1)) := by
    simpa only [Nat.add_assoc, show (1:ℕ)+1=2 by decide] using monitor_summable π
  have he := @tsum_even_add_odd ℝ _ _ _ _ (fun n => stageVariance π (n+1)) hz hm
  simp only [stageVariance_panel, tsum_zero, zero_add, Nat.add_assoc,
    show (1:ℕ)+1=2 by decide] at he
  have ht := (stageVariance_summable π).sum_add_tsum_nat_add 1
  simp only [sum_range_one] at ht
  rw [← he, stageVariance_root] at ht
  simp_rw [stageVariance_monitor] at ht
  rw [Summable.tsum_add (alarmMass_summable.mul_left _) (playTerm_summable.mul_left _),
    tsum_mul_left, tsum_mul_left, alarmMass_sum] at ht
  unfold objective mixture playTotal
  rw [inspectTotal_eq]
  rw [← ht]
  ring

/-- Every complete predictive-variance maximizer forfeits inspection. -/
theorem objective_le (π : ValidCausalPolicy Action Observation) : objective π ≤ playTotal := by
  rw [objective_eq_mixture]
  exact mixture_le _ (inspectionProbability_nonneg π.1 π.2)

theorem objective_eq_max_iff (π : ValidCausalPolicy Action Observation) :
    objective π = playTotal ↔ inspectionProbability π.1 = 0 := by
  rw [objective_eq_mixture]
  exact mixture_eq_iff _ (inspectionProbability_nonneg π.1 π.2)

/-- Every inspecting policy has complete predictive-variance return exactly 3/4. -/
theorem inspection_value (π : ValidCausalPolicy Action Observation)
    (hπ : inspectionProbability π.1 = 1) : objective π = 3/4 := by
  rw [objective_eq_mixture, hπ, mixture, inspectTotal_eq]
  ring

/-- A seven-observation planning horizon already exhibits a strict variance failure. -/
theorem sum_first_seven_eq (π : ValidCausalPolicy Action Observation) :
    (∑ t ∈ Finset.range 7, stageVariance π t) =
      inspectionProbability π.1 * (11/16 : ℝ) + (1-inspectionProbability π.1) * (167/240 : ℝ) := by
  norm_num [Finset.sum_range_succ, stageVariance_root,
    stageVariance_panel π 0, stageVariance_panel π 1, stageVariance_panel π 2,
    stageVariance_monitor π 0, stageVariance_monitor π 1, stageVariance_monitor π 2,
    alarmMass, playTerm, silentMass]
  ring

theorem sum_first_seven_le (π : ValidCausalPolicy Action Observation) :
    (∑ t ∈ Finset.range 7, stageVariance π t) ≤ (167/240 : ℝ) := by
  rw [sum_first_seven_eq]
  have hn := inspectionProbability_nonneg π.1 π.2
  linarith

theorem sum_first_seven_eq_max_iff (π : ValidCausalPolicy Action Observation) :
    (∑ t ∈ Finset.range 7, stageVariance π t) = (167/240 : ℝ) ↔ inspectionProbability π.1 = 0 := by
  rw [sum_first_seven_eq]
  constructor
  · intro h; linarith
  · intro h; simp [h]

end IdExp.AlarmPanelVariance
