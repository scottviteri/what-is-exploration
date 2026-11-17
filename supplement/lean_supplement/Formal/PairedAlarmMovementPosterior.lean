import Formal.PairedAlarmNativeExtraction
import Formal.AlarmPanelVariance

/-!
# Full-history Bayes posterior on the paired alarm interface

The countable world posterior of the complete retained action-observation
record, under the fixed positive geometric prior `AlarmPanelPrior.prior`
(`α(none) = 1/2`, `α(some k) = 2^{-(k+2)}`). Every observation after startup
reports the world-independent display and the alarm monitor together, so alarm
tick `k` is reported by the observation made after a history of length `k+1`.

On a history of length `k+1` that is compatible with pulse time `k`, the
likelihood row is constant on the later finite worlds, vanishes on earlier
pulses, and on the never-alarm world equals zero after inspection and the same
constant otherwise. This yields the exact Bayes normalizer and posterior atom
used by the posterior-movement rewards, including null-record cases.

Only interface-independent prior and series facts are imported from the
alternating study (`alarmMass`, `silentMass`, `finiteTail_mass`); every
response-law statement below is proved for the paired `response`.
-/

noncomputable section
namespace IdExp.PairedAlarm.Movement
open MeasureTheory Finset Set
open AlarmPanelVariance (alarmMass silentMass alarmMass_pos silentMass_pos silentMass_eq
  finiteTail_mass)

/-- The startup pair `(action, observation)` carries the whole first-step law. -/
theorem firstExpectation (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (θ : World) (n : ℕ) (f : Action × Observation → ℝ) :
    (∑ h : CausalFiniteTrace Action Observation (n+1), experiment π (n+1) θ h * f (h 0)) =
    ∑ ao : Action × Observation, π [] ao.1 * response θ [] ao.1 ao.2 * f ao := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Action × Observation)).sum_comp]
  rw [Fintype.sum_prod_type]
  have hc (ao : Action × Observation) (rest : CausalFiniteTrace Action Observation n) :
      (Fin.consEquiv (fun _ : Fin (n+1) => Action × Observation)) (ao,rest) =
        Fin.cons ao rest := by funext i; exact Fin.consEquiv_apply _ _ i
  simp_rw [hc]
  change (∑ ao, ∑ rest : CausalFiniteTrace Action Observation n,
    causalTraceProb π (response θ) (List.ofFn (Fin.cons ao rest)) * f ao) = _
  simp only [causalTraceProb, List.ofFn_cons, causalTraceProbFrom]
  have he (ao : Action × Observation) :
      (∑ rest : CausalFiniteTrace Action Observation n,
        π [] ao.1 * response θ [] ao.1 ao.2 *
          causalTraceProbFrom π (response θ) ([] ++ [ao]) (List.ofFn rest) * f ao) =
        π [] ao.1 * response θ [] ao.1 ao.2 * f ao := by
    calc
      _ = (π [] ao.1 * response θ [] ao.1 ao.2 * f ao) *
          ∑ rest : CausalFiniteTrace Action Observation n,
            causalTraceProbFrom π (response θ) [ao] (List.ofFn rest) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro rest _; simp only [List.nil_append]; ring
      _ = _ := by rw [sum_causalTraceProbFrom π hπ (response θ) (response_valid θ)]; ring
  exact Finset.sum_congr rfl (fun ao _ => he ao)

/-- In every world, the records whose startup action is INSPECT have total
probability equal to the root inspection probability. -/
theorem rootInspection_mass (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (θ : World) (n : ℕ) :
    (∑ h : CausalFiniteTrace Action Observation (n+1),
      if (h 0).1 = inspect then experiment π (n+1) θ h else 0) = inspectionProbability π := by
  have he := firstExpectation π hπ θ n (fun ao => if ao.1 = inspect then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at he
  rw [he, Fintype.sum_prod_type]
  have hrow (a : Action) : (∑ o : Observation,
      if a = inspect then π [] a * response θ [] a o else 0) =
      if a = inspect then π [] a else 0 := by
    split_ifs
    · rw [← Finset.mul_sum, (response_valid θ [] a).2, mul_one]
    · simp
  simp only [hrow, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

/-- Two worlds agree on the alarm ticks reported before trace position `n`;
tick `k` sits at trace position `k+1`. -/
def MonitorEquivalent (n : ℕ) (θ η : World) : Prop :=
  ∀ k, k + 1 < n → (θ = some k ↔ η = some k)

theorem response_eq_of_monitors (n : ℕ) {θ η : World}
    (he : MonitorEquivalent n θ η) (h : History) (hh : h ≠ [])
    (hn : h.length < n) (a : Action) : response θ h a = response η h a := by
  funext o
  rw [response_tick θ h a o hh, response_tick η h a o hh]
  have hpos : 0 < h.length := List.length_pos_iff.mpr hh
  have hidx : (h.length - 1) + 1 < n := by omega
  simp only [monitorLabel, he _ hidx]

theorem traceProbFrom_eq_of_monitors (π : CausalPolicy Action Observation)
    (n : ℕ) {θ η : World} (he : MonitorEquivalent n θ η)
    (pre rest : History) (hp : pre ≠ []) (hl : pre.length + rest.length ≤ n) :
    causalTraceProbFrom π (response θ) pre rest =
      causalTraceProbFrom π (response η) pre rest := by
  induction rest generalizing pre with
  | nil => rfl
  | cons ao rest ih =>
    simp only [causalTraceProbFrom]
    rw [response_eq_of_monitors n he pre hp (by simp only [List.length_cons] at hl; omega)]
    rw [ih (pre ++ [ao]) (by simp) (by simp only [List.length_append,
      List.length_cons, List.length_nil] at *; omega)]

/-- Monitor-equivalent worlds have equal likelihood rows, provided they agree
on the startup bit whenever the record starts with INSPECT. -/
theorem row_eq_on_monitor_equivalent (π : CausalPolicy Action Observation)
    (n : ℕ) {θ η : World} (he : MonitorEquivalent (n+1) θ η)
    (h : CausalFiniteTrace Action Observation (n+1))
    (hb : (h 0).1 = inspect → θ.isSome = η.isSome) :
    experiment π (n+1) θ h = experiment π (n+1) η h := by
  change causalTraceProb π (response θ) (List.ofFn h) =
    causalTraceProb π (response η) (List.ofFn h)
  rw [causalTraceProb, causalTraceProb, List.ofFn_succ]
  simp only [causalTraceProbFrom, response_root]
  have hr : rootDisplay θ (h 0).1 (h 0).2.1 = rootDisplay η (h 0).1 (h 0).2.1 := by
    by_cases hi : (h 0).1 = inspect
    · simp only [rootDisplay, if_pos hi, hb hi]
    · simp only [rootDisplay, if_neg hi]
  rw [hr, traceProbFrom_eq_of_monitors π (n+1) he _ _ (by simp) (by simp; omega)]

/-- On a supported inspected record, the startup display reveals whether the
alarm ever rings. -/
theorem supported_inspection_bit (π : CausalPolicy Action Observation) (θ : World)
    (n : ℕ) (h : CausalFiniteTrace Action Observation (n+1))
    (hh : experiment π (n+1) θ h ≠ 0) (hi : (h 0).1 = inspect) :
    decide (2 ≤ (h 0).2.1.val) = θ.isSome := by
  have he := experiment_response_ne_zero π θ (n+1) h hh 0
  simp only [Fin.val_zero, List.take_zero, response_root, rootDisplay, hi, ↓reduceIte] at he
  have hn := left_ne_zero_of_mul he
  have hd : (h 0).2.1 = (if θ.isSome then 2 else 0) := by
    by_contra hd
    simp [pointDisplay, hd] at hn
  rw [hd]
  cases θ <;> norm_num

/-- A record supported by pulse time `k` excludes every earlier pulse time:
the earlier tick was reported silent. -/
theorem past_pulse_row_zero (π : CausalPolicy Action Observation) (k j : ℕ) (hj : j < k)
    (h : CausalFiniteTrace Action Observation (k+1))
    (hh : experiment π (k+1) (some k) h ≠ 0) :
    experiment π (k+1) (some j) h = 0 := by
  by_contra hjh
  have hkobs := supported_monitor π (some k) (k+1) h hh ⟨j+1, by omega⟩
  have hjobs := supported_monitor π (some j) (k+1) h hjh ⟨j+1, by omega⟩
  have hkj : k ≠ j := by omega
  simp only [monitorAt_succ, monitorLabel, Option.some.injEq, if_neg hkj,
    ↓reduceIte] at hkobs hjobs
  have : (0 : Monitor) = 1 := hkobs.symm.trans hjobs
  exact absurd this (by decide)

/-- The actual Bayes posterior over worlds given the complete retained record,
with the prior assigned at null records. -/
def posteriorMeasure (π : ValidCausalPolicy Action Observation) (t : ℕ)
    (h : CausalFiniteTrace Action Observation t) : Measure World :=
  priorPosteriorMeasure AlarmPanelPrior.prior (experiment π.1 t) h

instance posteriorMeasure_probability (π : ValidCausalPolicy Action Observation) (t : ℕ)
    (h : CausalFiniteTrace Action Observation t) :
    IsProbabilityMeasure (posteriorMeasure π t h) :=
  priorPosteriorMeasure_probability AlarmPanelPrior.prior (experiment π.1 t)
    (experiment_valid π.1 π.2 t)
    (PulseBrierScore.likelihood_integrable _ (experiment_valid π.1 π.2 t)) h

theorem experiment_zero (π : CausalPolicy Action Observation) (θ : World)
    (h : CausalFiniteTrace Action Observation 0) : experiment π 0 θ h = 1 := by
  simp [experiment, causalFiniteExperiment, causalTraceProb, causalTraceProbFrom,
    List.ofFn_zero]

theorem priorSignalMass_zero (π : CausalPolicy Action Observation)
    (h : CausalFiniteTrace Action Observation 0) :
    priorSignalMass AlarmPanelPrior.prior (experiment π 0) h = 1 := by
  simp [priorSignalMass, experiment_zero]

@[simp] theorem posteriorMeasure_root (π : ValidCausalPolicy Action Observation)
    (h : CausalFiniteTrace Action Observation 0) :
    posteriorMeasure π 0 h = AlarmPanelPrior.prior := by
  simp [posteriorMeasure, priorPosteriorMeasure, priorSignalDensity,
    priorSignalMass_zero, experiment_zero]

theorem late_finite_monitorEquivalent (k j : ℕ) (hj : k ≤ j) :
    MonitorEquivalent (k+1) (some j) (some k) := by
  intro i hi
  simp only [Option.some.injEq]
  omega

theorem none_monitorEquivalent (k : ℕ) : MonitorEquivalent (k+1) none (some k) := by
  intro i hi
  simp only [Option.some.injEq, reduceCtorEq, false_iff]
  omega

/-- On a record of length `k+1` compatible with pulse time `k`, earlier pulse
worlds have zero likelihood and every later finite world has exactly the same
likelihood; the never-alarm world is excluded after inspection and has the same
likelihood otherwise. -/
theorem tick_likelihood_shape (π : ValidCausalPolicy Action Observation) (k : ℕ)
    (h : CausalFiniteTrace Action Observation (k+1))
    (hh : experiment π.1 (k+1) (some k) h ≠ 0) :
    (fun θ => experiment π.1 (k+1) θ h) =
      (fun θ => (waitingQueryTailSet (k+1)).indicator
        (fun _ => experiment π.1 (k+1) (some k) h) θ +
        ({none} : Set World).indicator
          (fun _ => if (h 0).1 = inspect then 0 else experiment π.1 (k+1) (some k) h) θ) := by
  funext θ
  cases θ with
  | none =>
    have hn : none ∉ waitingQueryTailSet (k+1) := by simp [waitingQueryTailSet]
    simp only [Set.indicator_of_notMem hn, zero_add,
      Set.indicator_of_mem (show none ∈ ({none} : Set World) by simp)]
    by_cases hi : (h 0).1 = inspect
    · rw [if_pos hi]
      by_contra hnone
      have hp := supported_inspection_bit π.1 (some k) k h hh hi
      have hn := supported_inspection_bit π.1 none k h hnone hi
      rw [hp] at hn
      contradiction
    · rw [if_neg hi]
      exact row_eq_on_monitor_equivalent π.1 k (none_monitorEquivalent k) h
        (fun hb => (hi hb).elim)
  | some j =>
    have hm : some j ∈ waitingQueryTailSet (k+1) ↔ k ≤ j := by
      simp only [waitingQueryTailSet, Set.mem_ofPred_eq, Option.some.injEq, exists_eq_left']
      omega
    simp only [Set.indicator_of_notMem (show some j ∉ ({none} : Set World) by simp), add_zero]
    by_cases hj : k ≤ j
    · rw [Set.indicator_of_mem (hm.mpr hj)]
      exact row_eq_on_monitor_equivalent π.1 k (late_finite_monitorEquivalent k j hj) h
        (fun _ => rfl)
    · rw [Set.indicator_of_notMem (mt hm.mp hj)]
      exact past_pulse_row_zero π.1 k j (by omega) h hh

/-- Exact Bayes normalizer of every positive pulse-`k` likelihood row at the
history length `k+1` where tick `k` is about to be reported. -/
theorem tick_predictive_mass (π : ValidCausalPolicy Action Observation) (k : ℕ)
    (h : CausalFiniteTrace Action Observation (k+1))
    (hh : experiment π.1 (k+1) (some k) h ≠ 0) :
    priorSignalMass AlarmPanelPrior.prior (experiment π.1 (k+1)) h =
      experiment π.1 (k+1) (some k) h *
        (if (h 0).1 = inspect then 2 * alarmMass k else silentMass k) := by
  unfold priorSignalMass
  rw [tick_likelihood_shape π k h hh]
  rw [integral_add ((integrable_const _).indicator (show MeasurableSet
      (waitingQueryTailSet (k+1)) from trivial))
    ((integrable_const _).indicator (measurableSet_singleton _))]
  rw [integral_indicator_const _ (show MeasurableSet (waitingQueryTailSet (k+1)) from trivial),
    integral_indicator_const _ (measurableSet_singleton _), finiteTail_mass,
    waitingQueryGeometricPrior_none]
  simp only [smul_eq_mul]
  by_cases hi : (h 0).1 = inspect <;> simp [hi, silentMass_eq] <;> ring

/-- Bayes' formula for the posterior probability that the alarm rings at tick
`k`, on every non-null record of length `k+1`. -/
theorem posterior_tick_atom (π : ValidCausalPolicy Action Observation) (k : ℕ)
    (h : CausalFiniteTrace Action Observation (k+1))
    (hm : priorSignalMass AlarmPanelPrior.prior (experiment π.1 (k+1)) h ≠ 0) :
    (posteriorMeasure π (k+1) h).real {some k} =
      alarmMass k * experiment π.1 (k+1) (some k) h /
        priorSignalMass AlarmPanelPrior.prior (experiment π.1 (k+1)) h := by
  have hp := PulseBrierScore.posteriorReport_bayes (experiment π.1 (k+1))
    (experiment_valid π.1 π.2 _) h hm (some k)
  change (posteriorMeasure π (k+1) h).real {some k} = _ at hp
  rw [waitingQueryGeometricPrior_some] at hp
  exact hp

end IdExp.PairedAlarm.Movement
