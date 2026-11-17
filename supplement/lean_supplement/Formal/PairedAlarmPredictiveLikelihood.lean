import Formal.PairedAlarmPredictiveCore
import Formal.AlarmPanelVarianceSeries

/-!
# Record likelihoods and Bayes normalizers on the paired alarm

Interface facts used by the predictive stage computation, proved directly for the
paired `response` (no alternating-interface theorem is used):

* the first action is inspection with probability `s = π(INSPECT | ∅)` in every
  world, for every randomized continuation;
* two worlds that agree on the startup bit (when inspected) and on every alarm
  tick reported before the horizon give the same record probability;
* on a record of length `k+1` compatible with a pulse at tick `k`, the
  prior-predictive mass is that record's pulse-`k` likelihood times
  `2 a_k` (inspected) or `S_k = 1/2 + 2 a_k` (played).

Here `a_k = 2^{-(k+2)}` is `AlarmPanelVariance.alarmMass k` and `S_k` is
`AlarmPanelVariance.silentMass k`; both are interface-free series constants.
-/

noncomputable section
namespace IdExp.PairedAlarm.Predictive
open MeasureTheory Finset
open AlarmPanelVariance (alarmMass silentMass alarmMass_pos silentMass_pos silentMass_eq)

/-- First-step marginal of the collected record of a causal policy. -/
theorem firstExpectation (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (θ : World) (n : ℕ) (f : Action × Observation → ℝ) :
    (∑ h : Trace (n+1), experiment π (n+1) θ h * f (h 0)) =
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

/-- In every world, the first action is inspection with probability `s`. -/
theorem rootInspection_mass (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (θ : World) (n : ℕ) :
    (∑ h : Trace (n+1), if (h 0).1 = inspect then experiment π (n+1) θ h else 0) =
      inspectionProbability π := by
  have he := firstExpectation π hπ θ n (fun ao => if ao.1 = inspect then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at he
  rw [he, Fintype.sum_prod_type, Finset.sum_eq_single inspect]
  · simp only [if_true]
    rw [← mul_sum, (response_valid θ [] inspect).2, mul_one]
    rfl
  · intro a _ ha
    exact sum_eq_zero fun o _ => if_neg ha
  · intro h; exact absurd (mem_univ _) h

/-- Prior-predictive averages are prior integrals of world-wise record averages. -/
theorem sum_mass_mul (π : ValidCausalPolicy Action Observation) (n : ℕ) (g : Trace n → ℝ) :
    ∑ h, mass π n h * g h = ∫ θ, ∑ h, record π n θ h * g h ∂prior := by
  rw [integral_finsetSum _ (fun h _ => (record_integrable π n h).mul_const _)]
  simp only [integral_mul_const, mass, priorSignalMass]

/-- In every fixed world, a startup-dependent payoff averages to the root mixture. -/
theorem record_inspection_sum (π : ValidCausalPolicy Action Observation) (θ : World)
    (n : ℕ) (c d : ℝ) :
    ∑ h : Trace (n+1), record π (n+1) θ h * (if (h 0).1 = inspect then c else d) =
      inspectionProbability π.1 * c + (1 - inspectionProbability π.1) * d := by
  have hd (h : Trace (n+1)) : record π (n+1) θ h * (if (h 0).1 = inspect then c else d) =
      (if (h 0).1 = inspect then record π (n+1) θ h else 0) * (c - d) +
        record π (n+1) θ h * d := by
    split <;> ring
  simp_rw [hd]
  rw [sum_add_distrib, ← sum_mul, ← sum_mul, rootInspection_mass π.1 π.2 θ n,
    (record_valid π (n+1) θ).2]
  ring

/-- Under the prior predictive law, the first action is inspection with probability `s`. -/
theorem inspectionMass_sum (π : ValidCausalPolicy Action Observation) (n : ℕ) (c d : ℝ) :
    ∑ h : Trace (n+1), mass π (n+1) h * (if (h 0).1 = inspect then c else d) =
      inspectionProbability π.1 * c + (1 - inspectionProbability π.1) * d := by
  rw [sum_mass_mul]
  simp_rw [record_inspection_sum π _ n c d]
  simp

/-- Two worlds agree on every alarm tick reported strictly before trace position `n`. -/
def MonitorEquivalent (n : ℕ) (θ η : World) : Prop :=
  ∀ k, k + 1 < n → (θ = some k ↔ η = some k)

theorem response_eq_of_monitors (n : ℕ) {θ η : World} (he : MonitorEquivalent n θ η)
    (h : History) (hh : h ≠ []) (hn : h.length < n) (a : Action) :
    response θ h a = response η h a := by
  funext o
  rw [response_tick θ h a o hh, response_tick η h a o hh]
  have hpos : 0 < h.length := List.length_pos_iff.mpr hh
  have hidx : h.length - 1 + 1 < n := by omega
  have hl : monitorLabel θ (h.length - 1) = monitorLabel η (h.length - 1) := by
    simp only [monitorLabel, he _ hidx]
  rw [hl]

theorem traceProbFrom_eq_of_monitors (π : CausalPolicy Action Observation) (n : ℕ)
    {θ η : World} (he : MonitorEquivalent n θ η) (pre rest : History) (hp : pre ≠ [])
    (hl : pre.length + rest.length ≤ n) :
    causalTraceProbFrom π (response θ) pre rest = causalTraceProbFrom π (response η) pre rest := by
  induction rest generalizing pre with
  | nil => rfl
  | cons ao rest ih =>
    simp only [causalTraceProbFrom]
    rw [response_eq_of_monitors n he pre hp (by simp only [List.length_cons] at hl; omega)]
    rw [ih (pre ++ [ao]) (by simp) (by simp only [List.length_append,
      List.length_cons, List.length_nil] at hl ⊢; omega)]

/-- Record rows agree when the worlds agree on the reported ticks and, after
inspection, on the startup bit. -/
theorem row_eq_on_monitor_equivalent (π : CausalPolicy Action Observation)
    (n : ℕ) {θ η : World} (he : MonitorEquivalent (n+1) θ η) (h : Trace (n+1))
    (hb : (h 0).1 = inspect → θ.isSome = η.isSome) :
    experiment π (n+1) θ h = experiment π (n+1) η h := by
  change causalTraceProb π (response θ) (List.ofFn h) = causalTraceProb π (response η) (List.ofFn h)
  rw [causalTraceProb, causalTraceProb, List.ofFn_succ]
  simp only [causalTraceProbFrom, response_root]
  have hr : rootDisplay θ (h 0).1 (h 0).2.1 = rootDisplay η (h 0).1 (h 0).2.1 := by
    by_cases hi : (h 0).1 = inspect
    · simp only [rootDisplay, if_pos hi, hb hi]
    · simp only [rootDisplay, if_neg hi]
  rw [hr, traceProbFrom_eq_of_monitors π (n+1) he _ _ (by simp)
    (by simp only [List.nil_append, List.length_singleton, List.length_ofFn]; omega)]

/-- After inspection, a supported record shows the world's startup bit. -/
theorem supported_inspection_bit (π : CausalPolicy Action Observation) (θ : World)
    (n : ℕ) (h : Trace (n+1)) (hh : experiment π (n+1) θ h ≠ 0) (hi : (h 0).1 = inspect) :
    decide (2 ≤ (h 0).2.1.val) = θ.isSome := by
  have he := experiment_response_ne_zero π θ (n+1) h hh 0
  simp only [Fin.val_zero, List.take_zero, response_root, rootDisplay, hi, ↓reduceIte] at he
  have hn := left_ne_zero_of_mul he
  have hd : (h 0).2.1 = (if θ.isSome then 2 else 0) := by
    by_contra hd
    simp [pointDisplay, hd] at hn
  rw [hd]
  cases θ <;> norm_num

/-- A world whose pulse precedes tick `k` cannot produce a record compatible with
a pulse at tick `k`. -/
theorem past_pulse_row_zero (π : CausalPolicy Action Observation) (k j : ℕ) (hj : j < k)
    (h : Trace (k+1)) (hh : experiment π (k+1) (some k) h ≠ 0) :
    experiment π (k+1) (some j) h = 0 := by
  by_contra hjh
  have hk := supported_monitor π (some k) (k+1) h hh ⟨j+1, by omega⟩
  have hj' := supported_monitor π (some j) (k+1) h hjh ⟨j+1, by omega⟩
  simp only [monitorAt_succ] at hk hj'
  have hkj : (some k : World) ≠ some j := by simp only [ne_eq, Option.some.injEq]; omega
  simp only [monitorLabel, hkj, ↓reduceIte] at hk
  simp only [monitorLabel, ↓reduceIte] at hj'
  rw [hk] at hj'
  exact absurd hj' (by decide)

theorem mem_tailSet_some (k j : ℕ) : (some j : World) ∈ waitingQueryTailSet (k+1) ↔ k ≤ j := by
  unfold waitingQueryTailSet
  constructor
  · rintro ⟨i, hi, hlt⟩
    simp only [Option.some.injEq] at hi
    omega
  · intro hj
    exact ⟨j, rfl, by omega⟩

theorem none_notMem_tailSet (k : ℕ) : (none : World) ∉ waitingQueryTailSet (k+1) := by
  simp [waitingQueryTailSet]

/-- On a record compatible with a pulse at tick `k`, earlier pulse worlds have
zero likelihood, every later finite world has the pulse-`k` likelihood, and the
never-pulse world has it too unless the startup inspection excluded it. -/
theorem monitor_likelihood_shape (π : ValidCausalPolicy Action Observation) (k : ℕ)
    (h : Trace (k+1)) (hh : record π (k+1) (some k) h ≠ 0) :
    (fun θ => record π (k+1) θ h) =
      (fun θ => (waitingQueryTailSet (k+1)).indicator
        (fun _ => record π (k+1) (some k) h) θ +
        ({none} : Set World).indicator
          (fun _ => if (h 0).1 = inspect then 0 else record π (k+1) (some k) h) θ) := by
  funext θ
  cases θ with
  | none =>
    simp only [Set.indicator_of_notMem (none_notMem_tailSet k), zero_add,
      Set.indicator_of_mem (show none ∈ ({none} : Set World) by simp)]
    by_cases hi : (h 0).1 = inspect
    · rw [if_pos hi]
      by_contra hnone
      have hp := supported_inspection_bit π.1 (some k) k h hh hi
      have hn := supported_inspection_bit π.1 none k h hnone hi
      rw [hp] at hn
      simp at hn
    · rw [if_neg hi]
      apply row_eq_on_monitor_equivalent π.1 k _ h (fun hb => (hi hb).elim)
      intro j hj
      have hjk : j ≠ k := by omega
      simp only [reduceCtorEq, false_iff, Option.some.injEq]
      omega
  | some j =>
    simp only [Set.indicator_of_notMem (show some j ∉ ({none} : Set World) by simp), add_zero]
    by_cases hj : k ≤ j
    · rw [Set.indicator_of_mem ((mem_tailSet_some k j).mpr hj)]
      apply row_eq_on_monitor_equivalent (θ := some j) (η := some k) π.1 k _ h (fun _ => rfl)
      intro i hi
      simp only [Option.some.injEq]
      omega
    · rw [Set.indicator_of_notMem (mt (mem_tailSet_some k j).mp hj)]
      exact past_pulse_row_zero π.1 k j (by omega) h hh

theorem finiteTail_mass (k : ℕ) :
    prior.real (waitingQueryTailSet (k+1)) = 2 * alarmMass k := by
  change waitingQueryTail prior (k+1) = _
  rw [waitingQueryGeometric_tail _ (by omega)]
  unfold alarmMass
  rw [show k+2 = (k+1)+1 by omega, pow_succ]
  ring

/-- Exact Bayes normalizer of every record with positive pulse-`k` likelihood. -/
theorem monitor_predictive_mass (π : ValidCausalPolicy Action Observation) (k : ℕ)
    (h : Trace (k+1)) (hh : record π (k+1) (some k) h ≠ 0) :
    mass π (k+1) h = record π (k+1) (some k) h *
      (if (h 0).1 = inspect then 2 * alarmMass k else silentMass k) := by
  unfold mass priorSignalMass
  rw [monitor_likelihood_shape π k h hh]
  rw [integral_add ((integrable_const _).indicator (show MeasurableSet
      (waitingQueryTailSet (k+1)) from trivial))
    ((integrable_const _).indicator (measurableSet_singleton _))]
  rw [integral_indicator_const _ (show MeasurableSet (waitingQueryTailSet (k+1)) from trivial),
    integral_indicator_const _ (measurableSet_singleton _), finiteTail_mass,
    waitingQueryGeometricPrior_none]
  simp only [smul_eq_mul]
  by_cases hi : (h 0).1 = inspect <;> simp [hi, silentMass_eq] <;> ring

end IdExp.PairedAlarm.Predictive
