import Formal.AlarmPanelVariance
import Formal.AlarmPanelVariantNative

/-!
# Actual posterior predictive-coordinate variance on the intervention variants

The complete summed posterior-coordinate variance of a variant `v` is the root
mixture `s * (1 - p + p^2) + (1 - s) * playTotal`, where `s` is the startup
inspection probability, `p` the color probability, and `playTotal` the same
monitor series as on the original interface. Panel retention does not change
the score (the panel is known randomness in either branch); a known color bias
rescales inspection's startup bonus from `1/4` to `(p^2 + (1-p)^2)/2`. Hence
inspection's value crosses the fixed play value: every maximizer skips
inspection when `1 - p + p^2 < playTotal`, every maximizer inspects when
`1 - p + p^2 > playTotal`, and all policies tie at equality. A nine-term partial
sum with the geometric tail bound encloses `playTotal` tightly enough to
classify each archived color bias; a fourteen-term sum encloses the exact
switch endpoints to five decimals.
-/

noncomputable section

namespace IdExp.AlarmPanel
open Finset

variable (v : Variant)

theorem traceProbFromV_eq_of_monitors (π : CausalPolicy Action Observation)
    (n : ℕ) {θ η : World} (he : MonitorEquivalent n θ η)
    (pre rest : History) (hp : 0 < pre.length) (hl : pre.length+rest.length ≤ n) :
    causalTraceProbFrom π (responseV v θ) pre rest =
      causalTraceProbFrom π (responseV v η) pre rest := by
  induction rest generalizing pre with
  | nil => rfl
  | cons ao rest ih =>
    simp only [causalTraceProbFrom]
    rw [responseV_eq_of_monitors v n he pre hp (by simp only [List.length_cons] at hl; omega)]
    rw [ih (pre ++ [ao]) (by simp) (by simp only [List.length_append,
      List.length_singleton, List.length_cons, List.length_nil] at *; omega)]

theorem rowV_eq_on_monitor_equivalent (π : CausalPolicy Action Observation)
    (n : ℕ) {θ η : World} (he : MonitorEquivalent (n+1) θ η)
    (h : CausalFiniteTrace Action Observation (n+1))
    (hb : (h 0).1 = inspect → θ.isSome = η.isSome) :
    experimentV v π (n+1) θ h = experimentV v π (n+1) η h := by
  change causalTraceProb π (responseV v θ) (List.ofFn h) =
    causalTraceProb π (responseV v η) (List.ofFn h)
  rw [causalTraceProb, causalTraceProb, List.ofFn_succ]
  simp only [causalTraceProbFrom, responseV_root]
  have hr : (if (h 0).1 = inspect then pairDistP v.p θ.isSome (h 0).2
      else startupDistP v.p (h 0).2) =
      (if (h 0).1 = inspect then pairDistP v.p η.isSome (h 0).2
      else startupDistP v.p (h 0).2) := by
    by_cases hi : (h 0).1 = inspect
    · rw [if_pos hi, if_pos hi, hb hi]
    · rw [if_neg hi, if_neg hi]
  rw [hr, traceProbFromV_eq_of_monitors v π (n+1) he _ _ (by simp) (by simp; omega)]

theorem past_pulseV_row_zero (π : CausalPolicy Action Observation) (k j : ℕ) (hj : j < k)
    (h : CausalFiniteTrace Action Observation (2*k+2))
    (hh : experimentV v π (2*k+2) (some k) h ≠ 0) :
    experimentV v π (2*k+2) (some j) h = 0 := by
  by_contra hjh
  have hkobs := supportedV_monitor v π (some k) (2*k+2) j (by omega) h hh
  have hjobs := supportedV_monitor v π (some j) (2*k+2) j (by omega) h hjh
  have hkj : k ≠ j := by omega
  simp only [monitorLabel, Option.some.injEq, if_neg hkj] at hkobs
  simp only [monitorLabel, ↓reduceIte] at hjobs
  have : (0 : Observation) = 1 := hkobs.symm.trans hjobs
  norm_num at this

/-- Root PLAY0 forever: a policy with startup inspection probability zero. -/
def playForeverPolicy : ValidCausalPolicy Action Observation := validDetPolicy fun _ => play0

@[simp] theorem playPolicy_root : inspectionProbability playForeverPolicy.1 = 0 := by
  simp [inspectionProbability, playForeverPolicy, validDetPolicy, detPolicy, inspect, play0]

end IdExp.AlarmPanel

namespace IdExp.AlarmPanelVariantVariance
open AlarmPanel MeasureTheory Finset Set Filter Topology
open AlarmPanelVariance (coordinateVariance coordinateVariance_constant coordinateVariance_monitor
  sum_observation alarmMass silentMass playTerm playTotal alarmMass_pos alarmMass_summable
  alarmMass_sum silentMass_eq silentMass_pos playTerm_summable playTerm_nonneg playTerm_bounds
  playTotal_gt playTotal_le_one late_finite_monitorEquivalent none_monitorEquivalent
  finiteTail_mass)

variable (v : Variant)

def posteriorMeasure (hv : v.Valid) (π : ValidCausalPolicy Action Observation) (t : ℕ)
    (h : CausalFiniteTrace Action Observation t) : Measure World :=
  have _ := hv
  priorPosteriorMeasure AlarmPanelPrior.prior (experimentV v π.1 t) h

instance posteriorMeasure_probability (hv : v.Valid) (π : ValidCausalPolicy Action Observation)
    (t : ℕ) (h : CausalFiniteTrace Action Observation t) :
    IsProbabilityMeasure (posteriorMeasure v hv π t h) :=
  priorPosteriorMeasure_probability AlarmPanelPrior.prior (experimentV v π.1 t)
    (experimentV_valid v hv π.1 π.2 t)
    (PulseBrierScore.likelihood_integrable _ (experimentV_valid v hv π.1 π.2 t)) h

def localVariance (hv : v.Valid) (π : ValidCausalPolicy Action Observation) (t : ℕ)
    (h : CausalFiniteTrace Action Observation t) (a : Action) : ℝ :=
  coordinateVariance (posteriorMeasure v hv π t h) (fun θ => responseV v θ (List.ofFn h) a)

def stageVariance (hv : v.Valid) (π : ValidCausalPolicy Action Observation) (t : ℕ) : ℝ :=
  ∑ h : CausalFiniteTrace Action Observation t,
    priorSignalMass AlarmPanelPrior.prior (experimentV v π.1 t) h *
      ∑ a : Action, π.1 (List.ofFn h) a * localVariance v hv π t h a

def objective (hv : v.Valid) (π : ValidCausalPolicy Action Observation) : ℝ :=
  ∑' t, stageVariance v hv π t

theorem localVariance_panel (hv : v.Valid) (π : ValidCausalPolicy Action Observation) (k : ℕ)
    (h : CausalFiniteTrace Action Observation (2*k+1)) (a : Action) :
    localVariance v hv π (2*k+1) h a = 0 := by
  have hp : (List.ofFn h).length % 2 = 1 := by simp only [List.length_ofFn]; omega
  have he : (fun θ => responseV v θ (List.ofFn h) a) = (fun _ =>
      if inspected (List.ofFn h) ∧ v.retain = false then pointDist 0
      else pairDistP v.p (a == play1)) := by
    funext θ o; simpa only [ite_apply] using responseV_panel v θ _ a o hp
  rw [localVariance, he]
  exact coordinateVariance_constant _ _

theorem localVariance_monitor (hv : v.Valid) (π : ValidCausalPolicy Action Observation) (k : ℕ)
    (h : CausalFiniteTrace Action Observation (2*k+2)) (a : Action) :
    localVariance v hv π (2*k+2) h a =
      2 * (posteriorMeasure v hv π (2*k+2) h).real {some k} *
        (1 - (posteriorMeasure v hv π (2*k+2) h).real {some k}) := by
  have hn : List.ofFn h ≠ [] := by simp
  have hp : (List.ofFn h).length % 2 ≠ 1 := by simp only [List.length_ofFn]; omega
  have hk : ((List.ofFn h).length - 2)/2 = k := by simp only [List.length_ofFn]; omega
  have he : (fun θ => responseV v θ (List.ofFn h) a) =
      (fun θ => pointDist (monitorLabel θ k)) := by
    funext θ o; rw [responseV_monitor v θ _ a o hn hp, hk]
  rw [localVariance, he]
  exact coordinateVariance_monitor _ _

theorem stageVariance_panel (hv : v.Valid) (π : ValidCausalPolicy Action Observation) (k : ℕ) :
    stageVariance v hv π (2*k+1) = 0 := by simp [stageVariance, localVariance_panel]

@[simp] theorem posteriorMeasure_root (hv : v.Valid) (π : ValidCausalPolicy Action Observation)
    (h : CausalFiniteTrace Action Observation 0) :
    posteriorMeasure v hv π 0 h = AlarmPanelPrior.prior := by
  have he (θ : World) : experimentV v π.1 0 θ h = 1 := by
    simp [experimentV, causalFiniteExperiment, causalTraceProb, causalTraceProbFrom, List.ofFn_zero]
  simp [posteriorMeasure, priorPosteriorMeasure, priorSignalDensity, priorSignalMass, he]

/-- Inspection's startup bonus: the bit split into colors of masses `p` and `1-p`. -/
def inspectRoot (p : ℝ) : ℝ := (p^2 + (1-p)^2)/2

theorem coordinateVariance_root (a : Action) :
    coordinateVariance AlarmPanelPrior.prior (fun θ => responseV v θ [] a) =
      if a = inspect then inspectRoot v.p else 0 := by
  have hm (o : Observation) : (∫ θ, responseV v θ [] a o ∂AlarmPanelPrior.prior) =
      (1/2 : ℝ) * responseV v none [] a o + (1/2 : ℝ) * responseV v (some 0) [] a o :=
    AlarmPanelPrior.integral_none_some _ (by intro k; simp [responseV_root])
  have hs (o : Observation) : (∫ θ, (responseV v θ [] a o)^2 ∂AlarmPanelPrior.prior) =
      (1/2 : ℝ) * (responseV v none [] a o)^2 + (1/2 : ℝ) * (responseV v (some 0) [] a o)^2 :=
    AlarmPanelPrior.integral_none_some _ (by intro k; simp [responseV_root])
  simp only [coordinateVariance, hm, hs]
  by_cases hi : a = inspect
  · subst a
    norm_num [responseV_root, pairDistP, colorMass, inspectRoot, sum_observation] <;> ring
  · norm_num [responseV_root, hi, startupDistP, colorMass, sum_observation] <;> ring

theorem localVariance_root (hv : v.Valid) (π : ValidCausalPolicy Action Observation)
    (h : CausalFiniteTrace Action Observation 0) (a : Action) :
    localVariance v hv π 0 h a = if a = inspect then inspectRoot v.p else 0 := by
  simp only [localVariance, List.ofFn_zero, posteriorMeasure_root]
  exact coordinateVariance_root v a

theorem stageVariance_root (hv : v.Valid) (π : ValidCausalPolicy Action Observation) :
    stageVariance v hv π 0 = inspectionProbability π.1 * inspectRoot v.p := by
  have hm (h : CausalFiniteTrace Action Observation 0) :
      priorSignalMass AlarmPanelPrior.prior (experimentV v π.1 0) h = 1 := by
    simp [priorSignalMass, experimentV, causalFiniteExperiment, causalTraceProb,
      causalTraceProbFrom, List.ofFn_zero]
  simp [stageVariance, hm, localVariance_root, List.ofFn_zero, mul_ite, inspectionProbability]

theorem monitor_likelihood_shape (π : ValidCausalPolicy Action Observation) (k : ℕ)
    (h : CausalFiniteTrace Action Observation (2*k+2))
    (hh : experimentV v π.1 (2*k+2) (some k) h ≠ 0) :
    (fun θ => experimentV v π.1 (2*k+2) θ h) =
      (fun θ => (waitingQueryTailSet (k+1)).indicator
        (fun _ => experimentV v π.1 (2*k+2) (some k) h) θ +
        ({none} : Set World).indicator
          (fun _ => if (h 0).1 = inspect then 0 else experimentV v π.1 (2*k+2) (some k) h) θ) := by
  funext θ
  cases θ with
  | none =>
    have hn : none ∉ waitingQueryTailSet (k+1) := by simp [waitingQueryTailSet]
    simp only [Set.indicator_of_notMem hn, zero_add, mem_singleton_iff,
      Set.indicator_of_mem (show none ∈ ({none} : Set World) by simp)]
    by_cases hi : (h 0).1 = inspect
    · rw [if_pos hi]
      by_contra hnone
      have hp := supportedV_inspection_bit v π.1 (some k) (2*k+1) h hh hi
      have hn := supportedV_inspection_bit v π.1 none (2*k+1) h hnone hi
      rw [hp] at hn
      contradiction
    · rw [if_neg hi]
      exact rowV_eq_on_monitor_equivalent v π.1 (2*k+1) (none_monitorEquivalent k) h
        (fun hb => (hi hb).elim)
  | some j =>
    have hm : some j ∈ waitingQueryTailSet (k+1) ↔ k ≤ j := by
      simp only [waitingQueryTailSet, mem_setOf_eq, Option.some.injEq, exists_eq_left']
      omega
    simp only [Set.indicator_of_notMem (show some j ∉ ({none} : Set World) by simp), add_zero]
    by_cases hj : k ≤ j
    · rw [Set.indicator_of_mem (hm.mpr hj)]
      exact rowV_eq_on_monitor_equivalent v π.1 (2*k+1) (late_finite_monitorEquivalent k j hj) h
        (fun _ => rfl)
    · rw [Set.indicator_of_notMem (mt hm.mp hj)]
      exact past_pulseV_row_zero v π.1 k j (by omega) h hh

theorem monitor_predictive_mass (π : ValidCausalPolicy Action Observation) (k : ℕ)
    (h : CausalFiniteTrace Action Observation (2*k+2))
    (hh : experimentV v π.1 (2*k+2) (some k) h ≠ 0) :
    priorSignalMass AlarmPanelPrior.prior (experimentV v π.1 (2*k+2)) h =
      experimentV v π.1 (2*k+2) (some k) h *
        (if (h 0).1 = inspect then 2 * alarmMass k else silentMass k) := by
  unfold priorSignalMass
  rw [monitor_likelihood_shape v π k h hh]
  rw [integral_add ((integrable_const _).indicator (show MeasurableSet
      (waitingQueryTailSet (k+1)) from trivial))
    ((integrable_const _).indicator (measurableSet_singleton _))]
  rw [integral_indicator_const _ (show MeasurableSet (waitingQueryTailSet (k+1)) from trivial),
    integral_indicator_const _ (measurableSet_singleton _), finiteTail_mass,
    waitingQueryGeometricPrior_none]
  simp only [smul_eq_mul]
  by_cases hi : (h 0).1 = inspect <;> simp [hi, silentMass_eq] <;> ring

theorem posterior_monitor_atom (hv : v.Valid) (π : ValidCausalPolicy Action Observation) (k : ℕ)
    (h : CausalFiniteTrace Action Observation (2*k+2))
    (hm : priorSignalMass AlarmPanelPrior.prior (experimentV v π.1 (2*k+2)) h ≠ 0) :
    (posteriorMeasure v hv π (2*k+2) h).real {some k} =
      alarmMass k * experimentV v π.1 (2*k+2) (some k) h /
        priorSignalMass AlarmPanelPrior.prior (experimentV v π.1 (2*k+2)) h := by
  have hp := PulseBrierScore.posteriorReport_bayes (experimentV v π.1 (2*k+2))
    (experimentV_valid v hv π.1 π.2 _) h hm (some k)
  change (posteriorMeasure v hv π (2*k+2) h).real {some k} = _ at hp
  rw [waitingQueryGeometricPrior_some] at hp
  exact hp

theorem monitor_weightedVariance (hv : v.Valid) (π : ValidCausalPolicy Action Observation)
    (k : ℕ) (h : CausalFiniteTrace Action Observation (2*k+2)) (a : Action) :
    priorSignalMass AlarmPanelPrior.prior (experimentV v π.1 (2*k+2)) h *
        localVariance v hv π (2*k+2) h a =
      experimentV v π.1 (2*k+2) (some k) h *
        (if (h 0).1 = inspect then alarmMass k else AlarmPanelVariance.playTerm k) := by
  rw [localVariance_monitor]
  by_cases hr : experimentV v π.1 (2*k+2) (some k) h = 0
  · rw [hr, zero_mul]
    by_cases hm : priorSignalMass AlarmPanelPrior.prior (experimentV v π.1 (2*k+2)) h = 0
    · rw [hm, zero_mul]
    · rw [posterior_monitor_atom v hv π k h hm, hr]
      simp
  · have hmass := monitor_predictive_mass v π k h hr
    have ha := alarmMass_pos k
    have hs := silentMass_pos k
    have hm : priorSignalMass AlarmPanelPrior.prior (experimentV v π.1 (2*k+2)) h ≠ 0 := by
      rw [hmass]
      apply mul_ne_zero hr
      split <;> positivity
    rw [posterior_monitor_atom v hv π k h hm, hmass]
    by_cases hi : (h 0).1 = inspect
    · rw [if_pos hi, if_pos hi]
      field_simp [hr, ne_of_gt ha]
      ring
    · rw [if_neg hi, if_neg hi]
      unfold AlarmPanelVariance.playTerm
      field_simp [hr, ne_of_gt hs]

theorem stageVariance_monitor (hv : v.Valid) (π : ValidCausalPolicy Action Observation) (k : ℕ) :
    stageVariance v hv π (2*k+2) = inspectionProbability π.1 * alarmMass k +
      (1-inspectionProbability π.1) * playTerm k := by
  have he (h : CausalFiniteTrace Action Observation (2*k+2)) :
      priorSignalMass AlarmPanelPrior.prior (experimentV v π.1 (2*k+2)) h *
        (∑ a : Action, π.1 (List.ofFn h) a * localVariance v hv π (2*k+2) h a) =
      experimentV v π.1 (2*k+2) (some k) h *
        (if (h 0).1 = inspect then alarmMass k else playTerm k) := by
    simp only [mul_sum, mul_left_comm _ (π.1 (List.ofFn h) _), monitor_weightedVariance,
      ← sum_mul, (π.2 (List.ofFn h)).2, one_mul]
  simp only [stageVariance, he]
  have hd (h : CausalFiniteTrace Action Observation (2*k+2)) :
      experimentV v π.1 (2*k+2) (some k) h *
        (if (h 0).1 = inspect then alarmMass k else playTerm k) =
      (if (h 0).1 = inspect then experimentV v π.1 (2*k+2) (some k) h else 0) *
          (alarmMass k - playTerm k) + experimentV v π.1 (2*k+2) (some k) h * playTerm k := by
    split <;> ring
  simp_rw [hd]
  rw [sum_add_distrib, ← sum_mul, ← sum_mul,
    rootInspectionV_mass v hv π.1 π.2 (some k) (2*k+1),
    (experimentV_valid v hv π.1 π.2 _ (some k)).2]
  ring

theorem monitor_summable (hv : v.Valid) (π : ValidCausalPolicy Action Observation) :
    Summable (fun k => stageVariance v hv π (2*k+2)) := by
  simp_rw [stageVariance_monitor]
  exact (alarmMass_summable.mul_left _).add (playTerm_summable.mul_left _)

theorem stageVariance_summable (hv : v.Valid) (π : ValidCausalPolicy Action Observation) :
    Summable (stageVariance v hv π) := by
  apply (summable_nat_add_iff 1).1
  apply Summable.even_add_odd
  · simp only [stageVariance_panel]
    exact summable_zero
  · simpa only [Nat.add_assoc, show (1:ℕ)+1=2 by decide] using monitor_summable v hv π

/-- Inspection's complete variance return under a known color bias. -/
def inspectTotalP (p : ℝ) : ℝ := 1 - p + p^2

def mixtureP (p s : ℝ) : ℝ := s * inspectTotalP p + (1-s) * playTotal

/-- The complete actual posterior-coordinate objective of a variant is the
displayed root mixture, with the same play value as the original interface. -/
theorem objective_eq_mixture (hv : v.Valid) (π : ValidCausalPolicy Action Observation) :
    objective v hv π = mixtureP v.p (inspectionProbability π.1) := by
  have hz : Summable (fun k => stageVariance v hv π (2*k+1)) := by
    simp only [stageVariance_panel]; exact summable_zero
  have hm : Summable (fun k => stageVariance v hv π (2*k+1+1)) := by
    simpa only [Nat.add_assoc, show (1:ℕ)+1=2 by decide] using monitor_summable v hv π
  have he := @tsum_even_add_odd ℝ _ _ _ _ (fun n => stageVariance v hv π (n+1)) hz hm
  simp only [stageVariance_panel, tsum_zero, zero_add, Nat.add_assoc,
    show (1:ℕ)+1=2 by decide] at he
  have ht := (stageVariance_summable v hv π).sum_add_tsum_nat_add 1
  simp only [sum_range_one] at ht
  rw [← he, stageVariance_root] at ht
  simp_rw [stageVariance_monitor] at ht
  rw [Summable.tsum_add (alarmMass_summable.mul_left _) (playTerm_summable.mul_left _),
    tsum_mul_left, tsum_mul_left, alarmMass_sum] at ht
  unfold objective mixtureP inspectTotalP playTotal
  rw [← ht]
  unfold inspectRoot
  ring

/-! ## Classification of complete-variance maximizers -/

theorem maximizer_iff_of_lt (hv : v.Valid) (hlt : inspectTotalP v.p < playTotal)
    (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, objective v hv ρ ≤ objective v hv π) ↔ inspectionProbability π.1 = 0 := by
  have hs0 := inspectionProbability_nonneg π.1 π.2
  constructor
  · intro h
    have hh := h playForeverPolicy
    rw [objective_eq_mixture, objective_eq_mixture, playPolicy_root] at hh
    unfold mixtureP at hh
    nlinarith
  · intro h ρ
    rw [objective_eq_mixture, objective_eq_mixture, h]
    unfold mixtureP
    have := inspectionProbability_nonneg ρ.1 ρ.2
    nlinarith

theorem maximizer_iff_of_gt (hv : v.Valid) (hgt : playTotal < inspectTotalP v.p)
    (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, objective v hv ρ ≤ objective v hv π) ↔ inspectionProbability π.1 = 1 := by
  have hs1 := inspectionProbability_le_one π.1 π.2
  constructor
  · intro h
    have hh := h ⟨inspectPolicy, inspectPolicy_valid⟩
    rw [objective_eq_mixture, objective_eq_mixture, inspectPolicy_inspectionProbability] at hh
    unfold mixtureP at hh
    nlinarith
  · intro h ρ
    rw [objective_eq_mixture, objective_eq_mixture, h]
    unfold mixtureP
    have := inspectionProbability_le_one ρ.1 ρ.2
    nlinarith

theorem all_tie_of_eq (hv : v.Valid) (heq : inspectTotalP v.p = playTotal)
    (π ρ : ValidCausalPolicy Action Observation) : objective v hv π = objective v hv ρ := by
  rw [objective_eq_mixture, objective_eq_mixture]
  unfold mixtureP
  rw [heq]
  ring

/-- Panel retention leaves the complete variance objective unchanged: every
maximizer still skips inspection. -/
theorem retained_maximizer_iff (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, objective Variant.retained Variant.retained_valid ρ ≤
      objective Variant.retained Variant.retained_valid π) ↔ inspectionProbability π.1 = 0 := by
  apply maximizer_iff_of_lt
  have := playTotal_gt
  simp only [inspectTotalP, Variant.retained_p]
  norm_num
  linarith

/-! ## A certified enclosure of the play value -/

def partialPlay (N : ℕ) : ℝ := ∑ k ∈ Finset.range N, playTerm k

theorem partialPlay_le (N : ℕ) : partialPlay N ≤ playTotal :=
  playTerm_summable.sum_le_tsum (Finset.range N) (fun k _ => playTerm_nonneg k)

theorem tail_alarmMass (N : ℕ) : (∑' i, alarmMass (i+N)) = (1/2 : ℝ)^(N+1) := by
  have he : (fun i => alarmMass (i+N)) = fun i => (1/2 : ℝ)^i * (1/2)^(N+2) := by
    funext i; simp only [alarmMass, pow_add]; ring
  rw [he, tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  ring

theorem playTotal_le_partial (N : ℕ) : playTotal ≤ partialPlay N + (1/2 : ℝ)^N := by
  have hs := playTerm_summable.sum_add_tsum_nat_add N
  have hb : (∑' i, playTerm (i+N)) ≤ ∑' i, 2 * alarmMass (i+N) :=
    Summable.tsum_le_tsum (fun i => (playTerm_bounds (i+N)).2)
      ((summable_nat_add_iff N).2 playTerm_summable)
      ((summable_nat_add_iff N).2 (alarmMass_summable.mul_left 2))
  rw [tsum_mul_left, tail_alarmMass] at hb
  unfold playTotal partialPlay
  rw [← hs]
  have h2 : 2 * (1/2 : ℝ)^(N+1) = (1/2)^N := by rw [pow_succ]; ring
  linarith

theorem partialPlay_fourteen_gt : (81606 / 100000 : ℝ) < partialPlay 14 := by
  norm_num [partialPlay, Finset.sum_range_succ, AlarmPanelVariance.playTerm,
    AlarmPanelVariance.alarmMass, AlarmPanelVariance.silentMass]

theorem partialPlay_fourteen_lt : partialPlay 14 + (1/2 : ℝ)^14 < (81613 / 100000 : ℝ) := by
  norm_num [partialPlay, Finset.sum_range_succ, AlarmPanelVariance.playTerm,
    AlarmPanelVariance.alarmMass, AlarmPanelVariance.silentMass]

/-- `0.81606 < playTotal < 0.81613`; the archived decimal is `0.8161249…`. -/
theorem playTotal_bounds : (81606/100000 : ℝ) < playTotal ∧ playTotal < (81613/100000 : ℝ) :=
  ⟨partialPlay_fourteen_gt.trans_le (partialPlay_le 14),
    (playTotal_le_partial 14).trans_lt partialPlay_fourteen_lt⟩

/-! ## The exact switch -/

/-- Half-width of the color interval on which every variance maximizer skips inspection. -/
def switchRadius : ℝ := Real.sqrt (playTotal - 3/4)

theorem switchRadius_pos : 0 < switchRadius :=
  Real.sqrt_pos.2 (by linarith [playTotal_gt])

theorem switchRadius_sq : switchRadius ^ 2 = playTotal - 3/4 :=
  Real.sq_sqrt (by linarith [playTotal_gt])

/-- Inspection loses to play exactly when the color is within `switchRadius` of fair. -/
theorem inspectTotalP_lt_iff (p : ℝ) :
    inspectTotalP p < playTotal ↔ |p - 1/2| < switchRadius := by
  have hr := switchRadius_pos
  have hsq := switchRadius_sq
  rw [abs_lt]
  unfold inspectTotalP
  constructor
  · intro h; constructor <;> nlinarith
  · rintro ⟨h1, h2⟩; nlinarith

theorem inspectTotalP_gt_iff (p : ℝ) :
    playTotal < inspectTotalP p ↔ switchRadius < |p - 1/2| := by
  have hr := switchRadius_pos
  have hsq := switchRadius_sq
  unfold inspectTotalP
  constructor
  · intro h
    rw [lt_abs]
    by_cases hp : 1/2 ≤ p
    · left; nlinarith [abs_of_nonneg (sub_nonneg.2 hp)]
    · right; push_neg at hp; nlinarith
  · intro h
    have h2 : switchRadius ^ 2 < (p - 1/2) ^ 2 := by
      have := abs_nonneg (p - 1/2)
      nlinarith [sq_abs (p - 1/2)]
    nlinarith

/-- The switch endpoints `1/2 ∓ switchRadius` lie in `(0.24284, 0.24298)` and
`(0.75702, 0.75716)`; the archived decimals are `.242852…` and `.757147…`. -/
theorem switchRadius_bounds :
    (25702 / 100000 : ℝ) < switchRadius ∧ switchRadius < (25716 / 100000 : ℝ) := by
  have hb := playTotal_bounds
  have hsq := switchRadius_sq
  have hr := switchRadius_pos
  constructor <;> nlinarith

theorem switch_endpoints_bounds :
    (24284 / 100000 : ℝ) < 1/2 - switchRadius ∧ 1/2 - switchRadius < (24298 / 100000 : ℝ) ∧
    (75702 / 100000 : ℝ) < 1/2 + switchRadius ∧ 1/2 + switchRadius < (75716 / 100000 : ℝ) := by
  have h := switchRadius_bounds
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h.1, h.2]

theorem colored_maximizer_skips (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (hp : 1 - p + p^2 < 81606/100000) (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, objective (Variant.colored p) (Variant.colored_valid p h0 h1) ρ ≤
      objective (Variant.colored p) (Variant.colored_valid p h0 h1) π) ↔
      inspectionProbability π.1 = 0 := by
  apply maximizer_iff_of_lt
  simp only [inspectTotalP, Variant.colored_p]
  linarith [playTotal_bounds.1]

theorem colored_maximizer_inspects (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (hp : 81613/100000 < 1 - p + p^2) (π : ValidCausalPolicy Action Observation) :
    (∀ ρ, objective (Variant.colored p) (Variant.colored_valid p h0 h1) ρ ≤
      objective (Variant.colored p) (Variant.colored_valid p h0 h1) π) ↔
      inspectionProbability π.1 = 1 := by
  apply maximizer_iff_of_gt
  simp only [inspectTotalP, Variant.colored_p]
  linarith [playTotal_bounds.2]

/-- The seven archived color biases. -/
theorem archived_biases_skip (π : ValidCausalPolicy Action Observation) :
    ((∀ ρ, objective (Variant.colored (1/4)) (Variant.colored_valid _ (by norm_num) (by norm_num)) ρ ≤
      objective (Variant.colored (1/4)) (Variant.colored_valid _ (by norm_num) (by norm_num)) π) ↔
      inspectionProbability π.1 = 0) ∧
    ((∀ ρ, objective (Variant.colored (1/2)) (Variant.colored_valid _ (by norm_num) (by norm_num)) ρ ≤
      objective (Variant.colored (1/2)) (Variant.colored_valid _ (by norm_num) (by norm_num)) π) ↔
      inspectionProbability π.1 = 0) ∧
    ((∀ ρ, objective (Variant.colored (3/4)) (Variant.colored_valid _ (by norm_num) (by norm_num)) ρ ≤
      objective (Variant.colored (3/4)) (Variant.colored_valid _ (by norm_num) (by norm_num)) π) ↔
      inspectionProbability π.1 = 0) :=
  ⟨colored_maximizer_skips _ (by norm_num) (by norm_num) (by norm_num) π,
   colored_maximizer_skips _ (by norm_num) (by norm_num) (by norm_num) π,
   colored_maximizer_skips _ (by norm_num) (by norm_num) (by norm_num) π⟩

theorem archived_biases_inspect (π : ValidCausalPolicy Action Observation) :
    ((∀ ρ, objective (Variant.colored (1/100)) (Variant.colored_valid _ (by norm_num) (by norm_num)) ρ ≤
      objective (Variant.colored (1/100)) (Variant.colored_valid _ (by norm_num) (by norm_num)) π) ↔
      inspectionProbability π.1 = 1) ∧
    ((∀ ρ, objective (Variant.colored (1/10)) (Variant.colored_valid _ (by norm_num) (by norm_num)) ρ ≤
      objective (Variant.colored (1/10)) (Variant.colored_valid _ (by norm_num) (by norm_num)) π) ↔
      inspectionProbability π.1 = 1) ∧
    ((∀ ρ, objective (Variant.colored (9/10)) (Variant.colored_valid _ (by norm_num) (by norm_num)) ρ ≤
      objective (Variant.colored (9/10)) (Variant.colored_valid _ (by norm_num) (by norm_num)) π) ↔
      inspectionProbability π.1 = 1) ∧
    ((∀ ρ, objective (Variant.colored (99/100)) (Variant.colored_valid _ (by norm_num) (by norm_num)) ρ ≤
      objective (Variant.colored (99/100)) (Variant.colored_valid _ (by norm_num) (by norm_num)) π) ↔
      inspectionProbability π.1 = 1) :=
  ⟨colored_maximizer_inspects _ (by norm_num) (by norm_num) (by norm_num) π,
   colored_maximizer_inspects _ (by norm_num) (by norm_num) (by norm_num) π,
   colored_maximizer_inspects _ (by norm_num) (by norm_num) (by norm_num) π,
   colored_maximizer_inspects _ (by norm_num) (by norm_num) (by norm_num) π⟩

end IdExp.AlarmPanelVariantVariance
