import Formal.AlarmPanelNativeSufficiency
import Formal.PulseMixture

/-! Every finite alarm-panel history has exact deficiency `(1-s)/2` to
the startup inspection bit, where `s` is its root inspection probability.
The lower bound permits arbitrary later history-dependent randomization. -/

noncomputable section
namespace IdExp.AlarmPanel
open Finset

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

 theorem rootInspection_mass (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (θ : World) (n : ℕ) :
    (∑ h : CausalFiniteTrace Action Observation (n+1),
      if (h 0).1 = inspect then experiment π (n+1) θ h else 0) = inspectionProbability π := by
  have he := firstExpectation π hπ θ n (fun ao => if ao.1 = inspect then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at he
  rw [he, Fintype.sum_prod_type]
  simp only [response_root]
  simp [inspectionProbability, inspect, Fin.sum_univ_succ, pairDist,
    uniformDist, Bool.apply_cond]
  cases θ <;> simp [pairDist, Fin.sum_univ_succ] <;> ring

 theorem response_late_eq (n : ℕ) (h : History) (h0 : 0 < h.length)
    (hn : h.length ≤ n) (a : Action) : response (some n) h a = response none h a := by
  have hz : h ≠ [] := by intro hh; simp [hh] at h0
  funext o
  simp only [response, if_neg hz]
  split
  · rfl
  · have hk : n ≠ (h.length-2)/2 := by omega
    simp [monitorLabel, hk]

 theorem traceProbFrom_late_eq (π : CausalPolicy Action Observation) (n : ℕ)
    (pre rest : History) (hp : 0 < pre.length) (hl : pre.length+rest.length ≤ n+1) :
    causalTraceProbFrom π (response (some n)) pre rest =
      causalTraceProbFrom π (response none) pre rest := by
  induction rest generalizing pre with
  | nil => rfl
  | cons ao rest ih =>
    simp only [causalTraceProbFrom]
    rw [response_late_eq n pre hp (by simp only [List.length_cons] at hl; omega)]
    rw [ih (pre ++ [ao]) (by simp) (by simp only [List.length_append,
      List.length_singleton, List.length_cons, List.length_nil] at *; omega)]

 theorem late_row_eq_on_no_inspection (π : CausalPolicy Action Observation)
    (n : ℕ) (h : CausalFiniteTrace Action Observation (n+1)) (hi : (h 0).1 ≠ inspect) :
    experiment π (n+1) (some (n+1)) h = experiment π (n+1) none h := by
  change causalTraceProb π (response (some (n+1))) (List.ofFn h) =
    causalTraceProb π (response none) (List.ofFn h)
  rw [causalTraceProb, causalTraceProb, List.ofFn_succ]
  simp only [causalTraceProbFrom, response_root, if_neg hi]
  rw [traceProbFrom_late_eq π (n+1) _ _ (by simp) (by simp; omega)]

 def bitTarget : FiniteExperiment World Bool := diracExp Option.isSome

 def rootBitDecoder (n : ℕ) (h : CausalFiniteTrace Action Observation (n+1)) (b : Bool) : ℝ :=
   if (h 0).1 = inspect then (if b = decide (2 ≤ (h 0).2.val) then 1 else 0) else 1/2

 theorem rootBitDecoder_valid (n : ℕ) : rootBitDecoder n ∈ stochasticRules _ _ := by
  intro h _
  constructor
  · intro b; unfold rootBitDecoder; split_ifs <;> norm_num
  · by_cases hh : (h 0).1 = inspect
    · simp [rootBitDecoder, hh]
    · simp [rootBitDecoder, hh]

 theorem rootBitDecoder_correct_mass (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (θ : World) (n : ℕ) :
    finiteDecisionLaw (experiment π (n+1)) (rootBitDecoder n) θ θ.isSome =
      (1 + inspectionProbability π)/2 := by
  have he := firstExpectation π hπ θ n (fun ao =>
    if ao.1 = inspect then (if θ.isSome = decide (2 ≤ ao.2.val) then 1 else 0) else 1/2)
  change (∑ h, experiment π (n+1) θ h *
    (if (h 0).1 = inspect then (if θ.isSome = decide (2 ≤ (h 0).2.val) then 1 else 0) else 1/2)) = _
  rw [he, Fintype.sum_prod_type]
  have hp := (hπ []).2
  norm_num [Fin.sum_univ_succ] at hp
  cases θ <;> norm_num [response_root, pairDist, uniformDist, inspect,
    inspectionProbability, Fin.sum_univ_succ] <;> linarith

 theorem bit_deficiency_le (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (n : ℕ) : finiteDeficiency (experiment π (n+1)) bitTarget ≤ (1-inspectionProbability π)/2 := by
  apply finiteDeficiency_le_of_decoder _ _ (rootBitDecoder n) (rootBitDecoder_valid n)
  intro θ
  rw [bitTarget, decodeErr_to_diracExp _ (experiment_valid π hπ _) _ _ (rootBitDecoder_valid n),
    rootBitDecoder_correct_mass π hπ θ n]
  linarith

 theorem bit_deficiency_ge (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (n : ℕ) : (1-inspectionProbability π)/2 ≤ finiteDeficiency (experiment π (n+1)) bitTarget := by
  apply le_csInf (finiteDeficiencyCandidates_nonempty_of_valid _ _
    (experiment_valid π hπ _) (diracExp_valid _))
  rintro c ⟨G,hG,herr⟩
  have hn := herr none
  have hk := herr (some (n+1))
  rw [decodeErr_to_diracExp _ (experiment_valid π hπ _) _ _ hG] at hn hk
  have hbound : finiteDecisionLaw (experiment π (n+1)) G none false +
      finiteDecisionLaw (experiment π (n+1)) G (some (n+1)) true ≤
      1 + inspectionProbability π := by
    unfold finiteDecisionLaw
    rw [← Finset.sum_add_distrib]
    calc
      _ ≤ ∑ h : CausalFiniteTrace Action Observation (n+1),
        (experiment π (n+1) none h +
          (if (h 0).1 = inspect then experiment π (n+1) (some (n+1)) h else 0)) := by
        apply Finset.sum_le_sum
        intro h _
        have h0 := (experiment_valid π hπ (n+1) none).1 h
        have h1 := (experiment_valid π hπ (n+1) (some (n+1))).1 h
        by_cases hi : (h 0).1 = inspect
        · rw [if_pos hi]
          have hg0 := stochasticRules_le_one hG h false
          have hg1 := stochasticRules_le_one hG h true
          nlinarith
        · rw [if_neg hi, late_row_eq_on_no_inspection π n h hi]
          have hg := stochasticRules_add_le_one hG h (Bool.false_ne_true)
          nlinarith
      _ = _ := by rw [Finset.sum_add_distrib, (experiment_valid π hπ _ none).2,
        rootInspection_mass π hπ (some (n+1)) n]
  simp only [Option.isSome_none, Option.isSome_some] at hn hk
  linarith

 theorem bit_deficiency_exact (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (n : ℕ) : finiteDeficiency (experiment π (n+1)) bitTarget = (1-inspectionProbability π)/2 :=
  le_antisymm (bit_deficiency_le π hπ n) (bit_deficiency_ge π hπ n)


 def coloredRoot (b : Bool) (h : CausalFiniteTrace Action Observation 1) : ℝ :=
   if (h 0).1 = inspect then pairDist b (h 0).2 else 0

 theorem coloredRoot_eq_experiment (θ : World) :
    coloredRoot θ.isSome = experiment inspectPolicy 1 θ := by
  funext h
  simp only [experiment, causalFiniteExperiment, causalTraceProb, List.ofFn_succ,
    List.ofFn_zero, causalTraceProbFrom, mul_one, response_root, inspectPolicy, detPolicy]
  by_cases hi : (h 0).1 = inspect <;> simp [coloredRoot, hi]

 theorem coloredRoot_valid : coloredRoot ∈ stochasticRules _ _ := by
  intro b _
  cases b with
  | false => exact (coloredRoot_eq_experiment none) ▸ experiment_valid inspectPolicy inspectPolicy_valid 1 none
  | true => exact (coloredRoot_eq_experiment (some 0)) ▸ experiment_valid inspectPolicy inspectPolicy_valid 1 (some 0)

 theorem root_from_bit : FiniteBlackwellLE (experiment inspectPolicy 1) bitTarget := by
  refine ⟨coloredRoot, coloredRoot_valid, ?_⟩
  funext θ h
  rw [bitTarget, finiteDecisionLaw_diracExp]
  exact congrFun (coloredRoot_eq_experiment θ) h

 theorem bit_from_root : FiniteBlackwellLE bitTarget (experiment inspectPolicy 1) := by
  refine ⟨rootBitDecoder 0, rootBitDecoder_valid 0, ?_⟩
  funext θ b
  have he := firstExpectation inspectPolicy inspectPolicy_valid θ 0 (fun ao =>
    if ao.1 = inspect then (if b = decide (2 ≤ ao.2.val) then 1 else 0) else 1/2)
  change (∑ h, experiment inspectPolicy 1 θ h *
    (if (h 0).1 = inspect then (if b = decide (2 ≤ (h 0).2.val) then 1 else 0) else 1/2)) = _
  rw [he, Fintype.sum_prod_type]
  cases θ <;> cases b <;> norm_num [response_root, pairDist, uniformDist, inspect,
    inspectPolicy, detPolicy, bitTarget, diracExp, Fin.sum_univ_succ]

/-- Exact deficiency to the literal one-step inspection experiment, with
its action and random color retained. -/
 theorem inspection_deficiency_exact (π : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (n : ℕ) :
    finiteDeficiency (experiment π (n+1)) (experiment inspectPolicy 1) =
      (1-inspectionProbability π)/2 := by
  rw [finiteDeficiency_eq_of_target_blackwellEquiv _ _ bitTarget
    (experiment_valid π hπ _) (experiment_valid inspectPolicy inspectPolicy_valid 1)
    (diracExp_valid _) root_from_bit bit_from_root]
  exact bit_deficiency_exact π hπ n

/-- Two worlds agree on the monitor coordinates appearing before `n`. -/
 def MonitorEquivalent (n : ℕ) (θ η : World) : Prop :=
   ∀ k, 2*k+2 < n → (θ = some k ↔ η = some k)

 theorem response_eq_of_monitors (n : ℕ) {θ η : World}
    (he : MonitorEquivalent n θ η) (h : History) (hh : 0 < h.length)
    (hn : h.length < n) (a : Action) : response θ h a = response η h a := by
  have hz : h ≠ [] := by intro hh'; simp [hh'] at hh
  funext o
  simp only [response, if_neg hz]
  split
  · rfl
  · rename_i hp
    have hidx : 2*((h.length-2)/2)+2 < n := by omega
    simp only [monitorLabel, he _ hidx]

 theorem traceProbFrom_eq_of_monitors (π : CausalPolicy Action Observation)
    (n : ℕ) {θ η : World} (he : MonitorEquivalent n θ η)
    (pre rest : History) (hp : 0 < pre.length) (hl : pre.length+rest.length ≤ n) :
    causalTraceProbFrom π (response θ) pre rest = causalTraceProbFrom π (response η) pre rest := by
  induction rest generalizing pre with
  | nil => rfl
  | cons ao rest ih =>
    simp only [causalTraceProbFrom]
    rw [response_eq_of_monitors n he pre hp (by simp only [List.length_cons] at hl; omega)]
    rw [ih (pre ++ [ao]) (by simp) (by simp only [List.length_append,
      List.length_singleton, List.length_cons, List.length_nil] at *; omega)]

 theorem no_inspection_rows_eq (π : CausalPolicy Action Observation)
    (hs : inspectionProbability π = 0) (n : ℕ) {θ η : World}
    (he : MonitorEquivalent n θ η) : experiment π n θ = experiment π n η := by
  funext h
  cases n with
  | zero => simp [experiment, causalFiniteExperiment, causalTraceProb, causalTraceProbFrom]
  | succ n =>
    change causalTraceProb π (response θ) (List.ofFn h) = causalTraceProb π (response η) (List.ofFn h)
    rw [causalTraceProb, causalTraceProb, List.ofFn_succ]
    simp only [causalTraceProbFrom, response_root]
    by_cases hi : (h 0).1 = inspect
    · simp [hi, inspectionProbability] at hs ⊢
      rw [hs]
      simp
    · simp only [if_neg hi]
      rw [traceProbFrom_eq_of_monitors π (n+1) he _ _ (by simp) (by simp; omega)]


 theorem row_eq_on_monitor_equivalent (π : CausalPolicy Action Observation)
    (n : ℕ) {θ η : World} (he : MonitorEquivalent (n+1) θ η)
    (h : CausalFiniteTrace Action Observation (n+1))
    (hb : (h 0).1 = inspect → θ.isSome = η.isSome) :
    experiment π (n+1) θ h = experiment π (n+1) η h := by
  change causalTraceProb π (response θ) (List.ofFn h) = causalTraceProb π (response η) (List.ofFn h)
  rw [causalTraceProb, causalTraceProb, List.ofFn_succ]
  simp only [causalTraceProbFrom, response_root]
  have hr : (if (h 0).1 = inspect then pairDist θ.isSome (h 0).2 else uniformDist (h 0).2) =
      (if (h 0).1 = inspect then pairDist η.isSome (h 0).2 else uniformDist (h 0).2) := by
    by_cases hi : (h 0).1 = inspect
    · rw [if_pos hi, if_pos hi, hb hi]
    · rw [if_neg hi, if_neg hi]
  rw [hr, traceProbFrom_eq_of_monitors π (n+1) he _ _ (by simp) (by simp; omega)]

 theorem past_pulse_row_zero (π : CausalPolicy Action Observation) (k j : ℕ) (hj : j < k)
    (h : CausalFiniteTrace Action Observation (2*k+2))
    (hh : experiment π (2*k+2) (some k) h ≠ 0) :
    experiment π (2*k+2) (some j) h = 0 := by
  by_contra hjh
  have hkobs := supported_monitor π (some k) (2*k+2) j (by omega) h hh
  have hjobs := supported_monitor π (some j) (2*k+2) j (by omega) h hjh
  have hkj : k ≠ j := by omega
  simp only [monitorLabel, Option.some.injEq, if_neg hkj] at hkobs
  simp only [monitorLabel, ↓reduceIte] at hjobs
  have : (0 : Observation) = 1 := hkobs.symm.trans hjobs
  norm_num at this

end IdExp.AlarmPanel
