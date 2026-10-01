import Formal.AlarmPanelVariant
import Formal.AlarmPanelNativeAudit

/-!
# Native audit of the intervention variants

For every valid variant (panel retained or not, any color probability), every
randomized history-dependent policy with startup inspection probability `s`
has deficiency `(1-s)/2` to the actual one-step inspection record at every
positive horizon, the depth-`m` native audit has the same value whenever
`1 ≤ m ≤ t`, inspection is natively sufficient, and sufficiency holds iff `s = 1`.
The decoder and lower-bound arguments are those of the original interface:
the panel rows are world-independent in every variant, and the color law is
known randomness the decoder regenerates.
-/

noncomputable section
namespace IdExp.AlarmPanel
open Finset

variable (v : Variant)

/-! ## Support lemmas -/

theorem traceV_response_ne_zero (π : CausalPolicy Action Observation) (θ : World)
    (h : History) (hh : causalTraceProb π (responseV v θ) h ≠ 0) (i : Fin h.length) :
    responseV v θ (h.take i.val) (h[i.val]).1 (h[i.val]).2 ≠ 0 := by
  have hprod : causalTraceProb π (responseV v θ) (h.take i.val) *
      causalTraceProbFrom π (responseV v θ) (h.take i.val) (h.drop i.val) ≠ 0 := by
    rwa [← causalTraceProb_append, List.take_append_drop]
  have htail := (mul_ne_zero_iff.mp hprod).2
  rw [List.drop_eq_getElem_cons i.isLt] at htail
  exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp htail).1).2

theorem experimentV_response_ne_zero (π : CausalPolicy Action Observation)
    (θ : World) (t : ℕ) (h : CausalFiniteTrace Action Observation t)
    (hh : experimentV v π t θ h ≠ 0) (i : Fin t) :
    responseV v θ ((List.ofFn h).take i.val) (h i).1 (h i).2 ≠ 0 := by
  have he := traceV_response_ne_zero v π θ (List.ofFn h) hh
    ⟨i.val, by simpa using i.isLt⟩
  simpa using he

theorem supportedV_monitor (π : CausalPolicy Action Observation)
    (θ : World) (t k : ℕ) (hk : 2*k+2 < t)
    (h : CausalFiniteTrace Action Observation t) (hh : experimentV v π t θ h ≠ 0) :
    (h ⟨2*k+2,hk⟩).2 = monitorLabel θ k := by
  have he := experimentV_response_ne_zero v π θ t h hh ⟨2*k+2,hk⟩
  have hlen : ((List.ofFn h).take (2*k+2)).length = 2*k+2 := by
    simp only [List.length_take, List.length_ofFn]
    omega
  have hn : (List.ofFn h).take (2*k+2) ≠ [] := by
    intro hz; rw [hz] at hlen; simp at hlen
  have hp : ((List.ofFn h).take (2*k+2)).length % 2 ≠ 1 := by omega
  rw [responseV_monitor v θ _ _ _ hn hp] at he
  have hidx : (((List.ofFn h).take (2*k+2)).length - 2) / 2 = k := by omega
  rw [hidx] at he
  simpa [pointDist] using he

theorem supportedV_inspection_bit (π : CausalPolicy Action Observation) (θ : World)
    (n : ℕ) (h : CausalFiniteTrace Action Observation (n+1))
    (hh : experimentV v π (n+1) θ h ≠ 0) (hi : (h 0).1 = inspect) :
    decide (2 ≤ (h 0).2.val) = θ.isSome := by
  have he := experimentV_response_ne_zero v π θ (n+1) h hh 0
  simp only [Fin.val_zero, List.take_zero, responseV_root, hi, ↓reduceIte] at he
  have ho := (h 0).2.isLt
  cases hb : θ.isSome <;>
    simp only [hb, pairDistP, Bool.false_eq_true, ↓reduceIte] at he ⊢
  · have hq : (h 0).2.val / 2 = 0 := by by_contra hq; simp [hq] at he
    have hq' : ¬2 ≤ (h 0).2.val := by omega
    simp [hq']
  · have hq : (h 0).2.val / 2 = 1 := by by_contra hq; simp [hq] at he
    have hq' : 2 ≤ (h 0).2.val := by omega
    simp [hq']

/-! ## Root mass and the lower bound -/

theorem firstExpectationV (hv : v.Valid) (π : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (θ : World) (n : ℕ) (f : Action × Observation → ℝ) :
    (∑ h : CausalFiniteTrace Action Observation (n+1), experimentV v π (n+1) θ h * f (h 0)) =
    ∑ ao : Action × Observation, π [] ao.1 * responseV v θ [] ao.1 ao.2 * f ao := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Action × Observation)).sum_comp]
  rw [Fintype.sum_prod_type]
  have hc (ao : Action × Observation) (rest : CausalFiniteTrace Action Observation n) :
      (Fin.consEquiv (fun _ : Fin (n+1) => Action × Observation)) (ao,rest) =
        Fin.cons ao rest := by funext i; exact Fin.consEquiv_apply _ _ i
  simp_rw [hc]
  change (∑ ao, ∑ rest : CausalFiniteTrace Action Observation n,
    causalTraceProb π (responseV v θ) (List.ofFn (Fin.cons ao rest)) * f ao) = _
  simp only [causalTraceProb, List.ofFn_cons, causalTraceProbFrom]
  have he (ao : Action × Observation) :
      (∑ rest : CausalFiniteTrace Action Observation n,
        π [] ao.1 * responseV v θ [] ao.1 ao.2 *
          causalTraceProbFrom π (responseV v θ) ([] ++ [ao]) (List.ofFn rest) * f ao) =
        π [] ao.1 * responseV v θ [] ao.1 ao.2 * f ao := by
    calc
      _ = (π [] ao.1 * responseV v θ [] ao.1 ao.2 * f ao) *
          ∑ rest : CausalFiniteTrace Action Observation n,
            causalTraceProbFrom π (responseV v θ) [ao] (List.ofFn rest) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro rest _; simp only [List.nil_append]; ring
      _ = _ := by
        rw [sum_causalTraceProbFrom π hπ (responseV v θ) (responseV_valid v hv θ)]; ring
  exact Finset.sum_congr rfl (fun ao _ => he ao)

theorem rootInspectionV_mass (hv : v.Valid) (π : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (θ : World) (n : ℕ) :
    (∑ h : CausalFiniteTrace Action Observation (n+1),
      if (h 0).1 = inspect then experimentV v π (n+1) θ h else 0) = inspectionProbability π := by
  have he := firstExpectationV v hv π hπ θ n (fun ao => if ao.1 = inspect then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at he
  rw [he, Fintype.sum_prod_type]
  have hin : ∀ a : Action, (∑ o : Observation,
      if a = inspect then π [] a * responseV v θ [] a o else 0) =
      if a = inspect then π [] a else 0 := by
    intro a
    by_cases ha : a = inspect
    · simp only [ha, eq_self_iff_true, if_true, responseV_root, ← Finset.mul_sum,
        pairDistP_sum, mul_one]
    · simp [ha]
  simp_rw [hin]
  simp [inspectionProbability]

theorem responseV_late_eq (n : ℕ) (h : History) (h0 : 0 < h.length)
    (hn : h.length ≤ n) (a : Action) : responseV v (some n) h a = responseV v none h a := by
  have hz : h ≠ [] := by intro hh; simp [hh] at h0
  funext o
  simp only [responseV, if_neg hz]
  split
  · rfl
  · have hk : n ≠ (h.length-2)/2 := by omega
    simp [monitorLabel, hk]

theorem traceProbFromV_late_eq (π : CausalPolicy Action Observation) (n : ℕ)
    (pre rest : History) (hp : 0 < pre.length) (hl : pre.length+rest.length ≤ n+1) :
    causalTraceProbFrom π (responseV v (some n)) pre rest =
      causalTraceProbFrom π (responseV v none) pre rest := by
  induction rest generalizing pre with
  | nil => rfl
  | cons ao rest ih =>
    simp only [causalTraceProbFrom]
    rw [responseV_late_eq v n pre hp (by simp only [List.length_cons] at hl; omega)]
    rw [ih (pre ++ [ao]) (by simp) (by simp only [List.length_append,
      List.length_singleton, List.length_cons, List.length_nil] at *; omega)]

theorem late_rowV_eq_on_no_inspection (π : CausalPolicy Action Observation)
    (n : ℕ) (h : CausalFiniteTrace Action Observation (n+1)) (hi : (h 0).1 ≠ inspect) :
    experimentV v π (n+1) (some (n+1)) h = experimentV v π (n+1) none h := by
  change causalTraceProb π (responseV v (some (n+1))) (List.ofFn h) =
    causalTraceProb π (responseV v none) (List.ofFn h)
  rw [causalTraceProb, causalTraceProb, List.ofFn_succ]
  simp only [causalTraceProbFrom, responseV_root, if_neg hi]
  rw [traceProbFromV_late_eq v π (n+1) _ _ (by simp) (by simp; omega)]

theorem rootBitDecoderV_correct_mass (hv : v.Valid) (π : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (θ : World) (n : ℕ) :
    finiteDecisionLaw (experimentV v π (n+1)) (rootBitDecoder n) θ θ.isSome =
      (1 + inspectionProbability π)/2 := by
  have he := firstExpectationV v hv π hπ θ n (fun ao =>
    if ao.1 = inspect then (if θ.isSome = decide (2 ≤ ao.2.val) then 1 else 0) else 1/2)
  change (∑ h, experimentV v π (n+1) θ h *
    (if (h 0).1 = inspect then (if θ.isSome = decide (2 ≤ (h 0).2.val) then 1 else 0) else 1/2)) = _
  rw [he, Fintype.sum_prod_type]
  have hp := (hπ []).2
  norm_num [Fin.sum_univ_succ] at hp
  cases θ <;> norm_num [responseV_root, pairDistP, startupDistP, colorMass, inspect,
    inspectionProbability, Fin.sum_univ_succ] <;> ring_nf <;> linarith

theorem bit_deficiencyV_le (hv : v.Valid) (π : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (n : ℕ) :
    finiteDeficiency (experimentV v π (n+1)) bitTarget ≤ (1-inspectionProbability π)/2 := by
  apply finiteDeficiency_le_of_decoder _ _ (rootBitDecoder n) (rootBitDecoder_valid n)
  intro θ
  rw [bitTarget, decodeErr_to_diracExp _ (experimentV_valid v hv π hπ _) _ _ (rootBitDecoder_valid n),
    rootBitDecoderV_correct_mass v hv π hπ θ n]
  linarith

theorem bit_deficiencyV_ge (hv : v.Valid) (π : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (n : ℕ) :
    (1-inspectionProbability π)/2 ≤ finiteDeficiency (experimentV v π (n+1)) bitTarget := by
  apply le_csInf (finiteDeficiencyCandidates_nonempty_of_valid _ _
    (experimentV_valid v hv π hπ _) (diracExp_valid _))
  rintro c ⟨G,hG,herr⟩
  have hn := herr none
  have hk := herr (some (n+1))
  rw [decodeErr_to_diracExp _ (experimentV_valid v hv π hπ _) _ _ hG] at hn hk
  have hbound : finiteDecisionLaw (experimentV v π (n+1)) G none false +
      finiteDecisionLaw (experimentV v π (n+1)) G (some (n+1)) true ≤
      1 + inspectionProbability π := by
    unfold finiteDecisionLaw
    rw [← Finset.sum_add_distrib]
    calc
      _ ≤ ∑ h : CausalFiniteTrace Action Observation (n+1),
        (experimentV v π (n+1) none h +
          (if (h 0).1 = inspect then experimentV v π (n+1) (some (n+1)) h else 0)) := by
        apply Finset.sum_le_sum
        intro h _
        have h0 := (experimentV_valid v hv π hπ (n+1) none).1 h
        have h1 := (experimentV_valid v hv π hπ (n+1) (some (n+1))).1 h
        by_cases hi : (h 0).1 = inspect
        · rw [if_pos hi]
          have hg0 := stochasticRules_le_one hG h false
          have hg1 := stochasticRules_le_one hG h true
          nlinarith
        · rw [if_neg hi, late_rowV_eq_on_no_inspection v π n h hi]
          have hg := stochasticRules_add_le_one hG h (Bool.false_ne_true)
          nlinarith
      _ = _ := by rw [Finset.sum_add_distrib, (experimentV_valid v hv π hπ _ none).2,
        rootInspectionV_mass v hv π hπ (some (n+1)) n]
  simp only [Option.isSome_none, Option.isSome_some] at hn hk
  linarith

theorem bit_deficiencyV_exact (hv : v.Valid) (π : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (n : ℕ) :
    finiteDeficiency (experimentV v π (n+1)) bitTarget = (1-inspectionProbability π)/2 :=
  le_antisymm (bit_deficiencyV_le v hv π hπ n) (bit_deficiencyV_ge v hv π hπ n)

/-- The one-step inspection record of a variant: the bit with its known color. -/
def coloredRootP (p : ℝ) (b : Bool) (h : CausalFiniteTrace Action Observation 1) : ℝ :=
  if (h 0).1 = inspect then pairDistP p b (h 0).2 else 0

theorem coloredRootP_eq_experimentV (θ : World) :
    coloredRootP v.p θ.isSome = experimentV v inspectPolicy 1 θ := by
  funext h
  simp only [experimentV, causalFiniteExperiment, causalTraceProb, List.ofFn_succ,
    List.ofFn_zero, causalTraceProbFrom, mul_one, responseV_root, inspectPolicy, detPolicy]
  by_cases hi : (h 0).1 = inspect <;> simp [coloredRootP, hi]

theorem coloredRootP_valid (hv : v.Valid) : coloredRootP v.p ∈ stochasticRules _ _ := by
  intro b _
  cases b with
  | false => exact (coloredRootP_eq_experimentV v none) ▸
      experimentV_valid v hv inspectPolicy inspectPolicy_valid 1 none
  | true => exact (coloredRootP_eq_experimentV v (some 0)) ▸
      experimentV_valid v hv inspectPolicy inspectPolicy_valid 1 (some 0)

theorem root_from_bitV (hv : v.Valid) :
    FiniteBlackwellLE (experimentV v inspectPolicy 1) bitTarget := by
  refine ⟨coloredRootP v.p, coloredRootP_valid v hv, ?_⟩
  funext θ h
  rw [bitTarget, finiteDecisionLaw_diracExp]
  exact congrFun (coloredRootP_eq_experimentV v θ) h

theorem bit_from_rootV (hv : v.Valid) :
    FiniteBlackwellLE bitTarget (experimentV v inspectPolicy 1) := by
  refine ⟨rootBitDecoder 0, rootBitDecoder_valid 0, ?_⟩
  funext θ b
  have he := firstExpectationV v hv inspectPolicy inspectPolicy_valid θ 0 (fun ao =>
    if ao.1 = inspect then (if b = decide (2 ≤ ao.2.val) then 1 else 0) else 1/2)
  change (∑ h, experimentV v inspectPolicy 1 θ h *
    (if (h 0).1 = inspect then (if b = decide (2 ≤ (h 0).2.val) then 1 else 0) else 1/2)) = _
  rw [he, Fintype.sum_prod_type]
  cases θ <;> cases b <;> norm_num [responseV_root, pairDistP, startupDistP, colorMass, inspect,
    inspectPolicy, detPolicy, bitTarget, diracExp, Fin.sum_univ_succ]

/-- Exact deficiency to the literal one-step inspection experiment of the variant. -/
theorem inspection_deficiencyV_exact (hv : v.Valid) (π : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (n : ℕ) :
    finiteDeficiency (experimentV v π (n+1)) (experimentV v inspectPolicy 1) =
      (1-inspectionProbability π)/2 := by
  rw [finiteDeficiency_eq_of_target_blackwellEquiv _ _ bitTarget
    (experimentV_valid v hv π hπ _) (experimentV_valid v hv inspectPolicy inspectPolicy_valid 1)
    (diracExp_valid _) (root_from_bitV v hv) (bit_from_rootV v hv)]
  exact bit_deficiencyV_exact v hv π hπ n

theorem responseV_eq_of_monitors (n : ℕ) {θ η : World}
    (he : MonitorEquivalent n θ η) (h : History) (hh : 0 < h.length)
    (hn : h.length < n) (a : Action) : responseV v θ h a = responseV v η h a := by
  have hz : h ≠ [] := by intro hh'; simp [hh'] at hh
  funext o
  simp only [responseV, if_neg hz]
  split
  · rfl
  · have hidx : 2*((h.length-2)/2)+2 < n := by omega
    simp only [monitorLabel, he _ hidx]

/-! ## The sharp upper bound by world-independent replay -/

theorem supportedV_compatible (π : CausalPolicy Action Observation) (θ : World)
    (n : ℕ) (h : CausalFiniteTrace Action Observation (n+1))
    (hh : experimentV v π (n+1) θ h ≠ 0) : Compatible n h θ.isSome θ :=
  ⟨rfl, fun k hk => supportedV_monitor v π θ (n+1) k hk h hh⟩

theorem compatibleV_experiment_eq (n : ℕ) (h : CausalFiniteTrace Action Observation (n+1))
    (b : Bool) {θ η : World} (hθ : Compatible n h b θ) (hη : Compatible n h b η)
    (ρ : CausalPolicy Action Observation) (m : ℕ) (hm : m ≤ n+1) :
    experimentV v ρ m θ = experimentV v ρ m η := by
  have hb : θ.isSome = η.isSome := hθ.1.trans hη.1.symm
  have hmon : MonitorEquivalent (n+1) θ η := by
    intro k hk
    have he := (hθ.2 k hk).symm.trans (hη.2 k hk)
    by_cases hx : θ = some k <;> by_cases hy : η = some k <;>
      simp_all [monitorLabel]
  funext w
  apply traceProbFrom_congr_before ρ (responseV v θ) (responseV v η) m
  · intro pre hpre a
    by_cases hp : pre = []
    · subst pre; funext o; simp only [responseV_root, hb]
    · exact responseV_eq_of_monitors v (n+1) hmon pre
        (by have := List.length_pos_iff.mpr hp; exact this) (by omega) a
  · simp

def guessedReplayV (ρ : CausalPolicy Action Observation) (m n : ℕ)
    (h : CausalFiniteTrace Action Observation (n+1)) (b : Bool) :=
  experimentV v ρ m (compatibleWorld n h b)

def auditReplayV (ρ : CausalPolicy Action Observation) (m n : ℕ)
    (h : CausalFiniteTrace Action Observation (n+1))
    : CausalFiniteTrace Action Observation m → ℝ :=
  if (h 0).1 = inspect then guessedReplayV v ρ m n h (decide (2 ≤ (h 0).2.val))
  else fun u => (guessedReplayV v ρ m n h false u + guessedReplayV v ρ m n h true u)/2

theorem auditReplayV_valid (hv : v.Valid) (ρ : CausalPolicy Action Observation)
    (hρ : IsCausalPolicy ρ) (m n : ℕ) : auditReplayV v ρ m n ∈ stochasticRules _ _ := by
  intro h _
  by_cases hi : (h 0).1 = inspect
  · simpa only [auditReplayV, if_pos hi, guessedReplayV] using
      experimentV_valid v hv ρ hρ m (compatibleWorld n h (decide (2 ≤ (h 0).2.val)))
  · constructor
    · intro u
      simp only [auditReplayV, if_neg hi]
      exact div_nonneg (add_nonneg (experimentV_valid v hv ρ hρ m _ |>.1 u)
        (experimentV_valid v hv ρ hρ m _ |>.1 u)) (by norm_num)
    · simp only [auditReplayV, if_neg hi, ← Finset.sum_div, Finset.sum_add_distrib,
        guessedReplayV]
      rw [(experimentV_valid v hv ρ hρ m _).2, (experimentV_valid v hv ρ hρ m _).2]
      norm_num

theorem guessedReplayV_correct (π ρ : CausalPolicy Action Observation) (θ : World)
    (m n : ℕ) (hm : m ≤ n+1) (h : CausalFiniteTrace Action Observation (n+1))
    (hh : experimentV v π (n+1) θ h ≠ 0) :
    guessedReplayV v ρ m n h θ.isSome = experimentV v ρ m θ := by
  exact compatibleV_experiment_eq v n h θ.isSome
    (compatibleWorld_correct n h θ (supportedV_compatible v π θ n h hh))
    (supportedV_compatible v π θ n h hh) ρ m hm

theorem auditReplayV_row_bound (hv : v.Valid) (π ρ : CausalPolicy Action Observation)
    (hρ : IsCausalPolicy ρ) (θ : World) (m n : ℕ) (hm : m ≤ n+1)
    (h : CausalFiniteTrace Action Observation (n+1)) (hh : experimentV v π (n+1) θ h ≠ 0) :
    finiteTV (auditReplayV v ρ m n h) (experimentV v ρ m θ) ≤
      if (h 0).1 = inspect then 0 else 1/2 := by
  have hc := guessedReplayV_correct v π ρ θ m n hm h hh
  by_cases hi : (h 0).1 = inspect
  · simp only [auditReplayV, if_pos hi, supportedV_inspection_bit v π θ n h hh hi]
    rw [hc]
    simp [finiteTV]
  · simp only [auditReplayV, if_neg hi]
    cases hb : θ.isSome
    · rw [hb] at hc
      rw [hc]
      exact half_mixture_tv _ _ (experimentV_valid v hv ρ hρ m θ)
        (experimentV_valid v hv ρ hρ m _)
    · rw [hb] at hc
      rw [hc]
      have he : (fun u => (guessedReplayV v ρ m n h false u + experimentV v ρ m θ u)/2) =
          (fun u => (experimentV v ρ m θ u + guessedReplayV v ρ m n h false u)/2) := by
        funext u; ring
      rw [he]
      exact half_mixture_tv _ _ (experimentV_valid v hv ρ hρ m θ)
        (experimentV_valid v hv ρ hρ m _)

theorem auditReplayV_error_le (hv : v.Valid) (π ρ : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (hρ : IsCausalPolicy ρ) (m n : ℕ) (hm : m ≤ n+1) (θ : World) :
    decodeErr (experimentV v π (n+1)) (experimentV v ρ m) (auditReplayV v ρ m n) θ ≤
      (1-inspectionProbability π)/2 := by
  apply (PredictiveTransport.decodeErr_le_weighted_rowTV _ (experimentV_valid v hv π hπ _)
    _ _ θ).trans
  calc
    _ ≤ ∑ h : CausalFiniteTrace Action Observation (n+1),
        experimentV v π (n+1) θ h * (if (h 0).1 = inspect then 0 else 1/2) := by
      apply Finset.sum_le_sum
      intro h _
      by_cases hh : experimentV v π (n+1) θ h = 0
      · simp [hh]
      · exact mul_le_mul_of_nonneg_left (auditReplayV_row_bound v hv π ρ hρ θ m n hm h hh)
          ((experimentV_valid v hv π hπ _ θ).1 h)
    _ = _ := by
      have ht (h : CausalFiniteTrace Action Observation (n+1)) :
          experimentV v π (n+1) θ h * (if (h 0).1 = inspect then 0 else 1/2) =
          (experimentV v π (n+1) θ h -
            (if (h 0).1 = inspect then experimentV v π (n+1) θ h else 0))/2 := by
        split_ifs <;> ring
      simp_rw [ht]
      rw [← Finset.sum_div, Finset.sum_sub_distrib, (experimentV_valid v hv π hπ _ θ).2,
        rootInspectionV_mass v hv π hπ θ n]

theorem policy_deficiencyV_le (hv : v.Valid) (π ρ : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (hρ : IsCausalPolicy ρ) (m n : ℕ) (hm : m ≤ n+1) :
    finiteDeficiency (experimentV v π (n+1)) (experimentV v ρ m) ≤
      (1-inspectionProbability π)/2 :=
  finiteDeficiency_le_of_decoder _ _ (auditReplayV v ρ m n) (auditReplayV_valid v hv ρ hρ m n) _
    (auditReplayV_error_le v hv π ρ hπ hρ m n hm)

theorem alwaysInspectV_blackwell (hv : v.Valid) (π ρ : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (hρ : IsCausalPolicy ρ) (m n : ℕ) (hm : m ≤ n+1)
    (hs : inspectionProbability π = 1) :
    FiniteBlackwellLE (experimentV v ρ m) (experimentV v π (n+1)) := by
  refine ⟨auditReplayV v ρ m n, auditReplayV_valid v hv ρ hρ m n, ?_⟩
  funext θ u
  have he := auditReplayV_error_le v hv π ρ hπ hρ m n hm θ
  rw [hs] at he
  norm_num at he
  exact (decodeErr_eq_zero_iff _ _ _ θ).1
    (le_antisymm he (decodeErr_nonneg _ _ _ θ)) u

/-- The exact depth-`m` native audit of a variant, for `1 ≤ m ≤ n+1`. -/
theorem native_auditV_exact (hv : v.Valid) (π : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (m n : ℕ) (hm0 : 1 ≤ m) (hm : m ≤ n+1) :
    causalNativeDeficiencyUpTo (experimentV v π (n+1)) (responseV v) m =
      (1-inspectionProbability π)/2 := by
  apply le_antisymm
  · apply (causalNativeDeficiency_le_iff_all_policy _ (experimentV_valid v hv π hπ _)
      (responseV v) (responseV_valid v hv) m _).2
    intro ρ hρ t ht
    exact policy_deficiencyV_le v hv π ρ hπ hρ t n (by omega)
  · rw [← inspection_deficiencyV_exact v hv π hπ n]
    rw [causalNativeDeficiencyUpTo_eq_terminal _ (experimentV_valid v hv π hπ _)
      (responseV v) (responseV_valid v hv)]
    exact finiteDeficiency_causalPolicy_le_native_of_le _ (experimentV_valid v hv π hπ _)
      inspectPolicy inspectPolicy_valid (responseV v) (responseV_valid v hv) hm0

theorem sufficientV_iff_inspectionProbability_one (hv : v.Valid)
    (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π) :
    CausalNativelySufficient (responseV v) ⟨π,hπ⟩ ↔ inspectionProbability π = 1 := by
  rw [causalNativelySufficient_iff_finitarilyGreatest (responseV v) (responseV_valid v hv)]
  constructor
  · intro hg
    have hs := inspectionProbability_le_one π hπ
    by_contra hsne
    have hslt : inspectionProbability π < 1 := lt_of_le_of_ne hs hsne
    obtain ⟨T,hT⟩ := hg ⟨inspectPolicy,inspectPolicy_valid⟩ 1
      ((1-inspectionProbability π)/4) (by linarith)
    have hbad := hT (T+1) (by omega)
    change finiteDeficiency (experimentV v π (T+1)) (experimentV v inspectPolicy 1) < _ at hbad
    rw [inspection_deficiencyV_exact v hv π hπ T] at hbad
    linarith
  · intro hs ρ m ε hε
    refine ⟨max m 1, ?_⟩
    intro t ht
    cases t with
    | zero => omega
    | succ n =>
      have hb := policy_deficiencyV_le v hv π ρ.1 hπ ρ.2 m n (by omega)
      rw [hs] at hb
      norm_num at hb
      exact lt_of_le_of_lt hb hε

theorem inspection_nativelyV_sufficient (hv : v.Valid) :
    CausalNativelySufficient (responseV v) ⟨inspectPolicy,inspectPolicy_valid⟩ :=
  (sufficientV_iff_inspectionProbability_one v hv inspectPolicy inspectPolicy_valid).2
    inspectPolicy_inspectionProbability

theorem inspectionV_finitarily_greatest (hv : v.Valid) :
    CausalFinitarilyGreatest (responseV v) ⟨inspectPolicy,inspectPolicy_valid⟩ :=
  (causalNativelySufficient_iff_finitarilyGreatest (responseV v) (responseV_valid v hv) _).1
    (inspection_nativelyV_sufficient v hv)

/-- Every non-inspecting root mixture is strictly finitarily dominated by
inspection in every valid variant. -/
theorem inspectionV_strictly_dominates (hv : v.Valid) (π : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (hs : inspectionProbability π < 1) :
    CausalFinitaryDominates (responseV v) ⟨inspectPolicy,inspectPolicy_valid⟩ ⟨π,hπ⟩ ∧
      ¬ CausalFinitaryDominates (responseV v) ⟨π,hπ⟩ ⟨inspectPolicy,inspectPolicy_valid⟩ := by
  refine ⟨inspectionV_finitarily_greatest v hv ⟨π,hπ⟩, ?_⟩
  intro hd
  obtain ⟨T,hT⟩ := hd 1 ((1-inspectionProbability π)/4) (by linarith)
  have hbad := hT (T+1) (by omega)
  change finiteDeficiency (experimentV v π (T+1)) (experimentV v inspectPolicy 1) < _ at hbad
  rw [inspection_deficiencyV_exact v hv π hπ T] at hbad
  linarith

/-- Inspection simulates every policy at the same positive horizon. -/
theorem inspection_same_horizonV_deficiency_zero (hv : v.Valid)
    (ρ : CausalPolicy Action Observation) (hρ : IsCausalPolicy ρ) (n : ℕ) :
    finiteDeficiency (experimentV v inspectPolicy (n+1)) (experimentV v ρ (n+1)) = 0 := by
  apply le_antisymm
  · have hb := policy_deficiencyV_le v hv inspectPolicy ρ inspectPolicy_valid hρ (n+1) n le_rfl
    simpa using hb
  · exact finiteDeficiency_nonneg_of_valid _ _
      (experimentV_valid v hv inspectPolicy inspectPolicy_valid _) (experimentV_valid v hv ρ hρ _)

/-! ## The two named interventions -/

/-- Panel retained after inspection: the native audit is unchanged. -/
theorem retained_native_audit_exact (π : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (m n : ℕ) (hm0 : 1 ≤ m) (hm : m ≤ n+1) :
    causalNativeDeficiencyUpTo (experimentV Variant.retained π (n+1))
      (responseV Variant.retained) m = (1-inspectionProbability π)/2 :=
  native_auditV_exact Variant.retained Variant.retained_valid π hπ m n hm0 hm

theorem retained_sufficient_iff (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π) :
    CausalNativelySufficient (responseV Variant.retained) ⟨π,hπ⟩ ↔
      inspectionProbability π = 1 :=
  sufficientV_iff_inspectionProbability_one Variant.retained Variant.retained_valid π hπ

/-- Known color bias: the native audit is unchanged for every color probability. -/
theorem colored_native_audit_exact (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π) (m n : ℕ)
    (hm0 : 1 ≤ m) (hm : m ≤ n+1) :
    causalNativeDeficiencyUpTo (experimentV (Variant.colored p) π (n+1))
      (responseV (Variant.colored p)) m = (1-inspectionProbability π)/2 :=
  native_auditV_exact (Variant.colored p) (Variant.colored_valid p h0 h1) π hπ m n hm0 hm

theorem colored_sufficient_iff (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π) :
    CausalNativelySufficient (responseV (Variant.colored p)) ⟨π,hπ⟩ ↔
      inspectionProbability π = 1 :=
  sufficientV_iff_inspectionProbability_one (Variant.colored p) (Variant.colored_valid p h0 h1) π hπ

/-- The original variant reproduces the original audit. -/
theorem original_native_audit_exact (π : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (m n : ℕ) (hm0 : 1 ≤ m) (hm : m ≤ n+1) :
    causalNativeDeficiencyUpTo (experiment π (n+1)) response m =
      (1-inspectionProbability π)/2 := by
  have h := native_auditV_exact Variant.original Variant.original_valid π hπ m n hm0 hm
  rwa [experimentV_original, responseV_original] at h

end IdExp.AlarmPanel
