import Formal.PairedAlarmNativeExtraction

/-!
# Same-horizon garblings on the paired alarm (local native facts for R5)

Small native facts needed by the finite-horizon posterior comparisons, proved
directly on the paired `response`; no alternating-interface theorem is
used.

* On a policy whose startup action is inspection with probability one, every
  supported record of length `n+1` determines the pulse QUERY record of the same
  length: the startup display's high bit is `θ.isSome`, and every later monitor
  coordinate is the literal waiting-query bit. A world's experiment at horizon
  `n+1`, under any policy, depends only on that QUERY record. Hence any such
  policy's record simulates every policy's record at the same horizon
  (`fullInspection_blackwell`).
* If the startup inspection probability is `s < 1`, the inspection record at
  horizon `n+1` is not a garbling of the policy's record of the same length:
  it would reveal the startup bit `θ.isSome` exactly, while the late world
  `some n` (pulse at trace position `n+1`, after the horizon) and `none` have
  identical records on every non-inspecting branch, of total mass `1-s`.

All declarations are in `IdExp.PairedAlarm.Information`.
-/

noncomputable section
namespace IdExp.PairedAlarm.Information
open Finset

/-- Inspect at the startup and at every later history. -/
def inspectPolicy : CausalPolicy Action Observation := detPolicy (fun _ => inspect)

theorem inspectPolicy_valid : IsCausalPolicy inspectPolicy := isCausalPolicy_detPolicy _

@[simp] theorem inspectPolicy_inspectionProbability :
    inspectionProbability inspectPolicy = 1 := by
  simp [inspectionProbability, inspectPolicy, detPolicy]

/-- With startup inspection probability one, the other startup actions are null. -/
theorem root_null_of_inspectionProbability_one (π : CausalPolicy Action Observation)
    (hπ : IsCausalPolicy π) (hs : inspectionProbability π = 1) (a : Action)
    (ha : a ≠ inspect) : π [] a = 0 := by
  have hsum := (hπ []).2
  have h0 := (hπ []).1 (0 : Action)
  have h1 := (hπ []).1 (1 : Action)
  have h2 := (hπ []).1 (2 : Action)
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hsum
  change π [] 0 = 1 at hs
  fin_cases a
  · exact absurd rfl ha
  · change π [] 1 = 0
    norm_num at hsum
    linarith
  · change π [] 2 = 0
    norm_num at hsum
    linarith

/-- Supported records of an always-inspecting startup begin with inspection. -/
theorem supported_root_inspect (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (hs : inspectionProbability π = 1) (θ : World) (n : ℕ)
    (h : CausalFiniteTrace Action Observation (n+1))
    (hh : experiment π (n+1) θ h ≠ 0) : (h 0).1 = inspect := by
  by_contra hne
  apply hh
  change causalTraceProb π (response θ) (List.ofFn h) = 0
  rw [causalTraceProb, List.ofFn_succ]
  simp only [causalTraceProbFrom]
  rw [root_null_of_inspectionProbability_one π hπ hs _ hne]
  ring

/-- On an inspected supported record, the startup display's high bit is the
world's startup bit `θ.isSome`. -/
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

/-- Read the pulse QUERY record off a paired record: the startup display's
high bit at position zero and the monitor coordinate afterwards. -/
def extractQuery (t : ℕ) (h : CausalFiniteTrace Action Observation t) :
    CausalFiniteTrace Bool Bool t := fun i =>
  if i.val = 0 then (true, decide (2 ≤ (h i).2.1.val))
  else (false, decide ((h i).2.2 = 1))

/-- An always-inspecting record of length `n+1` contains the pulse QUERY record
of the same length. -/
theorem extractQuery_supported (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (hs : inspectionProbability π = 1) (θ : World) (n : ℕ)
    (h : CausalFiniteTrace Action Observation (n+1))
    (hh : experiment π (n+1) θ h ≠ 0) :
    extractQuery (n+1) h = pulseTrace true (n+1) θ := by
  funext i
  by_cases hi : i.val = 0
  · have hi0 : i = 0 := Fin.ext hi
    subst hi0
    have hroot := supported_root_inspect π hπ hs θ n h hh
    simp only [extractQuery, pulseTrace, Fin.val_zero, if_true, Bool.true_and,
      supported_inspection_bit π θ n h hh hroot]
  · simp only [extractQuery, pulseTrace, hi, if_false, supported_monitor π θ (n+1) h hh i]
    congr 1
    cases hb : waitingQueryBit θ i.val
    · have hne : monitorAt θ i.val ≠ 1 := fun he =>
        absurd ((monitorAt_eq_one_iff θ i.val).1 he) (by simp [hb])
      simp [hne]
    · simp [(monitorAt_eq_one_iff θ i.val).2 hb]

/-- Worlds with the same QUERY record of length `t` have the same response rows
at every history shorter than `t`, for every proposed action. -/
theorem response_eq_of_queryTrace_eq {t : ℕ} {θ η : World}
    (he : pulseTrace true t θ = pulseTrace true t η)
    (h : History) (hh : h.length < t) (a : Action) :
    response θ h a = response η h a := by
  have ho := congrArg (fun x : CausalFiniteTrace Bool Bool t => (x ⟨h.length, hh⟩).2) he
  funext o
  by_cases hz : h = []
  · subst hz
    simp only [pulseTrace, List.length_nil, if_true, Bool.true_and] at ho
    simp [response_root, rootDisplay, ho]
  · have hl : h.length ≠ 0 := by simpa using hz
    simp only [pulseTrace, hl, if_false] at ho
    rw [response_tick θ h a o hz, response_tick η h a o hz]
    have hm : monitorLabel θ (h.length - 1) = monitorLabel η (h.length - 1) := by
      rw [← monitorAt_succ, ← monitorAt_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hl)]
      simp [monitorAt, ho]
    rw [hm]

/-- Finite causal execution only uses response rows before its horizon. -/
theorem traceProbFrom_congr_before (π : CausalPolicy Action Observation)
    (Q R : CausalResponse Action Observation) (n : ℕ)
    (hQR : ∀ h : History, h.length < n → ∀ a, Q h a = R h a)
    (pre rest : History) (hlen : pre.length + rest.length ≤ n) :
    causalTraceProbFrom π Q pre rest = causalTraceProbFrom π R pre rest := by
  induction rest generalizing pre with
  | nil => rfl
  | cons ao rest ih =>
    simp only [causalTraceProbFrom]
    rw [hQR pre (by simp only [List.length_cons] at hlen; omega) ao.1]
    have hl' : (pre ++ [ao]).length + rest.length ≤ n := by
      simp only [List.length_append, List.length_cons, List.length_nil] at *; omega
    rw [ih (pre ++ [ao]) hl']

/-- Every policy's experiment at horizon `t` depends on the world only through
its QUERY record of length `t`. -/
theorem experiment_eq_of_queryTrace_eq {t : ℕ} {θ η : World}
    (he : pulseTrace true t θ = pulseTrace true t η) (ρ : CausalPolicy Action Observation) :
    experiment ρ t θ = experiment ρ t η := by
  funext w
  exact traceProbFrom_congr_before ρ (response θ) (response η) t
    (fun h hh a => response_eq_of_queryTrace_eq he h hh a) [] (List.ofFn w) (by simp)

/-- A world with a prescribed QUERY record, if one exists. -/
def queryRepresentative (t : ℕ) (x : CausalFiniteTrace Bool Bool t) : World := by
  classical
  exact if hx : ∃ θ, pulseTrace true t θ = x then Classical.choose hx else none

theorem queryRepresentative_trace (t : ℕ) (θ : World) :
    pulseTrace true t (queryRepresentative t (pulseTrace true t θ)) = pulseTrace true t θ := by
  classical
  have hex : ∃ η, pulseTrace true t η = pulseTrace true t θ := ⟨θ, rfl⟩
  simp only [queryRepresentative, dif_pos hex]
  exact Classical.choose_spec hex

/-- Replay the requested policy in any world with the extracted QUERY record. -/
def inspectionReplay (ρ : CausalPolicy Action Observation) (t : ℕ)
    (h : CausalFiniteTrace Action Observation t) :
    CausalFiniteTrace Action Observation t → ℝ :=
  experiment ρ t (queryRepresentative t (extractQuery t h))

theorem inspectionReplay_valid (ρ : CausalPolicy Action Observation)
    (hρ : IsCausalPolicy ρ) (t : ℕ) : inspectionReplay ρ t ∈ stochasticRules _ _ := by
  intro h _
  exact experiment_valid ρ hρ t _

theorem inspectionReplay_law (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (hs : inspectionProbability π = 1) (ρ : CausalPolicy Action Observation) (n : ℕ) :
    finiteDecisionLaw (experiment π (n+1)) (inspectionReplay ρ (n+1)) = experiment ρ (n+1) := by
  funext θ u
  unfold finiteDecisionLaw
  have he : ∀ h, experiment π (n+1) θ h * inspectionReplay ρ (n+1) h u =
      experiment π (n+1) θ h * experiment ρ (n+1) θ u := by
    intro h
    by_cases hh : experiment π (n+1) θ h = 0
    · simp [hh]
    · unfold inspectionReplay
      rw [extractQuery_supported π hπ hs θ n h hh,
        experiment_eq_of_queryTrace_eq (queryRepresentative_trace (n+1) θ) ρ]
  simp_rw [he]
  rw [← Finset.sum_mul, (experiment_valid π hπ (n+1) θ).2, one_mul]

/-- A policy that inspects at startup with probability one simulates every
policy's record at the same positive horizon. -/
theorem fullInspection_blackwell (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (hs : inspectionProbability π = 1) (ρ : CausalPolicy Action Observation)
    (hρ : IsCausalPolicy ρ) (n : ℕ) :
    FiniteBlackwellLE (experiment ρ (n+1)) (experiment π (n+1)) :=
  ⟨inspectionReplay ρ (n+1), inspectionReplay_valid ρ hρ (n+1),
    inspectionReplay_law π hπ hs ρ n⟩

/-- Inspection simulates every policy at the same positive horizon. -/
theorem inspection_same_horizon_blackwell (ρ : CausalPolicy Action Observation)
    (hρ : IsCausalPolicy ρ) (n : ℕ) :
    FiniteBlackwellLE (experiment ρ (n+1)) (experiment inspectPolicy (n+1)) :=
  fullInspection_blackwell inspectPolicy inspectPolicy_valid
    inspectPolicy_inspectionProbability ρ hρ n

/-- Every `s = 1` policy simulates inspection at the same positive horizon. -/
theorem alwaysInspect_blackwell (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (hs : inspectionProbability π = 1) (n : ℕ) :
    FiniteBlackwellLE (experiment inspectPolicy (n+1)) (experiment π (n+1)) :=
  fullInspection_blackwell π hπ hs inspectPolicy inspectPolicy_valid n

/-! ## No reverse garbling when `s < 1` -/

/-- Expectations of a function of the first action-observation pair. -/
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

/-- The inspecting branch has probability `s` in every world. -/
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
    split_ifs with ha
    · rw [← Finset.mul_sum, (response_valid θ [] a).2, mul_one]
    · simp
  simp only [hrow, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

/-- The late world `some n` agrees with `none` at every nonempty history of
length at most `n`: its pulse is reported at trace position `n+1`. -/
theorem response_late_eq (n : ℕ) (h : History) (hz : h ≠ []) (hn : h.length ≤ n)
    (a : Action) : response (some n) h a = response none h a := by
  funext o
  rw [response_tick _ h a o hz, response_tick _ h a o hz]
  have hpos : 0 < h.length := List.length_pos_iff.mpr hz
  have hk : n ≠ h.length - 1 := by omega
  simp [monitorLabel, hk]

theorem traceProbFrom_late_eq (π : CausalPolicy Action Observation) (n : ℕ)
    (pre rest : History) (hp : pre ≠ []) (hl : pre.length + rest.length ≤ n + 1) :
    causalTraceProbFrom π (response (some n)) pre rest =
      causalTraceProbFrom π (response none) pre rest := by
  induction rest generalizing pre with
  | nil => rfl
  | cons ao rest ih =>
    simp only [causalTraceProbFrom]
    rw [response_late_eq n pre hp (by simp only [List.length_cons] at hl; omega)]
    have hl' : (pre ++ [ao]).length + rest.length ≤ n + 1 := by
      simp only [List.length_append, List.length_cons, List.length_nil] at *; omega
    rw [ih (pre ++ [ao]) (by simp) hl']

/-- Off the inspecting branch, the records of `none` and `some n` coincide up to
horizon `n+1`, under every policy. -/
theorem late_row_eq_on_no_inspection (π : CausalPolicy Action Observation) (n : ℕ)
    (h : CausalFiniteTrace Action Observation (n+1)) (hi : (h 0).1 ≠ inspect) :
    experiment π (n+1) (some n) h = experiment π (n+1) none h := by
  change causalTraceProb π (response (some n)) (List.ofFn h) =
    causalTraceProb π (response none) (List.ofFn h)
  rw [causalTraceProb, causalTraceProb, List.ofFn_succ]
  simp only [causalTraceProbFrom, response_root, rootDisplay, if_neg hi]
  congr 1
  apply traceProbFrom_late_eq π n _ _ (by simp)
  simp only [List.nil_append, List.length_singleton, List.length_ofFn]
  omega

/-- The exact startup bit `θ.isSome`. -/
def bitTarget : FiniteExperiment World Bool := diracExp Option.isSome

/-- No record of an `s < 1` policy is as informative as the startup bit. -/
theorem bit_not_garbling (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (n : ℕ) (hs : inspectionProbability π < 1) :
    ¬ FiniteBlackwellLE bitTarget (experiment π (n+1)) := by
  rintro ⟨G, hG, hlaw⟩
  have hn := congrFun (congrFun hlaw none) false
  have hk := congrFun (congrFun hlaw (some n)) true
  have hbound : finiteDecisionLaw (experiment π (n+1)) G none false +
      finiteDecisionLaw (experiment π (n+1)) G (some n) true ≤
      1 + inspectionProbability π := by
    unfold finiteDecisionLaw
    rw [← Finset.sum_add_distrib]
    calc
      _ ≤ ∑ h : CausalFiniteTrace Action Observation (n+1),
        (experiment π (n+1) none h +
          (if (h 0).1 = inspect then experiment π (n+1) (some n) h else 0)) := by
        apply Finset.sum_le_sum
        intro h _
        have h0 := (experiment_valid π hπ (n+1) none).1 h
        have h1 := (experiment_valid π hπ (n+1) (some n)).1 h
        have hg0 := stochasticRules_le_one hG h false
        have hg1 := stochasticRules_le_one hG h true
        have hp0 := (hG h (Set.mem_univ h)).1 false
        have hp1 := (hG h (Set.mem_univ h)).1 true
        by_cases hi : (h 0).1 = inspect
        · rw [if_pos hi]
          nlinarith
        · rw [if_neg hi, late_row_eq_on_no_inspection π n h hi]
          have hg := stochasticRules_add_le_one hG h (Bool.false_ne_true)
          nlinarith
      _ = _ := by rw [Finset.sum_add_distrib, (experiment_valid π hπ _ none).2,
        rootInspection_mass π hπ (some n) n]
  rw [hn, hk] at hbound
  simp [bitTarget, diracExp] at hbound
  linarith

/-- Read the startup bit from the startup display. -/
def rootBitRule (n : ℕ) (h : CausalFiniteTrace Action Observation (n+1)) (b : Bool) : ℝ :=
  if b = decide (2 ≤ (h 0).2.1.val) then 1 else 0

theorem rootBitRule_valid (n : ℕ) : rootBitRule n ∈ stochasticRules _ _ := by
  intro h _
  constructor
  · intro b; unfold rootBitRule; split_ifs <;> norm_num
  · simp [rootBitRule]

/-- Inspection's record of every positive length reveals the startup bit. -/
theorem bit_from_inspection (n : ℕ) :
    FiniteBlackwellLE bitTarget (experiment inspectPolicy (n+1)) := by
  refine ⟨rootBitRule n, rootBitRule_valid n, ?_⟩
  funext θ b
  unfold finiteDecisionLaw
  have he : ∀ h, experiment inspectPolicy (n+1) θ h * rootBitRule n h b =
      experiment inspectPolicy (n+1) θ h * (if b = θ.isSome then 1 else 0) := by
    intro h
    by_cases hh : experiment inspectPolicy (n+1) θ h = 0
    · simp [hh]
    · have hi := supported_root_inspect inspectPolicy inspectPolicy_valid
        inspectPolicy_inspectionProbability θ n h hh
      unfold rootBitRule
      rw [supported_inspection_bit inspectPolicy θ n h hh hi]
  simp_rw [he]
  rw [← Finset.sum_mul, (experiment_valid inspectPolicy inspectPolicy_valid (n+1) θ).2, one_mul]
  simp [bitTarget, diracExp]

/-- If `s < 1`, the policy's record does not simulate inspection's record of
the same positive length. -/
theorem no_reverse_of_inspectionProbability_lt_one
    (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (n : ℕ) (hs : inspectionProbability π < 1) :
    ¬ FiniteBlackwellLE (experiment inspectPolicy (n+1)) (experiment π (n+1)) := fun hr =>
  bit_not_garbling π hπ n hs (finiteBlackwellLE_trans (bit_from_inspection n) hr)

end IdExp.PairedAlarm.Information
