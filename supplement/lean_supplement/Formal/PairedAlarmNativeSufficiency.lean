import Formal.PairedAlarmNativeExtraction

/-! Startup inspection is a sufficient policy on the literal stochastic
simultaneous alarm-panel interface. Every finite record of every competing
policy is an exact randomized garbling of the inspection record of the same
positive length.

Index convention: alarm tick `k` is the monitor coordinate `(h i).2.2` at trace
position `i = k+1`, and the startup inspection bit is read from the startup
display label `(h 0).2.1`. A record of length `n+1` therefore carries ticks
`0, …, n-1`, which are exactly the ticks read by the response rows of
histories of length at most `n`. Port of `Formal.AlarmPanelNativeSufficiency`;
no alternating-interface theorem is used. -/

noncomputable section
namespace IdExp.PairedAlarm
open Finset

def inspectPolicy : CausalPolicy Action Observation := detPolicy (fun _ => inspect)
theorem inspectPolicy_valid : IsCausalPolicy inspectPolicy := isCausalPolicy_detPolicy _

@[simp] theorem rootDisplay_inspect (θ : World) : rootDisplay θ inspect = pointDisplay (if θ.isSome then 2 else 0) := by
  simp [rootDisplay]

theorem rootDisplay_of_ne (θ : World) {a : Action} (ha : a ≠ inspect) :
    rootDisplay θ a = pointDisplay 0 := by
  simp [rootDisplay, ha]

theorem rootDisplay_apply (θ : World) (a : Action) (d : Display) :
    rootDisplay θ a d = if a = inspect then pointDisplay (if θ.isSome then 2 else 0) d else pointDisplay 0 d := by
  unfold rootDisplay; split <;> rfl

/-- A display label is possible for the fair color attached to `b` exactly when
its high bit is `b`. -/
theorem pairDist_ne_zero_iff (b : Bool) (d : Display) :
    pairDist b d ≠ 0 ↔ decide (2 ≤ d.val) = b := by
  fin_cases d <;> cases b <;> norm_num [pairDist]

/-- The startup bit and the first `n` alarm ticks. -/
def summary (n : ℕ) (θ : World) : Bool × (Fin n → Bool) :=
  (θ.isSome, fun k => decide (θ = some k.val))

/-- Read the startup bit from the startup display label and alarm tick `k`
from the monitor coordinate at trace position `k+1`. -/
def extractSummary (n : ℕ) (h : CausalFiniteTrace Action Observation (n+1)) :
    Bool × (Fin n → Bool) :=
  (decide (2 ≤ (h 0).2.1.val), fun k => decide ((h k.succ).2.2 = 1))

theorem inspect_supported_root (θ : World) (t : ℕ) (ht : 0 < t)
    (h : CausalFiniteTrace Action Observation t)
    (hh : experiment inspectPolicy t θ h ≠ 0) :
    (h ⟨0,ht⟩).1 = inspect ∧
      decide (2 ≤ (h ⟨0,ht⟩).2.1.val) = θ.isSome := by
  have he := experiment_response_ne_zero inspectPolicy θ t h hh ⟨0,ht⟩
  have hp : (h ⟨0,ht⟩).1 = inspect := by
    have hprob : causalTraceProb inspectPolicy (response θ) (List.ofFn h) ≠ 0 := hh
    cases t with
    | zero => omega
    | succ t =>
      rw [causalTraceProb, List.ofFn_succ] at hprob
      simp only [causalTraceProbFrom] at hprob
      have hpol := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hprob).1).1
      simpa [inspectPolicy, detPolicy] using hpol
  refine ⟨hp, ?_⟩
  simp only [List.take_zero, response_root, hp, rootDisplay_inspect] at he
  exact pointDisplay_highBit _ _ (left_ne_zero_of_mul he)

theorem extractSummary_supported (θ : World) (n : ℕ)
    (h : CausalFiniteTrace Action Observation (n+1))
    (hh : experiment inspectPolicy (n+1) θ h ≠ 0) :
    extractSummary n h = summary n θ := by
  apply Prod.ext
  · exact (inspect_supported_root θ (n+1) (by omega) h hh).2
  · funext k
    have hm := supported_monitor inspectPolicy θ (n+1) h hh k.succ
    change decide ((h k.succ).2.2 = 1) = decide (θ = some k.val)
    rw [hm, Fin.val_succ, monitorAt_succ]
    by_cases hk : θ = some k.val
    · simp [monitorLabel, hk]
    · simp [monitorLabel, hk]

/-- Rows of histories of length at most `n` read only the startup bit and the
first `n` alarm ticks. -/
theorem response_eq_of_summary_eq {n : ℕ} {θ η : World}
    (he : summary n θ = summary n η) (h : History) (hh : h.length < n+1) (a : Action) :
    response θ h a = response η h a := by
  funext o
  by_cases h0 : h = []
  · subst h0
    have hb : θ.isSome = η.isSome := congrArg Prod.fst he
    rw [response_root, response_root, rootDisplay, rootDisplay, hb]
  · rw [response_tick θ h a o h0, response_tick η h a o h0]
    have hlen : 0 < h.length := List.length_pos_iff.mpr h0
    have hk : h.length - 1 < n := by omega
    have hbit := congrFun (congrArg Prod.snd he) ⟨h.length - 1, hk⟩
    have hiff : (θ = some (h.length - 1)) ↔ (η = some (h.length - 1)) := by
      simpa only [summary, decide_eq_decide] using hbit
    simp only [monitorLabel, hiff]

/-- Finite causal execution only uses rows before its horizon. -/
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
    rw [ih (pre ++ [ao]) (by simp only [List.length_append, List.length_cons,
      List.length_nil] at *; omega)]

theorem experiment_eq_of_summary_eq {n : ℕ} {θ η : World}
    (he : summary n θ = summary n η) (π : CausalPolicy Action Observation) :
    experiment π (n+1) θ = experiment π (n+1) η := by
  funext h
  exact traceProbFrom_congr_before π (response θ) (response η) (n+1)
    (fun h hh a => response_eq_of_summary_eq he h hh a) [] (List.ofFn h) (by simp)

def summaryRepresentative (n : ℕ) (s : Bool × (Fin n → Bool)) : World := by
  classical
  exact if hs : ∃ θ, summary n θ = s then Classical.choose hs else none

theorem summaryRepresentative_summary (n : ℕ) (θ : World) :
    summary n (summaryRepresentative n (summary n θ)) = summary n θ := by
  classical
  have hex : ∃ η, summary n η = summary n θ := ⟨θ,rfl⟩
  simp only [summaryRepresentative, dif_pos hex]
  exact Classical.choose_spec hex

/-- Simulate the requested policy using any world compatible with the
finite extracted statistic. The chosen world may depend on target depth. -/
def inspectionReplay (ρ : CausalPolicy Action Observation) (n : ℕ)
    (h : CausalFiniteTrace Action Observation (n+1)) :
    CausalFiniteTrace Action Observation (n+1) → ℝ :=
  experiment ρ (n+1) (summaryRepresentative n (extractSummary n h))

theorem inspectionReplay_valid (ρ : CausalPolicy Action Observation)
    (hρ : IsCausalPolicy ρ) (n : ℕ) : inspectionReplay ρ n ∈ stochasticRules _ _ := by
  intro h _
  exact experiment_valid ρ hρ (n+1) _

theorem inspectionReplay_law (ρ : CausalPolicy Action Observation) (_hρ : IsCausalPolicy ρ)
    (n : ℕ) : finiteDecisionLaw (experiment inspectPolicy (n+1))
      (inspectionReplay ρ n) = experiment ρ (n+1) := by
  funext θ u
  unfold finiteDecisionLaw
  have he : ∀ h, experiment inspectPolicy (n+1) θ h * inspectionReplay ρ n h u =
      experiment inspectPolicy (n+1) θ h * experiment ρ (n+1) θ u := by
    intro h
    by_cases hh : experiment inspectPolicy (n+1) θ h = 0
    · simp [hh]
    · unfold inspectionReplay
      rw [extractSummary_supported θ n h hh]
      rw [experiment_eq_of_summary_eq (summaryRepresentative_summary n θ) ρ]
  simp_rw [he]
  rw [← Finset.sum_mul, (experiment_valid inspectPolicy inspectPolicy_valid (n+1) θ).2,
    one_mul]

/-- Literal complete exploration: inspection simulates every finite experiment
induced by every valid policy at the same positive horizon, including all
native plans. -/
theorem inspection_dominates_every_finite_policy (ρ : CausalPolicy Action Observation)
    (hρ : IsCausalPolicy ρ) (n : ℕ) :
    FiniteBlackwellLE (experiment ρ (n+1)) (experiment inspectPolicy (n+1)) :=
  ⟨inspectionReplay ρ n, inspectionReplay_valid ρ hρ n, inspectionReplay_law ρ hρ n⟩

theorem inspection_deficiency_zero (ρ : CausalPolicy Action Observation)
    (hρ : IsCausalPolicy ρ) (n : ℕ) :
    finiteDeficiency (experiment inspectPolicy (n+1)) (experiment ρ (n+1)) = 0 := by
  apply le_antisymm
  · apply finiteDeficiency_le_of_decoder _ _ (inspectionReplay ρ n)
      (inspectionReplay_valid ρ hρ n)
    intro θ
    apply le_of_eq
    change (1 / 2 : ℝ) * ∑ u, |finiteDecisionLaw
      (experiment inspectPolicy (n+1)) (inspectionReplay ρ n) θ u - experiment ρ (n+1) θ u| = 0
    rw [inspectionReplay_law ρ hρ n]
    simp
  · exact finiteDeficiency_nonneg_of_valid _ _
      (experiment_valid inspectPolicy inspectPolicy_valid _) (experiment_valid ρ hρ (n+1))

end IdExp.PairedAlarm
