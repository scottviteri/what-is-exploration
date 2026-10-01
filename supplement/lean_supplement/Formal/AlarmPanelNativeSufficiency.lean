import Formal.AlarmPanelNativeExtraction

/-! Startup inspection is a sufficient policy on the literal stochastic
alarm-panel interface. Every finite record of every competing policy is an
exact randomized garbling of a finite inspection record. -/

noncomputable section
namespace IdExp.AlarmPanel
open Finset

 def inspectPolicy : CausalPolicy Action Observation := detPolicy (fun _ => inspect)
 theorem inspectPolicy_valid : IsCausalPolicy inspectPolicy := isCausalPolicy_detPolicy _

 def summary (n : ℕ) (θ : World) : Bool × (Fin n → Bool) :=
   (θ.isSome, fun k => decide (θ = some k.val))

 def extractSummary (n : ℕ) (h : CausalFiniteTrace Action Observation (2*n+1)) :
     Bool × (Fin n → Bool) :=
   (decide (2 ≤ (h ⟨0, by omega⟩).2.val),
     fun k => decide ((h ⟨2*k.val+2, by omega⟩).2 = 1))

 theorem inspect_supported_root (θ : World) (t : ℕ) (ht : 0 < t)
    (h : CausalFiniteTrace Action Observation t)
    (hh : experiment inspectPolicy t θ h ≠ 0) :
    (h ⟨0,ht⟩).1 = inspect ∧
      decide (2 ≤ (h ⟨0,ht⟩).2.val) = θ.isSome := by
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
  simp only [List.take_zero, response_root, hp, ↓reduceIte] at he
  have ho := (h ⟨0,ht⟩).2.isLt
  cases hθ : θ.isSome <;>
    simp only [hθ, pairDist, Bool.false_eq_true, ↓reduceIte] at he ⊢
  · have hb : (h ⟨0,ht⟩).2.val / 2 = 0 := by
      by_contra hbad; simp [hbad] at he
    have hb' : ¬2 ≤ (h ⟨0,ht⟩).2.val := by omega
    simp [hb']
  · have hb : (h ⟨0,ht⟩).2.val / 2 = 1 := by
      by_contra hbad; simp [hbad] at he
    have hb' : 2 ≤ (h ⟨0,ht⟩).2.val := by omega
    simp [hb']

 theorem extractSummary_supported (θ : World) (n : ℕ)
    (h : CausalFiniteTrace Action Observation (2*n+1))
    (hh : experiment inspectPolicy (2*n+1) θ h ≠ 0) :
    extractSummary n h = summary n θ := by
  apply Prod.ext
  · exact (inspect_supported_root θ (2*n+1) (by omega) h hh).2
  · funext k
    have hm := supported_monitor inspectPolicy θ (2*n+1) k.val (by omega) h hh
    change decide ((h ⟨2*k.val+2,by omega⟩).2 = 1) = decide (θ = some k.val)
    rw [hm]
    by_cases hk : θ = some k.val
    · simp [monitorLabel, hk]
    · simp [monitorLabel, hk]

 theorem response_eq_of_summary_eq {n : ℕ} {θ η : World}
    (he : summary n θ = summary n η) (h : History) (hh : h.length < n) (a : Action) :
    response θ h a = response η h a := by
  have hb := congrArg Prod.fst he
  have hm := congrArg Prod.snd he
  funext o
  unfold response
  split
  · simp only [summary] at hb
    rw [hb]
  · split
    · rfl
    · have hk : (h.length-2)/2 < n := by omega
      have hbit := congrFun hm ⟨(h.length-2)/2,hk⟩
      have hiff : (θ = some ((h.length-2)/2)) ↔ (η = some ((h.length-2)/2)) := by
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
    rw [ih (pre ++ [ao]) (by simp only [List.length_append, List.length_singleton,
      List.length_cons, List.length_nil] at *; omega)]

 theorem experiment_eq_of_summary_eq {n : ℕ} {θ η : World}
    (he : summary n θ = summary n η) (π : CausalPolicy Action Observation) :
    experiment π n θ = experiment π n η := by
  funext h
  exact traceProbFrom_congr_before π (response θ) (response η) n
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
    (h : CausalFiniteTrace Action Observation (2*n+1)) :
    CausalFiniteTrace Action Observation n → ℝ :=
  experiment ρ n (summaryRepresentative n (extractSummary n h))

 theorem inspectionReplay_valid (ρ : CausalPolicy Action Observation)
    (hρ : IsCausalPolicy ρ) (n : ℕ) : inspectionReplay ρ n ∈ stochasticRules _ _ := by
  intro h _
  exact experiment_valid ρ hρ n _

 theorem inspectionReplay_law (ρ : CausalPolicy Action Observation) (hρ : IsCausalPolicy ρ)
    (n : ℕ) : finiteDecisionLaw (experiment inspectPolicy (2*n+1))
      (inspectionReplay ρ n) = experiment ρ n := by
  funext θ u
  unfold finiteDecisionLaw
  have he : ∀ h, experiment inspectPolicy (2*n+1) θ h * inspectionReplay ρ n h u =
      experiment inspectPolicy (2*n+1) θ h * experiment ρ n θ u := by
    intro h
    by_cases hh : experiment inspectPolicy (2*n+1) θ h = 0
    · simp [hh]
    · unfold inspectionReplay
      rw [extractSummary_supported θ n h hh]
      rw [experiment_eq_of_summary_eq (summaryRepresentative_summary n θ) ρ]
  simp_rw [he]
  rw [← Finset.sum_mul, (experiment_valid inspectPolicy inspectPolicy_valid (2*n+1) θ).2,
    one_mul]

/-- Literal complete exploration: inspection eventually simulates every
finite experiment induced by every valid policy, including all native plans. -/
 theorem inspection_dominates_every_finite_policy (ρ : CausalPolicy Action Observation)
    (hρ : IsCausalPolicy ρ) (n : ℕ) :
    FiniteBlackwellLE (experiment ρ n) (experiment inspectPolicy (2*n+1)) :=
  ⟨inspectionReplay ρ n, inspectionReplay_valid ρ hρ n, inspectionReplay_law ρ hρ n⟩

 theorem inspection_deficiency_zero (ρ : CausalPolicy Action Observation)
    (hρ : IsCausalPolicy ρ) (n : ℕ) :
    finiteDeficiency (experiment inspectPolicy (2*n+1)) (experiment ρ n) = 0 :=
by
  apply le_antisymm
  · apply finiteDeficiency_le_of_decoder _ _ (inspectionReplay ρ n) (inspectionReplay_valid ρ hρ n)
    intro θ
    apply le_of_eq
    change (1 / 2 : ℝ) * ∑ u, |finiteDecisionLaw
      (experiment inspectPolicy (2*n+1)) (inspectionReplay ρ n) θ u - experiment ρ n θ u| = 0
    rw [inspectionReplay_law ρ hρ n]
    simp
  · exact finiteDeficiency_nonneg_of_valid _ _
      (experiment_valid inspectPolicy inspectPolicy_valid _) (experiment_valid ρ hρ n)


end IdExp.AlarmPanel
