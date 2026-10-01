import Formal.AlarmPanel
import Formal.PulseBehavior

/-! The literal alarm-monitor record is an exact deterministic garbling of
any policy's collected alarm-panel history. No policy or quotient-equivalence
premise is assumed. -/

noncomputable section
namespace IdExp.AlarmPanel
open Finset

 theorem trace_response_ne_zero (π : CausalPolicy Action Observation) (θ : World)
    (h : History) (hh : causalTraceProb π (response θ) h ≠ 0) (i : Fin h.length) :
    response θ (h.take i.val) (h[i.val]).1 (h[i.val]).2 ≠ 0 := by
  have hprod : causalTraceProb π (response θ) (h.take i.val) *
      causalTraceProbFrom π (response θ) (h.take i.val) (h.drop i.val) ≠ 0 := by
    rwa [← causalTraceProb_append, List.take_append_drop]
  have htail := (mul_ne_zero_iff.mp hprod).2
  rw [List.drop_eq_getElem_cons i.isLt] at htail
  exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp htail).1).2

 theorem experiment_response_ne_zero (π : CausalPolicy Action Observation)
    (θ : World) (t : ℕ) (h : CausalFiniteTrace Action Observation t)
    (hh : experiment π t θ h ≠ 0) (i : Fin t) :
    response θ ((List.ofFn h).take i.val) (h i).1 (h i).2 ≠ 0 := by
  have he := trace_response_ne_zero π θ (List.ofFn h) hh
    ⟨i.val, by simpa using i.isLt⟩
  simpa using he

 theorem supported_monitor (π : CausalPolicy Action Observation)
    (θ : World) (t k : ℕ) (hk : 2*k+2 < t)
    (h : CausalFiniteTrace Action Observation t) (hh : experiment π t θ h ≠ 0) :
    (h ⟨2*k+2,hk⟩).2 = monitorLabel θ k := by
  have he := experiment_response_ne_zero π θ t h hh ⟨2*k+2,hk⟩
  have hlen : ((List.ofFn h).take (2*k+2)).length = 2*k+2 := by
    simp only [List.length_take, List.length_ofFn]
    omega
  have hn : (List.ofFn h).take (2*k+2) ≠ [] := by
    intro hz; rw [hz] at hlen; simp at hlen
  have hp : ((List.ofFn h).take (2*k+2)).length % 2 ≠ 1 := by omega
  rw [response_monitor θ _ _ _ hn hp] at he
  have hidx : (((List.ofFn h).take (2*k+2)).length - 2) / 2 = k := by omega
  rw [hidx] at he
  simpa [pointDist] using he

/-- Ignore startup and toy colors; reinsert the original WAIT action record.
The source has at least every monitor coordinate needed by the output. -/
def extractWait (n : ℕ) (h : CausalFiniteTrace Action Observation (2*n+1)) :
    CausalFiniteTrace Bool Bool n := fun i =>
  (false, if i.val = 0 then false else decide ((h ⟨2*i.val, by omega⟩).2 = 1))

 theorem extractWait_supported (π : CausalPolicy Action Observation)
    (θ : World) (n : ℕ) (h : CausalFiniteTrace Action Observation (2*n+1))
    (hh : experiment π (2*n+1) θ h ≠ 0) :
    extractWait n h = waitingQueryTrace n θ := by
  funext i
  by_cases hi : i.val = 0
  · cases θ <;> simp [extractWait, waitingQueryTrace, waitingQueryBit, hi]
  · have hm := supported_monitor π θ (2*n+1) (i.val-1) (by omega) h hh
    have hidx : 2*(i.val-1)+2 = 2*i.val := by omega
    have hm' : (h ⟨2*i.val, by omega⟩).2 = monitorLabel θ (i.val-1) := by
      have hf : (⟨2*(i.val-1)+2, by omega⟩ : Fin (2*n+1)) =
            ⟨2*i.val, by omega⟩ := Fin.ext hidx
      rw [hf] at hm
      exact hm
    simp only [extractWait, hi, ↓reduceIte, waitingQueryTrace, hm']
    cases θ with
    | none => simp [monitorLabel, waitingQueryBit]
    | some k =>
      simp only [monitorLabel, Option.some.injEq, waitingQueryBit]
      have he : k = i.val-1 ↔ i.val = k+1 := by omega
      by_cases hk : k = i.val-1
      · rw [if_pos hk]
        have hw := he.mp hk
        norm_num only [hw, decide_true]
      · rw [if_neg hk]
        have hw := mt he.mpr hk
        norm_num only [hw, decide_false]
        rfl


/-- The exposed deterministic stochastic rule for downstream score proofs. -/
def extractWaitRule (n : ℕ) (h : CausalFiniteTrace Action Observation (2*n+1))
    (u : CausalFiniteTrace Bool Bool n) : ℝ := if u = extractWait n h then 1 else 0

 theorem extractWaitRule_valid (n : ℕ) : extractWaitRule n ∈ stochasticRules _ _ := by
  intro h _
  constructor
  · intro u; unfold extractWaitRule; split <;> norm_num
  · simp [extractWaitRule]

 theorem extractWait_law (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (n : ℕ) : finiteDecisionLaw (experiment π (2*n+1)) (extractWaitRule n) =
      pulseExperiment false n := by
  rw [pulseExperiment_wait, waitingQueryExperiment_eq_dirac]
  funext θ u
  change (∑ h, experiment π (2*n+1) θ h *
    (if u = extractWait n h then 1 else 0)) = _
  have he : ∀ h, experiment π (2*n+1) θ h *
      (if u = extractWait n h then 1 else 0) =
      experiment π (2*n+1) θ h * (if u = waitingQueryTrace n θ then 1 else 0) := by
    intro h
    by_cases hh : experiment π (2*n+1) θ h = 0
    · simp [hh]
    · rw [extractWait_supported π θ n h hh]
  simp_rw [he]
  rw [← Finset.sum_mul, (experiment_valid π hπ (2*n+1) θ).2]
  simp [diracExp]

 theorem wait_blackwell (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (n : ℕ) : FiniteBlackwellLE (pulseExperiment false n) (experiment π (2*n+1)) :=
  ⟨extractWaitRule n, extractWaitRule_valid n, extractWait_law π hπ n⟩

end IdExp.AlarmPanel
