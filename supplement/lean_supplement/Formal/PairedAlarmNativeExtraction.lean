import Formal.PairedAlarm
import Formal.PulseBehavior

/-! On the current paired interface, the monitor coordinate of every collected
observation is the literal waiting-query bit at the same trace position. The
pulse interface's WAIT record is therefore an exact deterministic garbling of
any policy's collected record of the same length. No policy or
quotient-equivalence premise is assumed. -/

noncomputable section
namespace IdExp.PairedAlarm
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
    ⟨i.val, by simp⟩
  simpa using he

/-- The literal monitor coordinate at trace position `i`: zero at startup and
the alarm-tick-`(i-1)` reading afterwards. -/
def monitorAt (θ : World) (i : ℕ) : Monitor := if waitingQueryBit θ i then 1 else 0

@[simp] theorem monitorAt_zero (θ : World) : monitorAt θ 0 = 0 := by
  cases θ <;> simp [monitorAt, waitingQueryBit]

@[simp] theorem monitorAt_succ (θ : World) (k : ℕ) : monitorAt θ (k+1) = monitorLabel θ k := by
  cases θ with
  | none => simp [monitorAt, waitingQueryBit, monitorLabel]
  | some j =>
    by_cases hj : j = k
    · subst hj; simp [monitorAt, waitingQueryBit, monitorLabel]
    · have hj' : ¬ (some j : World) = some k := by simpa using hj
      simp [monitorAt, waitingQueryBit, monitorLabel, hj', Ne.symm hj]

theorem monitorAt_eq_one_iff (θ : World) (i : ℕ) :
    monitorAt θ i = 1 ↔ waitingQueryBit θ i = true := by
  unfold monitorAt
  split <;> simp_all

/-- Every supported collected observation carries the literal monitor bit. -/
theorem supported_monitor (π : CausalPolicy Action Observation)
    (θ : World) (t : ℕ) (h : CausalFiniteTrace Action Observation t)
    (hh : experiment π t θ h ≠ 0) (i : Fin t) :
    (h i).2.2 = monitorAt θ i.val := by
  have he := experiment_response_ne_zero π θ t h hh i
  by_cases hi : i.val = 0
  · have htake : (List.ofFn h).take i.val = [] := by simp [hi]
    rw [htake, response_root] at he
    have hm := right_ne_zero_of_mul he
    rw [hi, monitorAt_zero]
    by_contra hne
    exact hm (by simp [pointMonitor, hne])
  · have hlen : ((List.ofFn h).take i.val).length = i.val := by
      simp only [List.length_take, List.length_ofFn]
      omega
    have hn : (List.ofFn h).take i.val ≠ [] := by
      intro hz; rw [hz] at hlen; simp at hlen; omega
    rw [response_tick θ _ _ _ hn, hlen] at he
    have hm := right_ne_zero_of_mul he
    obtain ⟨k, hk⟩ : ∃ k, i.val = k + 1 := ⟨i.val - 1, by omega⟩
    rw [hk, monitorAt_succ]
    rw [hk, Nat.add_sub_cancel] at hm
    by_contra hne
    exact hm (by simp [pointMonitor, hne])

/-- Ignore startup and panel coordinates; reinsert the WAIT action record.
The source has every monitor coordinate needed by the output. -/
def extractWait (n : ℕ) (h : CausalFiniteTrace Action Observation n) :
    CausalFiniteTrace Bool Bool n := fun i => (false, decide ((h i).2.2 = 1))

theorem extractWait_supported (π : CausalPolicy Action Observation)
    (θ : World) (n : ℕ) (h : CausalFiniteTrace Action Observation n)
    (hh : experiment π n θ h ≠ 0) :
    extractWait n h = waitingQueryTrace n θ := by
  funext i
  simp only [extractWait, waitingQueryTrace, supported_monitor π θ n h hh i,
    monitorAt_eq_one_iff]
  cases hb : waitingQueryBit θ i.val <;> simp

/-- The exposed deterministic stochastic rule for downstream score proofs. -/
def extractWaitRule (n : ℕ) (h : CausalFiniteTrace Action Observation n)
    (u : CausalFiniteTrace Bool Bool n) : ℝ := if u = extractWait n h then 1 else 0

theorem extractWaitRule_valid (n : ℕ) : extractWaitRule n ∈ stochasticRules _ _ := by
  intro h _
  constructor
  · intro u; unfold extractWaitRule; split <;> norm_num
  · simp [extractWaitRule]

theorem extractWait_law (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (n : ℕ) : finiteDecisionLaw (experiment π n) (extractWaitRule n) =
      pulseExperiment false n := by
  rw [pulseExperiment_wait, waitingQueryExperiment_eq_dirac]
  funext θ u
  change (∑ h, experiment π n θ h *
    (if u = extractWait n h then 1 else 0)) = _
  have he : ∀ h, experiment π n θ h *
      (if u = extractWait n h then 1 else 0) =
      experiment π n θ h * (if u = waitingQueryTrace n θ then 1 else 0) := by
    intro h
    by_cases hh : experiment π n θ h = 0
    · simp [hh]
    · rw [extractWait_supported π θ n h hh]
  simp_rw [he]
  rw [← Finset.sum_mul, (experiment_valid π hπ n θ).2]
  simp [diracExp]

/-- Every collected record of length `n` contains the pulse WAIT record of the
same length; no alternating-index conversion is needed. -/
theorem wait_blackwell (π : CausalPolicy Action Observation) (hπ : IsCausalPolicy π)
    (n : ℕ) : FiniteBlackwellLE (pulseExperiment false n) (experiment π n) :=
  ⟨extractWaitRule n, extractWaitRule_valid n, extractWait_law π hπ n⟩

end IdExp.PairedAlarm
