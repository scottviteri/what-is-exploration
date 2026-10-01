import Formal.AlarmPanelNativeFailure

/-! On every positive-probability inspection trace, only startup and the
single monitor pulse can have a nonzero raw observation. -/
noncomputable section
namespace IdExp.AlarmPanel
open Finset

 def pulsePosition : World → ℕ
   | none => 0
   | some k => 2*k+2

 theorem inspection_supported_nonzero_index (θ : World) (t : ℕ)
    (h : CausalFiniteTrace Action Observation t)
    (hh : experiment inspectPolicy t θ h ≠ 0) (i : Fin t) (hi : (h i).2 ≠ 0) :
    i.val = 0 ∨ i.val = pulsePosition θ := by
  by_cases hz : i.val = 0
  · exact Or.inl hz
  right
  have ht : 0 < t := by omega
  have hroot := (inspect_supported_root θ t ht h hh).1
  have he := experiment_response_ne_zero inspectPolicy θ t h hh i
  have hlen : ((List.ofFn h).take i.val).length = i.val := by
    simp only [List.length_take,List.length_ofFn]; omega
  have hmode : inspected ((List.ofFn h).take i.val) := by
    unfold inspected
    rw [List.head?_take, if_neg hz]
    cases t with
    | zero => omega
    | succ n => simpa [List.ofFn_succ] using hroot
  have hp : i.val % 2 ≠ 1 := by
    intro hpar
    rw [response_panel θ _ _ _ (by rwa [hlen]), if_pos hmode] at he
    have ho : (h i).2 = 0 := by simpa [pointDist] using he
    exact hi ho
  have hn : (List.ofFn h).take i.val ≠ [] := by
    intro hn; rw [hn] at hlen; simp at hlen; omega
  rw [response_monitor θ _ _ _ hn (by rwa [hlen]), hlen] at he
  have ho : (h i).2 = monitorLabel θ ((i.val-2)/2) := by simpa [pointDist] using he
  have hm : θ = some ((i.val-2)/2) := by
    by_contra hm
    simp [monitorLabel,hm] at ho
    exact hi ho
  rw [hm]
  simp only [pulsePosition]
  omega

 theorem countP_ofFn_eq_sum {X : Type*} (p : X → Bool) (t : ℕ) (f : Fin t → X) :
    (List.ofFn f).countP p = ∑ i, if p (f i) then 1 else 0 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [List.ofFn_succ, List.countP_cons, Fin.sum_univ_succ, ih]
    split <;> simp_all [Nat.add_comm]

 theorem sum_index_indicator_le_one (t c : ℕ) :
    (∑ i : Fin t, if i.val = c then 1 else 0 : ℕ) ≤ 1 := by
  have hc : (Finset.univ.filter (fun i : Fin t => i.val = c)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    apply Fin.ext
    exact (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm
  simpa only [Finset.card_filter] using hc

 theorem inspection_nonzero_count_le_two (θ : World) (t : ℕ)
    (h : CausalFiniteTrace Action Observation t)
    (hh : experiment inspectPolicy t θ h ≠ 0) :
    (List.ofFn (fun i => (h i).2)).countP (fun o => decide (o ≠ 0)) ≤ 2 := by
  rw [countP_ofFn_eq_sum]
  calc
    _ ≤ ∑ i : Fin t, ((if i.val = 0 then 1 else 0) +
        (if i.val = pulsePosition θ then 1 else 0) : ℕ) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : (h i).2 = 0
      · simp [hi]
      · obtain h0 | hk := inspection_supported_nonzero_index θ t h hh i hi
        · simp [hi,h0]
        · simp [hi,hk]
    _ = (∑ i : Fin t, if i.val = 0 then 1 else 0) +
        (∑ i : Fin t, if i.val = pulsePosition θ then 1 else 0) := Finset.sum_add_distrib
    _ ≤ 2 := by have := sum_index_indicator_le_one t 0
                have := sum_index_indicator_le_one t (pulsePosition θ)
                omega


/-- The deterministic observation archive once the startup color is fixed. -/
 def canonicalArchive (θ : World) (startup : Observation) (t : ℕ) : List Observation :=
   List.ofFn (fun i : Fin t => if i.val = 0 then startup else
     if i.val % 2 = 1 then 0 else monitorLabel θ ((i.val-2)/2))

 def startupLabel (θ : World) (color : Bool) : Observation :=
   if θ.isSome then (if color then 3 else 2) else (if color then 1 else 0)

 theorem inspection_observation_after_root (θ : World) (t : ℕ)
    (h : CausalFiniteTrace Action Observation t)
    (hh : experiment inspectPolicy t θ h ≠ 0) (i : Fin t) (hz : i.val ≠ 0) :
    (h i).2 = if i.val % 2 = 1 then 0 else monitorLabel θ ((i.val-2)/2) := by
  have ht : 0 < t := by omega
  have hroot := (inspect_supported_root θ t ht h hh).1
  have he := experiment_response_ne_zero inspectPolicy θ t h hh i
  have hlen : ((List.ofFn h).take i.val).length = i.val := by
    simp only [List.length_take,List.length_ofFn]; omega
  have hmode : inspected ((List.ofFn h).take i.val) := by
    unfold inspected
    rw [List.head?_take, if_neg hz]
    cases t with
    | zero => omega
    | succ n => simpa [List.ofFn_succ] using hroot
  by_cases hp : i.val % 2 = 1
  · rw [response_panel θ _ _ _ (by rwa [hlen]), if_pos hmode] at he
    simpa [pointDist, hp] using he
  · have hn : (List.ofFn h).take i.val ≠ [] := by
      intro hn; rw [hn] at hlen; simp at hlen; omega
    rw [response_monitor θ _ _ _ hn (by rwa [hlen]), hlen] at he
    simpa [pointDist,hp] using he

 theorem inspection_archive_supported (θ : World) (n : ℕ)
    (h : CausalFiniteTrace Action Observation (n+1))
    (hh : experiment inspectPolicy (n+1) θ h ≠ 0) :
    List.ofFn (fun i => (h i).2) = canonicalArchive θ (h 0).2 (n+1) := by
  unfold canonicalArchive
  congr 1
  funext i
  by_cases hi : i.val = 0
  · have he : i = 0 := Fin.ext hi
    simp [hi,he]
  · rw [if_neg hi]
    exact inspection_observation_after_root θ (n+1) h hh i hi

/-- Arbitrary observation-archive payoffs under actual inspection execution
reduce to exactly two equiprobable startup colors, at every positive horizon. -/
 theorem inspection_archive_expectation (θ : World) (n : ℕ) (f : List Observation → ℝ) :
    (∑ h : CausalFiniteTrace Action Observation (n+1),
      experiment inspectPolicy (n+1) θ h * f (List.ofFn (fun i => (h i).2))) =
      (f (canonicalArchive θ (startupLabel θ false) (n+1)) +
        f (canonicalArchive θ (startupLabel θ true) (n+1)))/2 := by
  have he : ∀ h : CausalFiniteTrace Action Observation (n+1),
      experiment inspectPolicy (n+1) θ h * f (List.ofFn (fun i => (h i).2)) =
      experiment inspectPolicy (n+1) θ h * f (canonicalArchive θ (h 0).2 (n+1)) := by
    intro h
    by_cases hh : experiment inspectPolicy (n+1) θ h = 0
    · simp [hh]
    · rw [inspection_archive_supported θ n h hh]
  simp_rw [he]
  rw [firstExpectation inspectPolicy inspectPolicy_valid θ n
    (fun ao => f (canonicalArchive θ ao.2 (n+1))), Fintype.sum_prod_type]
  cases θ <;> norm_num [response_root, inspectPolicy, detPolicy, inspect, pairDist,
    uniformDist, startupLabel, Fin.sum_univ_succ, Fin.succ] <;> ring_nf <;> rfl


 theorem canonicalArchive_nonzero_count_le_two (θ : World) (startup : Observation) (t : ℕ) :
    (canonicalArchive θ startup t).countP (fun o => decide (o ≠ 0)) ≤ 2 := by
  unfold canonicalArchive
  rw [countP_ofFn_eq_sum]
  calc
    _ ≤ ∑ i : Fin t, ((if i.val = 0 then 1 else 0) +
        (if i.val = pulsePosition θ then 1 else 0) : ℕ) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hz : i.val = 0
      · simp only [hz, ↓reduceIte]
        split_ifs <;> omega
      · simp only [hz, ↓reduceIte, zero_add]
        by_cases hp : i.val % 2 = 1
        · simp [hp]
        · simp only [hp, ↓reduceIte]
          by_cases hm : θ = some ((i.val-2)/2)
          · have hi : i.val = pulsePosition θ := by rw [hm]; simp only [pulsePosition]; omega
            rw [if_pos hi]
            simp only [monitorLabel, if_pos hm]
            decide
          · simp [monitorLabel,hm]
    _ = (∑ i : Fin t, if i.val = 0 then 1 else 0) +
        (∑ i : Fin t, if i.val = pulsePosition θ then 1 else 0) := Finset.sum_add_distrib
    _ ≤ 2 := by have := sum_index_indicator_le_one t 0
                have := sum_index_indicator_le_one t (pulsePosition θ)
                omega

 theorem canonicalArchive_take (θ : World) (startup : Observation) (m t : ℕ) (hmt : m ≤ t) :
    (canonicalArchive θ startup t).take m = canonicalArchive θ startup m := by
  apply List.ext_getElem
  · simp [canonicalArchive, hmt]
  · intro i hi hi'
    simp [canonicalArchive]

end IdExp.AlarmPanel
