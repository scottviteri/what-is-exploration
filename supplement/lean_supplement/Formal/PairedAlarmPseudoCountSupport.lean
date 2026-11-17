import Formal.PairedAlarmNativeExtraction
import Formal.PairedAlarmPseudoCountExpectation
import Formal.CausalBlockSplice

/-!
# Pathwise label counts on supported simultaneous-alarm records

Two facts about every positive-probability collected record.

* After an inspecting startup, every later observation is `(0, monitor bit)`,
  whatever the later (possibly randomized, adaptive) actions are, and the
  monitor bit is nonzero only at the single pulse position. So at most two raw
  labels differ from `(0,0)`: the startup label and the pulse.
* The deterministic witness that plays PLAY₁ at even history lengths (startup
  included) and PLAY₀ at odd ones yields, at odd positions, display labels in
  `{0,1}` and, at even positions `≥ 2`, display labels in `{2,3}`; apart from
  the single pulse position the monitor bit is zero. A length-`t` record thus
  holds at least `⌊t/2⌋-1` labels in `{(0,0),(1,0)}` and at least
  `⌊(t-1)/2⌋-1` labels in `{(2,0),(3,0)}`.

Unlike the alternating interface there are no separate monitor-tick labels.
-/

namespace IdExp.PairedAlarm.PseudoCount
noncomputable section
open Finset

/-- The raw observation labels of a collected record, in order. -/
abbrev archive {t : ℕ} (w : CausalFiniteTrace Action Observation t) : List Observation :=
  List.ofFn (fun i => (w i).2)

/-! ## Generic counting helpers -/

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

/-- Injectively selected record positions lower-bound a label count. -/
theorem selected_count_le {t : ℕ} (w : CausalFiniteTrace Action Observation t)
    (p : Observation → Bool) {ι : Type*} [Fintype ι]
    (s : Finset ι) (f : ι → Fin t)
    (hf : Set.InjOn f s) (hp : ∀ i ∈ s, p (w (f i)).2 = true) :
    s.card ≤ (archive w).countP p := by
  classical
  have hc := Finset.card_le_card_of_injOn f
    (t := univ.filter (fun i : Fin t => p (w i).2))
    (fun i hi => mem_filter.mpr ⟨mem_univ _, hp i hi⟩) hf
  simpa only [Finset.card_filter, countP_ofFn_eq_sum] using hc

/-- If all but at most one of `m` injectively selected positions carry a label
satisfying `p`, the record has at least `m - 1` such labels. -/
theorem selected_count_ge_sub_one {t m : ℕ} (w : CausalFiniteTrace Action Observation t)
    (p : Observation → Bool) (f : Fin m → Fin t) (hf : Function.Injective f)
    (bad : Fin m → Prop) [DecidablePred bad] (hbad : ∀ i j, bad i → bad j → i = j)
    (hp : ∀ i, ¬ bad i → p (w (f i)).2 = true) :
    m - 1 ≤ (archive w).countP p := by
  let good : Finset (Fin m) := univ.filter (fun i => ¬ bad i)
  let badSet : Finset (Fin m) := univ.filter bad
  have hb : badSet.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact hbad i j (mem_filter.mp hi).2 (mem_filter.mp hj).2
  have hsum : good.card + badSet.card = m := by
    have h := Finset.card_filter_add_card_filter_not (s := univ) (fun i : Fin m => ¬ bad i)
    simpa [good, badSet] using h
  have hc := selected_count_le w p good f (fun _ _ _ _ he => hf he)
    (fun i hi => hp i (mem_filter.mp hi).2)
  omega

/-! ## Supported actions, displays, and monitor bits -/

theorem supported_action (π : CausalPolicy Action Observation) (θ : World) (t : ℕ)
    (w : CausalFiniteTrace Action Observation t) (hw : experiment π t θ w ≠ 0) (i : Fin t) :
    π ((List.ofFn w).take i.val) (w i).1 ≠ 0 := by
  simpa using causalTraceProb_policy_ne_zero π (response θ) (List.ofFn w) hw
    ⟨i.val, by simp⟩

theorem take_length {t : ℕ} (w : CausalFiniteTrace Action Observation t) (i : Fin t) :
    ((List.ofFn w).take i.val).length = i.val := by
  simp only [List.length_take, List.length_ofFn]; omega

theorem take_ne_nil {t : ℕ} (w : CausalFiniteTrace Action Observation t) (i : Fin t)
    (hi : i.val ≠ 0) : (List.ofFn w).take i.val ≠ [] := by
  intro hn
  have hlen := take_length w i
  rw [hn] at hlen
  simp at hlen
  omega

/-- After startup the mode is read from the retained startup action. -/
theorem inspected_take_iff {t : ℕ} (w : CausalFiniteTrace Action Observation t) (i : ℕ)
    (hi : i ≠ 0) (ht : 0 < t) :
    inspected ((List.ofFn w).take i) ↔ (w ⟨0, ht⟩).1 = inspect := by
  unfold inspected
  rw [List.head?_take, if_neg hi]
  cases t with
  | zero => omega
  | succ n => simp [List.ofFn_succ]

/-- Every later supported display has positive probability under the panel law. -/
theorem supported_display (π : CausalPolicy Action Observation) (θ : World) (t : ℕ)
    (w : CausalFiniteTrace Action Observation t) (hw : experiment π t θ w ≠ 0) (i : Fin t)
    (hi : i.val ≠ 0) :
    panelDisplay ((List.ofFn w).take i.val) (w i).1 (w i).2.1 ≠ 0 := by
  have he := experiment_response_ne_zero π θ t w hw i
  rw [response_tick θ _ _ _ (take_ne_nil w i hi)] at he
  exact left_ne_zero_of_mul he

/-- The position at which the single alarm pulse is observed (`0` for `none`,
where no pulse occurs and the startup monitor bit is zero anyway). -/
def pulsePosition : World → ℕ
  | none => 0
  | some k => k + 1

theorem monitorAt_eq_zero_of_ne (θ : World) (i : ℕ) (hi : i ≠ pulsePosition θ) :
    monitorAt θ i = 0 := by
  cases θ with
  | none => simp [monitorAt, waitingQueryBit]
  | some k =>
    have hk : i ≠ k + 1 := by simpa [pulsePosition] using hi
    simp [monitorAt, waitingQueryBit, hk]

/-! ## Inspection branches -/

theorem inspectBranch_supported_root (π : CausalPolicy Action Observation)
    (θ : World) (t : ℕ) (ht : 0 < t) (w : CausalFiniteTrace Action Observation t)
    (hw : experiment (inspectBranch π) t θ w ≠ 0) : (w ⟨0, ht⟩).1 = inspect := by
  simpa [inspectBranch] using supported_action (inspectBranch π) θ t w hw ⟨0, ht⟩

/-- After an inspecting startup, every later supported label is `(0, monitor bit)`,
for arbitrary randomized adaptive later actions. -/
theorem inspecting_supported_label (π : CausalPolicy Action Observation)
    (θ : World) (t : ℕ) (w : CausalFiniteTrace Action Observation t)
    (hw : experiment π t θ w ≠ 0)
    (hroot : ∀ ht : 0 < t, (w ⟨0, ht⟩).1 = inspect)
    (i : Fin t) (hi : i.val ≠ 0) : (w i).2 = (0, monitorAt θ i.val) := by
  have ht : 0 < t := by omega
  have hd := supported_display π θ t w hw i hi
  have hmode : inspected ((List.ofFn w).take i.val) :=
    (inspected_take_iff w i.val hi ht).mpr (hroot ht)
  rw [panelDisplay, if_pos hmode] at hd
  have hdisp : (w i).2.1 = 0 := by
    by_contra hne
    exact hd (by simp [pointDisplay, hne])
  exact Prod.ext hdisp (supported_monitor π θ t w hw i)

theorem inspecting_supported_nonzero_index (π : CausalPolicy Action Observation)
    (θ : World) (t : ℕ) (w : CausalFiniteTrace Action Observation t)
    (hw : experiment π t θ w ≠ 0)
    (hroot : ∀ ht : 0 < t, (w ⟨0, ht⟩).1 = inspect)
    (i : Fin t) (hi : (w i).2 ≠ (0, 0)) : i.val = 0 ∨ i.val = pulsePosition θ := by
  by_cases hz : i.val = 0
  · exact Or.inl hz
  right
  by_contra hp
  apply hi
  rw [inspecting_supported_label π θ t w hw hroot i hz, monitorAt_eq_zero_of_ne θ i.val hp]

/-- On every supported inspection-branch record at most two labels differ from `(0,0)`. -/
theorem inspectBranch_offCount_le_two (π : CausalPolicy Action Observation)
    (θ : World) (t : ℕ) (w : CausalFiniteTrace Action Observation t)
    (hw : experiment (inspectBranch π) t θ w ≠ 0) :
    (archive w).countP (fun o => decide (o ≠ (0, 0))) ≤ 2 := by
  rw [countP_ofFn_eq_sum]
  calc
    _ ≤ ∑ i : Fin t, ((if i.val = 0 then 1 else 0) +
        (if i.val = pulsePosition θ then 1 else 0) : ℕ) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : (w i).2 = (0, 0)
      · simp [hi]
      · obtain h0 | hk := inspecting_supported_nonzero_index (inspectBranch π) θ t w hw
          (fun ht => inspectBranch_supported_root π θ t ht w hw) i hi
        · simp [hi, h0]
        · simp [hi, hk]
    _ = (∑ i : Fin t, if i.val = 0 then 1 else 0) +
        (∑ i : Fin t, if i.val = pulsePosition θ then 1 else 0) := Finset.sum_add_distrib
    _ ≤ 2 := by
      have := sum_index_indicator_le_one t 0
      have := sum_index_indicator_le_one t (pulsePosition θ)
      omega

/-! ## The alternating-play witness -/

/-- PLAY₀ at odd history lengths, PLAY₁ at even ones (including startup). -/
def altAction (h : History) : Action := if h.length % 2 = 1 then play0 else play1

/-- The deterministic alternating-play witness. -/
def altPolicy : CausalPolicy Action Observation := detPolicy altAction

theorem altPolicy_valid : IsCausalPolicy altPolicy := isCausalPolicy_detPolicy _

theorem alt_supported_action (θ : World) (t : ℕ)
    (w : CausalFiniteTrace Action Observation t) (hw : experiment altPolicy t θ w ≠ 0)
    (i : Fin t) : (w i).1 = if i.val % 2 = 1 then play0 else play1 := by
  have h := supported_action altPolicy θ t w hw i
  have ha : (w i).1 = altAction ((List.ofFn w).take i.val) := by
    by_contra hne
    exact h (detPolicy_of_ne altAction _ hne)
  rw [ha, altAction, take_length]

/-- At every later supported position of the witness, the display's high digit
is the parity-selected action digit. -/
theorem alt_supported_display (θ : World) (t : ℕ)
    (w : CausalFiniteTrace Action Observation t) (hw : experiment altPolicy t θ w ≠ 0)
    (i : Fin t) (hi : i.val ≠ 0) :
    (w i).2.1.val / 2 = if i.val % 2 = 1 then 0 else 1 := by
  have ht : 0 < t := by omega
  have hd := supported_display altPolicy θ t w hw i hi
  have hroot := alt_supported_action θ t w hw ⟨0, ht⟩
  have hmode : ¬ inspected ((List.ofFn w).take i.val) := by
    rw [inspected_take_iff w i.val hi ht, hroot]
    simp [play1, inspect]
  rw [panelDisplay, if_neg hmode, alt_supported_action θ t w hw i] at hd
  by_cases hpar : i.val % 2 = 1
  · rw [if_pos hpar] at hd ⊢
    have hb : (play0 == play1) = false := by decide
    rw [hb] at hd
    by_contra hne
    exact hd (by simp [pairDist, hne])
  · rw [if_neg hpar] at hd ⊢
    have hb : (play1 == play1) = true := by decide
    rw [hb] at hd
    by_contra hne
    exact hd (by simp [pairDist, hne])

/-- Low-display, monitor-zero labels collected by the witness. -/
theorem alt_low_count_ge (θ : World) (t : ℕ)
    (w : CausalFiniteTrace Action Observation t) (hw : experiment altPolicy t θ w ≠ 0) :
    t / 2 - 1 ≤ (archive w).countP (fun o => decide (o = (0, 0) ∨ o = (1, 0))) := by
  let f : Fin (t / 2) → Fin t := fun i => ⟨2 * i.val + 1, by omega⟩
  have hf : Function.Injective f := by
    intro i j he
    apply Fin.ext
    have := congrArg Fin.val he
    dsimp [f] at this
    omega
  refine selected_count_ge_sub_one w _ f hf (fun i => θ = some (2 * i.val))
    (fun i j hi hj => Fin.ext (by have := Option.some.inj (hi.symm.trans hj); omega)) ?_
  intro i hgood
  have hz : (f i).val ≠ 0 := by dsimp [f]; omega
  have hpar : (f i).val % 2 = 1 := by dsimp [f]; omega
  have hdisp := alt_supported_display θ t w hw (f i) hz
  rw [if_pos hpar] at hdisp
  have hmon := supported_monitor altPolicy θ t w hw (f i)
  have hfi : (f i).val = 2 * i.val + 1 := rfl
  rw [hfi, monitorAt_succ] at hmon
  have hm0 : (w (f i)).2.2 = 0 := by rw [hmon]; simp [monitorLabel, hgood]
  have hlt := (w (f i)).2.1.isLt
  have hd : (w (f i)).2.1 = 0 ∨ (w (f i)).2.1 = 1 := by
    have : (w (f i)).2.1.val = 0 ∨ (w (f i)).2.1.val = 1 := by omega
    rcases this with h | h
    · left; exact Fin.ext h
    · right; exact Fin.ext h
  simp only [decide_eq_true_eq]
  rcases hd with hd | hd
  · left; exact Prod.ext hd hm0
  · right; exact Prod.ext hd hm0

/-- High-display, monitor-zero labels collected by the witness. -/
theorem alt_high_count_ge (θ : World) (t : ℕ)
    (w : CausalFiniteTrace Action Observation t) (hw : experiment altPolicy t θ w ≠ 0) :
    (t - 1) / 2 - 1 ≤ (archive w).countP (fun o => decide (o = (2, 0) ∨ o = (3, 0))) := by
  let f : Fin ((t - 1) / 2) → Fin t := fun i => ⟨2 * i.val + 2, by omega⟩
  have hf : Function.Injective f := by
    intro i j he
    apply Fin.ext
    have := congrArg Fin.val he
    dsimp [f] at this
    omega
  refine selected_count_ge_sub_one w _ f hf (fun i => θ = some (2 * i.val + 1))
    (fun i j hi hj => Fin.ext (by have := Option.some.inj (hi.symm.trans hj); omega)) ?_
  intro i hgood
  have hz : (f i).val ≠ 0 := by dsimp [f]; omega
  have hpar : ¬ (f i).val % 2 = 1 := by dsimp [f]; omega
  have hdisp := alt_supported_display θ t w hw (f i) hz
  rw [if_neg hpar] at hdisp
  have hmon := supported_monitor altPolicy θ t w hw (f i)
  have hfi : (f i).val = (2 * i.val + 1) + 1 := rfl
  rw [hfi, monitorAt_succ] at hmon
  have hm0 : (w (f i)).2.2 = 0 := by rw [hmon]; simp [monitorLabel, hgood]
  have hlt := (w (f i)).2.1.isLt
  have hd : (w (f i)).2.1 = 2 ∨ (w (f i)).2.1 = 3 := by
    have : (w (f i)).2.1.val = 2 ∨ (w (f i)).2.1.val = 3 := by omega
    rcases this with h | h
    · left; exact Fin.ext h
    · right; exact Fin.ext h
  simp only [decide_eq_true_eq]
  rcases hd with hd | hd
  · left; exact Prod.ext hd hm0
  · right; exact Prod.ext hd hm0

end
end IdExp.PairedAlarm.PseudoCount
