import Formal.AlarmPanelNativeCompressionSupport
import Formal.StartupPolicyReferences
import Formal.CausalBlockSplice

/-! Pathwise counting for the continuing categorical count bonus. The bounds
retain arbitrary randomized continuations after an inspecting startup. -/
namespace IdExp.AlarmPanel.PseudoCount
noncomputable section
open Finset

abbrev archive {t : ℕ} (w : CausalFiniteTrace Action Observation t) : List Observation :=
  List.ofFn (fun i => (w i).2)

def highPolicy : CausalPolicy Action Observation := detPolicy (fun _ => play1)
theorem highPolicy_valid : IsCausalPolicy highPolicy := isCausalPolicy_detPolicy _

theorem supported_action (π : CausalPolicy Action Observation) (θ : World) (t : ℕ)
    (w : CausalFiniteTrace Action Observation t) (hw : experiment π t θ w ≠ 0) (i : Fin t) :
    π ((List.ofFn w).take i.val) (w i).1 ≠ 0 := by
  simpa using causalTraceProb_policy_ne_zero π (response θ) (List.ofFn w) hw
    ⟨i.val, by simpa using i.isLt⟩

theorem high_supported_action (θ : World) (t : ℕ)
    (w : CausalFiniteTrace Action Observation t) (hw : experiment highPolicy t θ w ≠ 0)
    (i : Fin t) : (w i).1 = play1 := by
  simpa [highPolicy, detPolicy] using supported_action highPolicy θ t w hw i

theorem inspectBranch_supported_root (π : CausalPolicy Action Observation)
    (θ : World) (t : ℕ) (ht : 0 < t) (w : CausalFiniteTrace Action Observation t)
    (hw : experiment (inspectBranch π) t θ w ≠ 0) : (w ⟨0, ht⟩).1 = inspect := by
  simpa [inspectBranch] using supported_action (inspectBranch π) θ t w hw ⟨0, ht⟩

theorem inspecting_supported_nonzero_index (π : CausalPolicy Action Observation)
    (θ : World) (t : ℕ) (w : CausalFiniteTrace Action Observation t)
    (hw : experiment π t θ w ≠ 0)
    (hroot : ∀ ht : 0 < t, (w ⟨0, ht⟩).1 = inspect)
    (i : Fin t) (hi : (w i).2 ≠ 0) : i.val = 0 ∨ i.val = pulsePosition θ := by
  by_cases hz : i.val = 0
  · exact Or.inl hz
  right
  have ht : 0 < t := by omega
  have he := experiment_response_ne_zero π θ t w hw i
  have hlen : ((List.ofFn w).take i.val).length = i.val := by
    simp only [List.length_take, List.length_ofFn]; omega
  have hmode : inspected ((List.ofFn w).take i.val) := by
    unfold inspected
    rw [List.head?_take, if_neg hz]
    cases t with
    | zero => omega
    | succ n => simpa [List.ofFn_succ] using hroot ht
  have hp : i.val % 2 ≠ 1 := by
    intro hpar
    rw [response_panel θ _ _ _ (by rwa [hlen]), if_pos hmode] at he
    have ho : (w i).2 = 0 := by simpa [pointDist] using he
    exact hi ho
  have hn : (List.ofFn w).take i.val ≠ [] := by
    intro hn; rw [hn] at hlen; simp at hlen; omega
  rw [response_monitor θ _ _ _ hn (by rwa [hlen]), hlen] at he
  have ho : (w i).2 = monitorLabel θ ((i.val-2)/2) := by simpa [pointDist] using he
  have hm : θ = some ((i.val-2)/2) := by
    by_contra hm
    simp [monitorLabel, hm] at ho
    exact hi ho
  rw [hm]
  simp only [pulsePosition]
  omega

theorem inspectBranch_nonzero_count_le_two (π : CausalPolicy Action Observation)
    (θ : World) (t : ℕ) (w : CausalFiniteTrace Action Observation t)
    (hw : experiment (inspectBranch π) t θ w ≠ 0) :
    (archive w).countP (fun o => decide (o ≠ 0)) ≤ 2 := by
  rw [countP_ofFn_eq_sum]
  calc
    _ ≤ ∑ i : Fin t, ((if i.val = 0 then 1 else 0) +
        (if i.val = pulsePosition θ then 1 else 0) : ℕ) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : (w i).2 = 0
      · simp [hi]
      · obtain h0 | hk := inspecting_supported_nonzero_index (inspectBranch π) θ t w hw
          (fun ht => inspectBranch_supported_root π θ t ht w hw) i hi
        · simp [hi, h0]
        · simp [hi, hk]
    _ = (∑ i : Fin t, if i.val = 0 then 1 else 0) +
        (∑ i : Fin t, if i.val = pulsePosition θ then 1 else 0) := Finset.sum_add_distrib
    _ ≤ 2 := by have := sum_index_indicator_le_one t 0
                have := sum_index_indicator_le_one t (pulsePosition θ)
                omega

theorem high_supported_panel (θ : World) (t : ℕ)
    (w : CausalFiniteTrace Action Observation t) (hw : experiment highPolicy t θ w ≠ 0)
    (i : Fin t) (hi : i.val % 2 = 1) : (w i).2 = 2 ∨ (w i).2 = 3 := by
  have hz : i.val ≠ 0 := by omega
  have ht : 0 < t := by omega
  have hroot := high_supported_action θ t w hw ⟨0, ht⟩
  have he := experiment_response_ne_zero highPolicy θ t w hw i
  have hlen : ((List.ofFn w).take i.val).length = i.val := by
    simp only [List.length_take, List.length_ofFn]; omega
  have hmode : ¬ inspected ((List.ofFn w).take i.val) := by
    unfold inspected
    rw [List.head?_take, if_neg hz]
    cases t with
    | zero => omega
    | succ n =>
        have hr : (w 0).1 = play1 := hroot
        simp [List.ofFn_succ, hr, play1, inspect]
  rw [response_panel θ _ _ _ (by rwa [hlen]), if_neg hmode,
    high_supported_action θ t w hw i] at he
  have hv : (w i).2.val / 2 = 1 := by
    by_contra hbad
    simp [pairDist, hbad] at he
  have ho := (w i).2.isLt
  have hh : (w i).2.val = 2 ∨ (w i).2.val = 3 := by omega
  simpa [Fin.ext_iff] using hh

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

theorem high_count_ge (θ : World) (t : ℕ)
    (w : CausalFiniteTrace Action Observation t) (hw : experiment highPolicy t θ w ≠ 0) :
    t / 2 ≤ (archive w).countP (fun o => decide (o = 2 ∨ o = 3)) := by
  let f : Fin (t / 2) → Fin t := fun i => ⟨2 * i.val + 1, by omega⟩
  have hf : Function.Injective f := by
    intro i j he
    apply Fin.ext
    have := congrArg Fin.val he
    dsimp [f] at this
    omega
  have hc := selected_count_le w (fun o => decide (o = 2 ∨ o = 3)) univ f
    (fun _ _ _ _ he => hf he) (by
      intro i _
      simp only [decide_eq_true_eq]
      exact high_supported_panel θ t w hw (f i) (by dsimp [f]; omega))
  simpa using hc

theorem zero_count_ge (π : CausalPolicy Action Observation) (θ : World) (t : ℕ)
    (w : CausalFiniteTrace Action Observation t) (hw : experiment π t θ w ≠ 0) :
    (t - 1) / 2 - 1 ≤ (archive w).count 0 := by
  let m := (t - 1) / 2
  let good : Finset (Fin m) := univ.filter (fun i => θ ≠ some i.val)
  let bad : Finset (Fin m) := univ.filter (fun i => θ = some i.val)
  have hb : bad.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    apply Fin.ext
    have hi' := (mem_filter.mp hi).2
    have hj' := (mem_filter.mp hj).2
    exact Option.some.inj (hi'.symm.trans hj')
  have hsum : good.card + bad.card = m := by
    have h := Finset.card_filter_add_card_filter_not (s := univ) (fun i : Fin m => θ ≠ some i.val)
    simpa [good, bad] using h
  let f : Fin m → Fin t := fun i => ⟨2 * i.val + 2, by dsimp [m] at i ⊢; omega⟩
  have hf : Function.Injective f := by
    intro i j he
    apply Fin.ext
    have := congrArg Fin.val he
    dsimp [f] at this
    omega
  have hc := selected_count_le w (fun o => decide (o = 0)) good f
    (fun _ _ _ _ he => hf he) (by
      intro i hi
      have he := supported_monitor π θ t i.val (by dsimp [m] at i ⊢; omega) w hw
      change (w (f i)).2 = monitorLabel θ i.val at he
      have hi' := (mem_filter.mp hi).2
      simp only [decide_eq_true_eq]
      simpa [monitorLabel, hi'] using he)
  have he : (archive w).countP (fun o => decide (o = 0)) = (archive w).count 0 := by
    induction archive w with
    | nil => simp
    | cons a l ih =>
        by_cases ha : a = 0
        · subst a; simp [ih]
        · have ha' : (0 : Observation) ≠ a := Ne.symm ha
          simp only [List.countP_cons, List.count_cons, ha, ha', decide_false, Bool.false_eq_true, if_false, Nat.add_zero, ih]
          simp only [beq_iff_eq, ha, if_false, Nat.add_zero]
  rw [he] at hc
  dsimp [m] at hsum
  omega

end
end IdExp.AlarmPanel.PseudoCount
