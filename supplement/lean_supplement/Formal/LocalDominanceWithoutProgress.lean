import Formal.WaitProxyCausalProfile

/-!
# Finite lookahead dominance does not supply continued acquisition

A literal two-world wait/test process has one noisy test of strength 1/4
before a chosen deadline, and a revealing test of strength 1/2 afterward.
Testing absorbs. The immediate-test policy exactly simulates every native
experiment through the chosen short horizon, yet permanently loses 1/4 on
one fixed later native experiment. Waiting to the deadline is complete.
This is a BSC variant of Experiment 65's separate erasure example; equality
of their numerical deficits does not identify the two source experiments.
-/

namespace IdExp
noncomputable section
open Finset

def lookaheadStrength (d s : ℕ) : ℝ := if s < d then 1 / 4 else 1 / 2

theorem lookaheadStrength_nonneg (d s : ℕ) : 0 ≤ lookaheadStrength d s := by
  unfold lookaheadStrength
  split <;> norm_num

theorem lookaheadStrength_le_half (d s : ℕ) : lookaheadStrength d s ≤ 1 / 2 := by
  unfold lookaheadStrength
  split <;> norm_num

/-- One actual world-independent policy: wait S times, test, then wait forever. -/
def lookaheadPolicy (S : ℕ) :
    ValidCausalPolicy (WaitProxyAction Unit) WaitProxyObservation :=
  ⟨waitProxyOneShotPolicy S (fun _ : Unit => 1),
    waitProxyOneShotPolicy_valid S _ (by intros; norm_num) (by simp)⟩

theorem lookaheadPolicy_effective (S d t : ℕ) (hSt : S < t) :
    waitProxyEffectiveWeightFinite (lookaheadPolicy S).1 (lookaheadStrength d) t () =
      2 * lookaheadStrength d S := by
  unfold waitProxyEffectiveWeightFinite lookaheadPolicy
  simp_rw [waitProxyOneShot_firstTestMass]
  simp [hSt]

/-- The immediate test is an exact substitute for every deterministic native
experiment within the short lookahead window. -/
theorem lookahead_immediate_exact_short (d : ℕ) (hd : 0 < d)
    {n : ℕ} (hn : n ≤ d)
    (τ : CausalPlan (WaitProxyAction Unit) WaitProxyObservation n)
    {t : ℕ} (ht : 0 < t) :
    finiteDeficiency
      (causalFiniteExperiment (lookaheadPolicy 0).1 (waitProxyResponse (lookaheadStrength d)) t)
      (causalPlanObservationExperiment n τ (waitProxyResponse (lookaheadStrength d))) = 0 := by
  rcases waitProxyPlan_alwaysWait_or_firstTestsAt τ with hall | ⟨s, a, hfirst⟩
  · exact waitProxyNativePlan_alwaysWait_deficiency _
      (causalFiniteExperiment_valid _ (lookaheadPolicy 0).2 _
        (waitProxyResponse_valid _ (lookaheadStrength_nonneg d) (lookaheadStrength_le_half d)) t)
      τ _ (lookaheadStrength_nonneg d) (lookaheadStrength_le_half d) hall
  · have hs : s < n := hfirst.1
    have hsd : s < d := lt_of_lt_of_le hs hn
    have hf := waitProxyPolicyTestDeficiency_eq_of_first (a := a)
      (lookaheadPolicy 0) (lookaheadStrength d) (lookaheadStrength_nonneg d)
      (lookaheadStrength_le_half d) τ hs hfirst t
    change finiteDeficiency _ _ = _ at hf
    cases a
    rw [lookaheadPolicy_effective 0 d t ht] at hf
    simpa [lookaheadStrength, hd, hsd, causalNativeTestExperiment] using hf

/-- A single fixed later native test retains a positive deficit forever. -/
theorem lookahead_immediate_later_deficiency (d : ℕ) (hd : 0 < d)
    {t : ℕ} (ht : 0 < t) :
    finiteDeficiency
      (causalFiniteExperiment (lookaheadPolicy 0).1 (waitProxyResponse (lookaheadStrength d)) t)
      (causalPlanObservationExperiment (d + 1) (waitProxyCanonicalPlan d ())
        (waitProxyResponse (lookaheadStrength d))) = 1 / 4 := by
  have hf := waitProxyPolicyTestDeficiency_eq_of_first (a := ())
    (lookaheadPolicy 0) (lookaheadStrength d) (lookaheadStrength_nonneg d)
    (lookaheadStrength_le_half d) (waitProxyCanonicalPlan d ()) (Nat.lt_succ_self d)
    (waitProxyCanonicalPlan_firstTestsAt d ()) t
  change finiteDeficiency _ _ = _ at hf
  rw [lookaheadPolicy_effective 0 d t ht] at hf
  norm_num [lookaheadStrength, hd] at hf ⊢
  exact hf

theorem lookahead_immediate_not_nativelySufficient (d : ℕ) (hd : 0 < d) :
    ¬ CausalNativelySufficient (waitProxyResponse (lookaheadStrength d)) (lookaheadPolicy 0) := by
  intro h
  obtain ⟨T, hT⟩ := h (d + 1) (1 / 4) (by norm_num)
  have he := hT (T + 1) (by omega) (waitProxyCanonicalPlan d ())
  rw [lookahead_immediate_later_deficiency d hd (Nat.succ_pos T)] at he
  exact (lt_irrefl _ he)

/-- Waiting to the deadline preserves full revelation, hence every native
experiment is exactly simulable from every subsequent acquired prefix. -/
theorem lookahead_delayed_exact (d : ℕ)
    {n : ℕ} (τ : CausalPlan (WaitProxyAction Unit) WaitProxyObservation n)
    {t : ℕ} (ht : d < t) :
    finiteDeficiency
      (causalFiniteExperiment (lookaheadPolicy d).1 (waitProxyResponse (lookaheadStrength d)) t)
      (causalPlanObservationExperiment n τ (waitProxyResponse (lookaheadStrength d))) = 0 := by
  rcases waitProxyPlan_alwaysWait_or_firstTestsAt τ with hall | ⟨s, a, hfirst⟩
  · exact waitProxyNativePlan_alwaysWait_deficiency _
      (causalFiniteExperiment_valid _ (lookaheadPolicy d).2 _
        (waitProxyResponse_valid _ (lookaheadStrength_nonneg d) (lookaheadStrength_le_half d)) t)
      τ _ (lookaheadStrength_nonneg d) (lookaheadStrength_le_half d) hall
  · have hf := waitProxyPolicyTestDeficiency_eq_of_first (a := a)
      (lookaheadPolicy d) (lookaheadStrength d) (lookaheadStrength_nonneg d)
      (lookaheadStrength_le_half d) τ hfirst.1 hfirst t
    change finiteDeficiency _ _ = _ at hf
    cases a
    rw [lookaheadPolicy_effective d d t ht] at hf
    have hs := lookaheadStrength_le_half d s
    simp only [lookaheadStrength, lt_self_iff_false, ↓reduceIte] at hf
    split_ifs at hf <;> norm_num at hf <;> exact hf

theorem lookahead_delayed_nativelySufficient (d : ℕ) :
    CausalNativelySufficient (waitProxyResponse (lookaheadStrength d)) (lookaheadPolicy d) := by
  intro n ε hε
  refine ⟨d + 1, fun t ht τ => ?_⟩
  rw [lookahead_delayed_exact d τ (by omega)]
  exact hε

/-- Every controlled continuation after any test is independent of the world
and of subsequent actions: later local choice cannot undo the first loss. -/
theorem lookahead_after_test_silent (d : ℕ) (θ : Unit → Bool)
    (h : CausalHistory (WaitProxyAction Unit) WaitProxyObservation)
    (hh : waitProxyHasTest h = true) (a : WaitProxyAction Unit)
    (o : WaitProxyObservation) :
    waitProxyResponse (lookaheadStrength d) θ h a o =
      if o = WaitProxyObservation.silent then 1 else 0 := by
  simp [waitProxyResponse, hh]

end
end IdExp
