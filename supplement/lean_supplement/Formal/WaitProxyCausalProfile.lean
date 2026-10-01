import Formal.WaitProxyCausalTrace
import Formal.CausalProfile
import Formal.BinaryBlackwell

/-!
# Literal causal profiles for the hidden wait/proxy class

This module completes the bridge from the checked first-test stopping algebra
to the paper's actual enumerated native-test profile.  Its first layer shows
that a deterministic native plan which first tests coordinate `a` after `s`
silent waits is Blackwell-equivalent to the canonical binary target of
strength `c s`; an always-wait plan is uninformative.  The later layers use
that classification to identify the raw profile range, its product-topology
closure, and its Pareto frontier.
-/

namespace IdExp

open Filter Finset Set Topology
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false


noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

instance : Nonempty (WaitProxyAction A) := ⟨WaitProxyAction.wait⟩

theorem causalPolicyOfPlan_waitProxy_silent
    {n : ℕ}
    (tau : CausalPlan (WaitProxyAction A) WaitProxyObservation n)
    {s : ℕ} (hs : s < n) (act : WaitProxyAction A) :
    causalPolicyOfPlan n tau (waitProxySilentHistory s) act =
      if act = waitProxyPlanSilentAction tau ⟨s, hs⟩ then 1 else 0 := by
  classical
  unfold causalPolicyOfPlan waitProxyPlanSilentAction
  rw [dif_pos (by simpa [waitProxySilentHistory] using hs)]
  congr 2
theorem causalPolicyOfPlan_waitProxy_wait_of_before
    {n : ℕ}
    (tau : CausalPlan (WaitProxyAction A) WaitProxyObservation n)
    {s r : ℕ} (hs : s < n)
    (hfirst : WaitProxyPlanFirstTestsAt tau s a) (hr : r < s) :
    causalPolicyOfPlan n tau (waitProxySilentHistory r)
        WaitProxyAction.wait = 1 := by
  rcases hfirst with ⟨_, _, hbefore⟩
  rw [causalPolicyOfPlan_waitProxy_silent tau (lt_trans hr hs)]
  simp [hbefore r hr]

theorem causalPolicyOfPlan_waitProxy_test_at
    {n : ℕ}
    (tau : CausalPlan (WaitProxyAction A) WaitProxyObservation n)
    {s : ℕ} (hs : s < n)
    (hfirst : WaitProxyPlanFirstTestsAt tau s a) :
    causalPolicyOfPlan n tau (waitProxySilentHistory s)
        (WaitProxyAction.test a) = 1 := by
  rcases hfirst with ⟨_, hat, _⟩
  rw [causalPolicyOfPlan_waitProxy_silent tau hs]
  simp [hat]

theorem causalPolicyOfPlan_waitProxy_wait_at
    {n : ℕ}
    (tau : CausalPlan (WaitProxyAction A) WaitProxyObservation n)
    {s : ℕ} (hs : s < n)
    (hfirst : WaitProxyPlanFirstTestsAt tau s a) :
    causalPolicyOfPlan n tau (waitProxySilentHistory s)
        WaitProxyAction.wait = 0 := by
  rcases hfirst with ⟨_, hat, _⟩
  rw [causalPolicyOfPlan_waitProxy_silent tau hs]
  simp [hat]

theorem causalPolicyOfPlan_waitProxy_other_test_at
    {n : ℕ}
    (tau : CausalPlan (WaitProxyAction A) WaitProxyObservation n)
    {s : ℕ} (hs : s < n)
    (hfirst : WaitProxyPlanFirstTestsAt tau s a) {b : A} (hba : b ≠ a) :
    causalPolicyOfPlan n tau (waitProxySilentHistory s)
        (WaitProxyAction.test b) = 0 := by
  rcases hfirst with ⟨_, hat, _⟩
  rw [causalPolicyOfPlan_waitProxy_silent tau hs]
  simp [hat, hba]

theorem waitProxySurvival_causalPolicyOfPlan_eq_one_of_le
    {n : ℕ}
    (tau : CausalPlan (WaitProxyAction A) WaitProxyObservation n)
    {s : ℕ} (hs : s < n)
    (hfirst : WaitProxyPlanFirstTestsAt tau s a)
    {r : ℕ} (hr : r ≤ s) :
    waitProxySurvival (causalPolicyOfPlan n tau) r = 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [waitProxySurvival_succ, ih (Nat.le_of_succ_le hr)]
      rw [causalPolicyOfPlan_waitProxy_wait_of_before tau hs hfirst
        (Nat.lt_of_succ_le hr)]
      ring

theorem waitProxySurvival_causalPolicyOfPlan_eq_zero_of_test_lt
    {n : ℕ}
    (tau : CausalPlan (WaitProxyAction A) WaitProxyObservation n)
    {s r : ℕ} (hs : s < n)
    (hfirst : WaitProxyPlanFirstTestsAt tau s a) (hsr : s < r) :
    waitProxySurvival (causalPolicyOfPlan n tau) r = 0 := by
  have hzero :
      waitProxySurvival (causalPolicyOfPlan n tau) (s + 1) = 0 := by
    rw [waitProxySurvival_succ,
      waitProxySurvival_causalPolicyOfPlan_eq_one_of_le tau hs hfirst le_rfl,
      causalPolicyOfPlan_waitProxy_wait_at tau hs hfirst]
    ring
  obtain ⟨k, rfl⟩ : ∃ k, r = (s + 1) + k :=
    Nat.exists_eq_add_of_le (Nat.succ_le_iff.2 hsr)
  induction k with
  | zero => simpa using hzero
  | succ k ih =>
      rw [Nat.add_succ, waitProxySurvival_succ, ih (by omega), zero_mul]

theorem waitProxyFirstTestMass_causalPolicyOfPlan
    {n : ℕ}
    (tau : CausalPlan (WaitProxyAction A) WaitProxyObservation n)
    {s : ℕ} (hs : s < n)
    (hfirst : WaitProxyPlanFirstTestsAt tau s a)
    (r : ℕ) (b : A) :
    waitProxyFirstTestMass (causalPolicyOfPlan n tau) r b =
      if r = s ∧ b = a then 1 else 0 := by
  rcases lt_trichotomy r s with hrs | hrs | hrs
  · rw [if_neg (fun h => (ne_of_lt hrs) h.1)]
    unfold waitProxyFirstTestMass
    rw [causalPolicyOfPlan_waitProxy_silent tau (lt_trans hrs hs)]
    rcases hfirst with ⟨_, _, hbefore⟩
    simp [hbefore r hrs]
  · subst r
    by_cases hba : b = a
    · subst b
      rw [if_pos ⟨rfl, rfl⟩]
      simp [waitProxyFirstTestMass,
        waitProxySurvival_causalPolicyOfPlan_eq_one_of_le tau hs hfirst le_rfl,
        causalPolicyOfPlan_waitProxy_test_at tau hs hfirst]
    · rw [if_neg (fun h => hba h.2)]
      simp [waitProxyFirstTestMass,
        waitProxySurvival_causalPolicyOfPlan_eq_one_of_le tau hs hfirst le_rfl,
        causalPolicyOfPlan_waitProxy_other_test_at tau hs hfirst hba]
  · rw [if_neg (fun h => (ne_of_gt hrs) h.1)]
    simp [waitProxyFirstTestMass,
      waitProxySurvival_causalPolicyOfPlan_eq_zero_of_test_lt tau hs hfirst hrs]
theorem waitProxyStoppingExperiment_causalPolicyOfPlan_first
    {n : ℕ}
    (tau : CausalPlan (WaitProxyAction A) WaitProxyObservation n)
    (c : ℕ → ℝ) {s : ℕ} (hs : s < n)
    (hfirst : WaitProxyPlanFirstTestsAt tau s a)
    (theta : A → Bool) (sig : WaitProxyStoppingSignal A n) :
    waitProxyStoppingExperiment (causalPolicyOfPlan n tau) c n theta sig =
      match sig with
      | none => 0
      | some (r, b, x) =>
          if r.val = s ∧ b = a then waitProxyTarget (c s) a theta x else 0 := by
  cases sig with
  | none =>
      simp only [waitProxyStoppingExperiment]
      exact waitProxySurvival_causalPolicyOfPlan_eq_zero_of_test_lt
        tau hs hfirst hs
  | some rbx =>
      rcases rbx with ⟨r, b, x⟩
      simp only [waitProxyStoppingExperiment]
      rw [waitProxyFirstTestMass_causalPolicyOfPlan tau hs hfirst]
      by_cases h : r.val = s ∧ b = a
      · rw [if_pos h]
        rcases h with ⟨hr, rfl⟩
        simp [waitProxyTarget, hr]
      · simp only [if_neg h, zero_mul]

def waitProxyFirstTestEmbed {n : ℕ} (s : Fin n) (a : A) (x : Bool) :
    WaitProxyStoppingSignal A n :=
  some (s, a, x)

def waitProxyFirstTestProject {n : ℕ}
    (sig : WaitProxyStoppingSignal A n) : Bool :=
  match sig with
  | none => false
  | some (_, _, x) => x

@[simp] theorem waitProxyFirstTestProject_embed {n : ℕ}
    (s : Fin n) (a : A) (x : Bool) :
    waitProxyFirstTestProject (waitProxyFirstTestEmbed s a x) = x := rfl

def waitProxyFirstTestEmbedRule {n : ℕ} (s : Fin n) (a : A) :
    Bool → WaitProxyStoppingSignal A n → ℝ :=
  finiteMapRule (waitProxyFirstTestEmbed s a)

def waitProxyFirstTestProjectRule {n : ℕ} :
    WaitProxyStoppingSignal A n → Bool → ℝ :=
  finiteMapRule waitProxyFirstTestProject

theorem waitProxyFirstTestEmbedRule_mem {n : ℕ} (s : Fin n) (a : A) :
    waitProxyFirstTestEmbedRule s a ∈
      stochasticRules Bool (WaitProxyStoppingSignal A n) :=
  finiteMapRule_mem _

theorem waitProxyFirstTestProjectRule_mem {n : ℕ} :
    waitProxyFirstTestProjectRule (A := A) ∈
      stochasticRules (WaitProxyStoppingSignal A n) Bool :=
  finiteMapRule_mem _

theorem finiteDecisionLaw_waitProxyFirstTestEmbedRule
    {n : ℕ}
    (tau : CausalPlan (WaitProxyAction A) WaitProxyObservation n)
    (c : ℕ → ℝ) {s : ℕ} (hs : s < n)
    (hfirst : WaitProxyPlanFirstTestsAt tau s a) :
    finiteDecisionLaw (waitProxyTarget (c s) a)
        (waitProxyFirstTestEmbedRule ⟨s, hs⟩ a) =
      waitProxyStoppingExperiment (causalPolicyOfPlan n tau) c n := by
  classical
  funext theta sig
  rw [waitProxyStoppingExperiment_causalPolicyOfPlan_first
    tau c hs hfirst theta sig]
  unfold finiteDecisionLaw waitProxyFirstTestEmbedRule finiteMapRule
  rw [Fintype.sum_bool]
  cases sig with
  | none =>
      simp [waitProxyFirstTestEmbed]
  | some rbx =>
      rcases rbx with ⟨r, b, x⟩
      by_cases hr : r.val = s
      · have hre : r = ⟨s, hs⟩ := Fin.ext hr
        subst r
        by_cases hb : b = a
        · subst b
          cases x <;> cases htheta : theta a <;>
            simp [waitProxyFirstTestEmbed, waitProxyTarget, htheta]
        · simp [waitProxyFirstTestEmbed, hb]
      · have hre : r ≠ ⟨s, hs⟩ :=
          fun h => hr (congrArg Fin.val h)
        simp [waitProxyFirstTestEmbed, hre, hr]
theorem finiteDecisionLaw_waitProxyFirstTestProjectRule
    {n : ℕ}
    (tau : CausalPlan (WaitProxyAction A) WaitProxyObservation n)
    (c : ℕ → ℝ) {s : ℕ} (hs : s < n)
    (hfirst : WaitProxyPlanFirstTestsAt tau s a) :
    finiteDecisionLaw
        (waitProxyStoppingExperiment (causalPolicyOfPlan n tau) c n)
        waitProxyFirstTestProjectRule =
      waitProxyTarget (c s) a := by
  classical
  funext theta x
  unfold finiteDecisionLaw waitProxyFirstTestProjectRule
  rw [Finset.sum_eq_single
    (waitProxyFirstTestEmbed (⟨s, hs⟩ : Fin n) a x)]
  · rw [waitProxyStoppingExperiment_causalPolicyOfPlan_first
      tau c hs hfirst]
    simp [waitProxyFirstTestEmbed, waitProxyFirstTestProject,
      finiteMapRule]
  · intro sig _ hne
    rw [waitProxyStoppingExperiment_causalPolicyOfPlan_first
      tau c hs hfirst]
    cases sig with
    | none =>
        simp [waitProxyFirstTestProject, finiteMapRule]
    | some rby =>
        rcases rby with ⟨r, b, y⟩
        by_cases hr : r.val = s
        · have hre : r = ⟨s, hs⟩ := Fin.ext hr
          subst r
          by_cases hb : b = a
          · subst b
            have hyx : y ≠ x := by
              intro hy
              subst y
              exact hne rfl
            have hxy : x ≠ y := Ne.symm hyx
            simp [waitProxyFirstTestProject, finiteMapRule, hxy]
          · simp [waitProxyFirstTestProject, finiteMapRule, hb]
        · simp [waitProxyFirstTestProject, finiteMapRule, hr]
  · simp
theorem waitProxyStopping_plan_first_blackwellEquiv
    {n : ℕ}
    (tau : CausalPlan (WaitProxyAction A) WaitProxyObservation n)
    (c : ℕ → ℝ) {s : ℕ} (hs : s < n)
    (hfirst : WaitProxyPlanFirstTestsAt tau s a) :
    FiniteBlackwellLE
        (waitProxyStoppingExperiment (causalPolicyOfPlan n tau) c n)
        (waitProxyTarget (c s) a) ∧
      FiniteBlackwellLE
        (waitProxyTarget (c s) a)
        (waitProxyStoppingExperiment (causalPolicyOfPlan n tau) c n) := by
  constructor
  · exact ⟨waitProxyFirstTestEmbedRule ⟨s, hs⟩ a,
      waitProxyFirstTestEmbedRule_mem ⟨s, hs⟩ a,
      finiteDecisionLaw_waitProxyFirstTestEmbedRule tau c hs hfirst⟩
  · exact ⟨waitProxyFirstTestProjectRule,
      waitProxyFirstTestProjectRule_mem,
      finiteDecisionLaw_waitProxyFirstTestProjectRule tau c hs hfirst⟩

theorem waitProxyNativePlan_first_blackwellEquiv
    {n : ℕ}
    (tau : CausalPlan (WaitProxyAction A) WaitProxyObservation n)
    (c : ℕ → ℝ) (hc0 : ∀ r, 0 ≤ c r)
    (hchalf : ∀ r, c r ≤ 1 / 2)
    {s : ℕ} (hs : s < n)
    (hfirst : WaitProxyPlanFirstTestsAt tau s a) :
    FiniteBlackwellLE
        (causalPlanObservationExperiment n tau (waitProxyResponse c))
        (waitProxyTarget (c s) a) ∧
      FiniteBlackwellLE
        (waitProxyTarget (c s) a)
        (causalPlanObservationExperiment n tau (waitProxyResponse c)) := by
  let pi := causalPolicyOfPlan n tau
  have hpi : IsCausalPolicy pi := isCausalPolicy_causalPolicyOfPlan n tau
  have hobs := causalPlan_full_observation_blackwell_equiv
    n tau (waitProxyResponse c)
  have hstop := waitProxyStopping_causalFiniteExperiment_blackwellEquiv
    pi hpi c hc0 hchalf n
  have hbinary := waitProxyStopping_plan_first_blackwellEquiv tau c hs hfirst
  exact ⟨
    finiteBlackwellLE_trans hobs.1
      (finiteBlackwellLE_trans hstop.2 hbinary.1),
    finiteBlackwellLE_trans hbinary.2
      (finiteBlackwellLE_trans hstop.1 hobs.2)⟩
theorem causalPolicyOfPlan_waitProxy_wait_of_always
    {n : ℕ}
    (tau : CausalPlan (WaitProxyAction A) WaitProxyObservation n)
    (halways : WaitProxyPlanAlwaysWait tau)
    {r : ℕ} (hr : r < n) :
    causalPolicyOfPlan n tau (waitProxySilentHistory r)
        WaitProxyAction.wait = 1 := by
  rw [causalPolicyOfPlan_waitProxy_silent tau hr]
  simp [halways ⟨r, hr⟩]

theorem waitProxySurvival_causalPolicyOfPlan_eq_one_of_always
    {n : ℕ}
    (tau : CausalPlan (WaitProxyAction A) WaitProxyObservation n)
    (halways : WaitProxyPlanAlwaysWait tau)
    {r : ℕ} (hr : r ≤ n) :
    waitProxySurvival (causalPolicyOfPlan n tau) r = 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [waitProxySurvival_succ, ih (Nat.le_of_succ_le hr)]
      rw [causalPolicyOfPlan_waitProxy_wait_of_always tau halways
        (Nat.lt_of_succ_le hr)]
      ring

theorem waitProxyFirstTestMass_causalPolicyOfPlan_eq_zero_of_always
    {n : ℕ}
    (tau : CausalPlan (WaitProxyAction A) WaitProxyObservation n)
    (halways : WaitProxyPlanAlwaysWait tau)
    {r : ℕ} (hr : r < n) (b : A) :
    waitProxyFirstTestMass (causalPolicyOfPlan n tau) r b = 0 := by
  unfold waitProxyFirstTestMass
  rw [waitProxySurvival_causalPolicyOfPlan_eq_one_of_always
    tau halways hr.le]
  rw [causalPolicyOfPlan_waitProxy_silent tau hr]
  simp [halways ⟨r, hr⟩]

theorem waitProxyStoppingExperiment_causalPolicyOfPlan_always
    {n : ℕ}
    (tau : CausalPlan (WaitProxyAction A) WaitProxyObservation n)
    (c : ℕ → ℝ) (halways : WaitProxyPlanAlwaysWait tau)
    (theta : A → Bool) (sig : WaitProxyStoppingSignal A n) :
    waitProxyStoppingExperiment (causalPolicyOfPlan n tau) c n theta sig =
      if sig = none then 1 else 0 := by
  cases sig with
  | none =>
      simp [waitProxyStoppingExperiment,
        waitProxySurvival_causalPolicyOfPlan_eq_one_of_always
          tau halways le_rfl]
  | some rbx =>
      rcases rbx with ⟨r, b, x⟩
      simp [waitProxyStoppingExperiment,
        waitProxyFirstTestMass_causalPolicyOfPlan_eq_zero_of_always
          tau halways r.isLt b]

def waitProxyNoneRule (X : Type*) [Fintype X] {n : ℕ} :
    X → WaitProxyStoppingSignal A n → ℝ :=
  finiteMapRule (fun _ => none)

theorem waitProxyNoneRule_mem (X : Type*) [Fintype X] {n : ℕ} :
    waitProxyNoneRule (A := A) X (n := n) ∈
      stochasticRules X (WaitProxyStoppingSignal A n) :=
  finiteMapRule_mem _

theorem finiteDecisionLaw_waitProxyNoneRule
    {X : Type*} [Fintype X]
    (E : FiniteExperiment (A → Bool) X) (hE : IsFiniteExperiment E)
    {n : ℕ}
    (tau : CausalPlan (WaitProxyAction A) WaitProxyObservation n)
    (c : ℕ → ℝ) (halways : WaitProxyPlanAlwaysWait tau) :
    finiteDecisionLaw E (waitProxyNoneRule (A := A) X (n := n)) =
      waitProxyStoppingExperiment (causalPolicyOfPlan n tau) c n := by
  classical
  funext theta sig
  rw [waitProxyStoppingExperiment_causalPolicyOfPlan_always
    tau c halways theta sig]
  unfold finiteDecisionLaw waitProxyNoneRule finiteMapRule
  by_cases hsig : sig = none
  · subst sig
    simp [(hE theta).2]
  · simp [hsig]

theorem waitProxyNativePlan_alwaysWait_deficiency
    {X : Type*} [Fintype X]
    (E : FiniteExperiment (A → Bool) X) (hE : IsFiniteExperiment E)
    {n : ℕ}
    (tau : CausalPlan (WaitProxyAction A) WaitProxyObservation n)
    (c : ℕ → ℝ) (hc0 : ∀ r, 0 ≤ c r)
    (hchalf : ∀ r, c r ≤ 1 / 2)
    (halways : WaitProxyPlanAlwaysWait tau) :
    finiteDeficiency E
        (causalPlanObservationExperiment n tau (waitProxyResponse c)) = 0 := by
  apply finiteDeficiency_eq_zero_of_finiteBlackwellLE
  let pi := causalPolicyOfPlan n tau
  have hpi : IsCausalPolicy pi := isCausalPolicy_causalPolicyOfPlan n tau
  have hobs := causalPlan_full_observation_blackwell_equiv
    n tau (waitProxyResponse c)
  have hstop := waitProxyStopping_causalFiniteExperiment_blackwellEquiv
    pi hpi c hc0 hchalf n
  apply finiteBlackwellLE_trans
    (finiteBlackwellLE_trans hobs.1 hstop.2)
  exact ⟨waitProxyNoneRule (A := A) X,
    waitProxyNoneRule_mem (A := A) X,
    finiteDecisionLaw_waitProxyNoneRule E hE tau c halways⟩
theorem waitProxyPolicyTestDeficiency_eq_of_first
    (pi : ValidCausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (c : ℕ → ℝ) (hc0 : ∀ r, 0 ≤ c r)
    (hchalf : ∀ r, c r ≤ 1 / 2)
    {n s : ℕ}
    (tau : CausalPlan (WaitProxyAction A) WaitProxyObservation n)
    (hs : s < n) (hfirst : WaitProxyPlanFirstTestsAt tau s a)
    (t : ℕ) :
    causalPolicyTestDeficiency pi (waitProxyResponse c) ⟨n, tau⟩ t =
      max (c s - waitProxyEffectiveWeightFinite pi.1 c t a / 2) 0 := by
  change finiteDeficiency
      (causalFiniteExperiment pi.1 (waitProxyResponse c) t)
      (causalPlanObservationExperiment n tau (waitProxyResponse c)) = _
  rw [finiteDeficiency_eq_of_target_blackwellEquiv
    (causalFiniteExperiment pi.1 (waitProxyResponse c) t)
    (causalPlanObservationExperiment n tau (waitProxyResponse c))
    (waitProxyTarget (c s) a)
    (causalFiniteExperiment_valid pi.1 pi.2 _
      (waitProxyResponse_valid c hc0 hchalf) t)
    (causalPlanObservationExperiment_valid n tau _
      (waitProxyResponse_valid c hc0 hchalf))
    (waitProxyTarget_valid (hc0 s) (hchalf s) a)
    (waitProxyNativePlan_first_blackwellEquiv
      tau c hc0 hchalf hs hfirst).1
    (waitProxyNativePlan_first_blackwellEquiv
      tau c hc0 hchalf hs hfirst).2]
  exact causalFiniteExperiment_waitProxy_deficiency
    pi.1 pi.2 c hc0 hchalf t (hc0 s) (hchalf s) a

theorem waitProxyPolicyTestDeficiency_eq_zero_of_always
    (pi : ValidCausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (c : ℕ → ℝ) (hc0 : ∀ r, 0 ≤ c r)
    (hchalf : ∀ r, c r ≤ 1 / 2)
    {n : ℕ}
    (tau : CausalPlan (WaitProxyAction A) WaitProxyObservation n)
    (halways : WaitProxyPlanAlwaysWait tau)
    (t : ℕ) :
    causalPolicyTestDeficiency pi (waitProxyResponse c) ⟨n, tau⟩ t = 0 := by
  exact waitProxyNativePlan_alwaysWait_deficiency
    (causalFiniteExperiment pi.1 (waitProxyResponse c) t)
    (causalFiniteExperiment_valid pi.1 pi.2 _
      (waitProxyResponse_valid c hc0 hchalf) t)
    tau c hc0 hchalf halways

theorem waitProxyPlan_exists_first_of_not_always
    {n : ℕ}
    (tau : CausalPlan (WaitProxyAction A) WaitProxyObservation n)
    (hnot : ¬ WaitProxyPlanAlwaysWait tau) :
    ∃ p : ℕ × A, WaitProxyPlanFirstTestsAt tau p.1 p.2 := by
  rcases waitProxyPlan_alwaysWait_or_firstTestsAt tau with halways | hfirst
  · exact (hnot halways).elim
  · rcases hfirst with ⟨s, a, hs⟩
    exact ⟨(s, a), hs⟩

noncomputable def waitProxyPlanCoordinate {n : ℕ}
    (tau : CausalPlan (WaitProxyAction A) WaitProxyObservation n) :
    Option (ℕ × A) := by
  classical
  exact if h : WaitProxyPlanAlwaysWait tau then none
    else some (Classical.choose
      (waitProxyPlan_exists_first_of_not_always tau h))

theorem waitProxyPlanCoordinate_eq_none
    {n : ℕ}
    (tau : CausalPlan (WaitProxyAction A) WaitProxyObservation n)
    (halways : WaitProxyPlanAlwaysWait tau) :
    waitProxyPlanCoordinate tau = none := by
  simp [waitProxyPlanCoordinate, halways]

theorem waitProxyPlanCoordinate_eq_some
    {n : ℕ}
    (tau : CausalPlan (WaitProxyAction A) WaitProxyObservation n)
    {s : ℕ} (hfirst : WaitProxyPlanFirstTestsAt tau s a) :
    waitProxyPlanCoordinate tau = some (s, a) := by
  have hnot : ¬ WaitProxyPlanAlwaysWait tau := by
    intro halways
    rcases hfirst with ⟨hs, hat, _⟩
    have hw := halways ⟨s, hs⟩
    rw [hat] at hw
    cases hw
  rw [waitProxyPlanCoordinate, dif_neg hnot]
  let p : ℕ × A :=
    Classical.choose (waitProxyPlan_exists_first_of_not_always tau hnot)
  have hp : WaitProxyPlanFirstTestsAt tau p.1 p.2 :=
    Classical.choose_spec (waitProxyPlan_exists_first_of_not_always tau hnot)
  have hu := waitProxyPlanFirstTestsAt_unique tau hp hfirst
  change some p = some (s, a)
  congr 1
  exact Prod.ext hu.1 hu.2

noncomputable def waitProxyCausalCoordinate
    (c : ℕ → ℝ) (z : A → ℝ)
    (q : CausalNativeTest (WaitProxyAction A) WaitProxyObservation) : ℝ :=
  match waitProxyPlanCoordinate q.2 with
  | none => 0
  | some p => waitProxyProfile c z p

theorem waitProxyCausalCoordinate_eq_zero_of_always
    (c : ℕ → ℝ) (z : A → ℝ)
    {n : ℕ}
    (tau : CausalPlan (WaitProxyAction A) WaitProxyObservation n)
    (halways : WaitProxyPlanAlwaysWait tau) :
    waitProxyCausalCoordinate c z ⟨n, tau⟩ = 0 := by
  simp [waitProxyCausalCoordinate,
    waitProxyPlanCoordinate_eq_none tau halways]

theorem waitProxyCausalCoordinate_eq_of_first
    (c : ℕ → ℝ) (z : A → ℝ)
    {n s : ℕ}
    (tau : CausalPlan (WaitProxyAction A) WaitProxyObservation n)
    (hfirst : WaitProxyPlanFirstTestsAt tau s a) :
    waitProxyCausalCoordinate c z ⟨n, tau⟩ =
      max (c s - z a / 2) 0 := by
  simp [waitProxyCausalCoordinate,
    waitProxyPlanCoordinate_eq_some tau hfirst, waitProxyProfile]

theorem waitProxyPolicyProfileValue_eq
    (pi : ValidCausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (c : ℕ → ℝ) (hc0 : ∀ r, 0 ≤ c r)
    (hchalf : ∀ r, c r ≤ 1 / 2)
    (e : ℕ ≃ CausalNativeTest (WaitProxyAction A) WaitProxyObservation)
    (j : ℕ) :
    causalPolicyProfileValue pi (waitProxyResponse c) e j =
      waitProxyCausalCoordinate c (waitProxyEffectiveWeight pi.1 c) (e j) := by
  apply tendsto_nhds_unique
    (causalPolicyProfileValue_tendsto pi _
      (waitProxyResponse_valid c hc0 hchalf) e j)
  rcases hq : e j with ⟨n, tau⟩
  rcases waitProxyPlan_alwaysWait_or_firstTestsAt tau with halways | hfirst
  · have hcoord :
        waitProxyCausalCoordinate c (waitProxyEffectiveWeight pi.1 c)
          (⟨n, tau⟩ : CausalNativeTest (WaitProxyAction A) WaitProxyObservation) = 0 :=
      waitProxyCausalCoordinate_eq_zero_of_always
        c (waitProxyEffectiveWeight pi.1 c) tau halways
    rw [hcoord]
    apply tendsto_const_nhds.congr'
    exact Filter.Eventually.of_forall fun t => by
      exact (waitProxyPolicyTestDeficiency_eq_zero_of_always
        pi c hc0 hchalf tau halways t).symm
  · rcases hfirst with ⟨s, a, hs, hat, hbefore⟩
    have hfirst' : WaitProxyPlanFirstTestsAt tau s a := ⟨hs, hat, hbefore⟩
    have hcoord :
        waitProxyCausalCoordinate c (waitProxyEffectiveWeight pi.1 c)
          (⟨n, tau⟩ : CausalNativeTest (WaitProxyAction A) WaitProxyObservation) =
            max (c s - waitProxyEffectiveWeight pi.1 c a / 2) 0 :=
      waitProxyCausalCoordinate_eq_of_first
        c (waitProxyEffectiveWeight pi.1 c) tau hfirst'
    rw [hcoord]
    refine (tendsto_causalFiniteExperiment_waitProxy_deficiency
      pi.1 pi.2 c hc0 hchalf (hc0 s) (hchalf s) a).congr' ?_
    exact Filter.Eventually.of_forall fun t => by
      change finiteDeficiency
          (causalFiniteExperiment pi.1 (waitProxyResponse c) t)
          (waitProxyTarget (c s) a) =
        causalPolicyTestDeficiency pi (waitProxyResponse c) ⟨n, tau⟩ t
      rw [causalFiniteExperiment_waitProxy_deficiency
        pi.1 pi.2 c hc0 hchalf t (hc0 s) (hchalf s) a,
        waitProxyPolicyTestDeficiency_eq_of_first
          pi c hc0 hchalf tau hs hfirst' t]


theorem waitProxyCausalCoordinate_nonneg
    (c : ℕ → ℝ) (z : A → ℝ)
    (q : CausalNativeTest (WaitProxyAction A) WaitProxyObservation) :
    0 ≤ waitProxyCausalCoordinate c z q := by
  unfold waitProxyCausalCoordinate
  cases h : waitProxyPlanCoordinate q.2 with
  | none => simp [h]
  | some p =>
      rcases p with ⟨s, a⟩
      simp [h, waitProxyProfile]

theorem waitProxyCausalCoordinate_le_one
    (c : ℕ → ℝ) (hchalf : ∀ s, c s ≤ 1 / 2)
    (z : A → ℝ) (hz0 : ∀ a, 0 ≤ z a)
    (q : CausalNativeTest (WaitProxyAction A) WaitProxyObservation) :
    waitProxyCausalCoordinate c z q ≤ 1 := by
  unfold waitProxyCausalCoordinate
  cases h : waitProxyPlanCoordinate q.2 with
  | none => simp [h]
  | some p =>
      rcases p with ⟨s, a⟩
      simp only [h, waitProxyProfile]
      apply max_le
      · linarith [hchalf s, hz0 a]
      · norm_num

noncomputable def waitProxyCausalWeightProfile
    (c : ℕ → ℝ)
    (e : ℕ ≃ CausalNativeTest (WaitProxyAction A) WaitProxyObservation)
    (z : A → ℝ) : ProfileCube :=
  fun j =>
    ⟨min (waitProxyCausalCoordinate c z (e j)) 1,
      le_min (waitProxyCausalCoordinate_nonneg c z (e j)) (by norm_num),
      min_le_right _ _⟩

@[simp] theorem waitProxyCausalWeightProfile_coe
    (c : ℕ → ℝ)
    (e : ℕ ≃ CausalNativeTest (WaitProxyAction A) WaitProxyObservation)
    (z : A → ℝ) (j : ℕ) :
    ((waitProxyCausalWeightProfile c e z j : Set.Icc (0 : ℝ) 1) : ℝ) =
      min (waitProxyCausalCoordinate c z (e j)) 1 := rfl

theorem waitProxyCausalWeightProfile_coe_eq_coordinate
    (c : ℕ → ℝ) (hchalf : ∀ s, c s ≤ 1 / 2)
    (e : ℕ ≃ CausalNativeTest (WaitProxyAction A) WaitProxyObservation)
    (z : A → ℝ) (hz0 : ∀ a, 0 ≤ z a) (j : ℕ) :
    ((waitProxyCausalWeightProfile c e z j : Set.Icc (0 : ℝ) 1) : ℝ) =
      waitProxyCausalCoordinate c z (e j) := by
  rw [waitProxyCausalWeightProfile_coe, min_eq_left]
  exact waitProxyCausalCoordinate_le_one c hchalf z hz0 (e j)

theorem continuous_waitProxyCausalWeightProfile
    (c : ℕ → ℝ)
    (e : ℕ ≃ CausalNativeTest (WaitProxyAction A) WaitProxyObservation) :
    Continuous (waitProxyCausalWeightProfile c e) := by
  apply continuous_pi
  intro j
  apply Continuous.subtype_mk
  change Continuous (fun z : A → ℝ =>
    min (waitProxyCausalCoordinate c z (e j)) 1)
  apply Continuous.min
  · unfold waitProxyCausalCoordinate
    cases h : waitProxyPlanCoordinate (e j).2 with
    | none =>
        simp only [h]
        exact continuous_const
    | some p =>
        rcases p with ⟨s, a⟩
        simp only [h, waitProxyProfile]
        fun_prop
  · exact continuous_const

theorem causalPolicyProfile_eq_waitProxyCausalWeightProfile
    (pi : ValidCausalPolicy (WaitProxyAction A) WaitProxyObservation)
    (c : ℕ → ℝ) (hc0 : ∀ r, 0 ≤ c r)
    (hchalf : ∀ r, c r ≤ 1 / 2)
    (e : ℕ ≃ CausalNativeTest (WaitProxyAction A) WaitProxyObservation) :
    causalPolicyProfile (waitProxyResponse c)
        (waitProxyResponse_valid c hc0 hchalf) e pi =
      waitProxyCausalWeightProfile c e (waitProxyEffectiveWeight pi.1 c) := by
  funext j
  apply Subtype.ext
  rw [causalPolicyProfile_coe,
    waitProxyCausalWeightProfile_coe_eq_coordinate c hchalf]
  · exact waitProxyPolicyProfileValue_eq pi c hc0 hchalf e j
  · exact waitProxyEffectiveWeight_nonneg pi.1 pi.2 c hc0

def waitProxyCausalRawProfiles
    (c : ℕ → ℝ)
    (e : ℕ ≃ CausalNativeTest (WaitProxyAction A) WaitProxyObservation) :
    Set ProfileCube :=
  {p | ∃ z, IsStrictSubprobability z ∧
    p = waitProxyCausalWeightProfile c e z}

def waitProxyCausalCompletedProfiles
    (c : ℕ → ℝ)
    (e : ℕ ≃ CausalNativeTest (WaitProxyAction A) WaitProxyObservation) :
    Set ProfileCube :=
  {p | ∃ z, IsSubprobability z ∧
    p = waitProxyCausalWeightProfile c e z}

theorem causalPolicyProfiles_waitProxy_eq_raw
    (c : ℕ → ℝ) (hc0 : ∀ r, 0 ≤ c r)
    (hclt : ∀ r, c r < 1 / 2)
    (hcofinal : ∀ x < (1 / 2 : ℝ), ∃ s, x < c s)
    (e : ℕ ≃ CausalNativeTest (WaitProxyAction A) WaitProxyObservation) :
    causalPolicyProfiles (waitProxyResponse c)
        (waitProxyResponse_valid c hc0 (fun r => (hclt r).le)) e =
      waitProxyCausalRawProfiles c e := by
  ext p
  constructor
  · rintro ⟨pi, rfl⟩
    let z := waitProxyEffectiveWeight pi.1 c
    have hz : IsStrictSubprobability z :=
      waitProxyEffectiveWeight_strictSubprobability pi.1 pi.2 c hc0 hclt
    refine ⟨z, hz, ?_⟩
    exact causalPolicyProfile_eq_waitProxyCausalWeightProfile
      pi c hc0 (fun r => (hclt r).le) e
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨pi, hpi, hweight⟩ :=
      exists_waitProxyPolicy_effectiveWeight_eq c hcofinal z hz
    let vpi : ValidCausalPolicy (WaitProxyAction A) WaitProxyObservation :=
      ⟨pi, hpi⟩
    refine ⟨vpi, ?_⟩
    rw [causalPolicyProfile_eq_waitProxyCausalWeightProfile
      vpi c hc0 (fun r => (hclt r).le) e]
    rw [hweight]


theorem shrinkWaitProxyCausalWeightProfile_tendsto
    (c : ℕ → ℝ)
    (e : ℕ ≃ CausalNativeTest (WaitProxyAction A) WaitProxyObservation)
    (z : A → ℝ) :
    Filter.Tendsto
      (fun n => waitProxyCausalWeightProfile c e
        (shrinkWaitProxyWeight n z))
      Filter.atTop (𝓝 (waitProxyCausalWeightProfile c e z)) :=
  ((continuous_waitProxyCausalWeightProfile c e).tendsto z).comp
    (shrinkWaitProxyWeight_tendsto z)

theorem waitProxyCausalCompleted_subset_closure_raw
    (c : ℕ → ℝ)
    (e : ℕ ≃ CausalNativeTest (WaitProxyAction A) WaitProxyObservation) :
    waitProxyCausalCompletedProfiles c e ⊆
      closure (waitProxyCausalRawProfiles c e) := by
  intro p hp
  rcases hp with ⟨z, hz, rfl⟩
  rw [mem_closure_iff_seq_limit]
  refine ⟨fun n => waitProxyCausalWeightProfile c e
      (shrinkWaitProxyWeight n z), ?_,
    shrinkWaitProxyCausalWeightProfile_tendsto c e z⟩
  intro n
  exact ⟨shrinkWaitProxyWeight n z,
    shrinkWaitProxyWeight_strict n z hz, rfl⟩

theorem closure_waitProxyCausalRaw_subset_completed
    (c : ℕ → ℝ)
    (e : ℕ ≃ CausalNativeTest (WaitProxyAction A) WaitProxyObservation) :
    closure (waitProxyCausalRawProfiles c e) ⊆
      waitProxyCausalCompletedProfiles c e := by
  intro p hp
  rw [mem_closure_iff_seq_limit] at hp
  obtain ⟨pseq, hpraw, hptend⟩ := hp
  choose z hz hzp using hpraw
  have hzle (n : ℕ) (a : A) : z n a ≤ 1 := by
    have hsingle : z n a ≤ ∑ b, z n b :=
      Finset.single_le_sum (fun b _ => (hz n).1 b) (Finset.mem_univ a)
    exact hsingle.trans (hz n).2.le
  let zcube : ℕ → (A → Set.Icc (0 : ℝ) 1) :=
    fun n a => ⟨z n a, (hz n).1 a, hzle n a⟩
  obtain ⟨w, -, phi, hphi, hlim⟩ :=
    isCompact_univ.tendsto_subseq (fun n => Set.mem_univ (zcube n))
  let zlim : A → ℝ := fun a => (w a : ℝ)
  have hzlim : Filter.Tendsto (fun n => z (phi n))
      Filter.atTop (𝓝 zlim) := by
    rw [tendsto_pi_nhds]
    intro a
    have hcoord :=
      ((continuous_subtype_val.comp (continuous_apply a)).tendsto w).comp hlim
    simpa [Function.comp_def, zcube, zlim] using hcoord
  have hsumlim : Filter.Tendsto (fun n => ∑ a, z (phi n) a)
      Filter.atTop (𝓝 (∑ a, zlim a)) := by
    simpa using tendsto_finsetSum (Finset.univ : Finset A)
      (fun a _ => (tendsto_pi_nhds.1 hzlim) a)
  have hzlimSub : IsSubprobability zlim := by
    constructor
    · intro a
      exact (w a).property.1
    · exact le_of_tendsto hsumlim
        (Filter.Eventually.of_forall fun n => (hz (phi n)).2.le)
  have hpseqSub : Filter.Tendsto (fun n => pseq (phi n))
      Filter.atTop (𝓝 p) :=
    hptend.comp hphi.tendsto_atTop
  have hpseqEq : (fun n => pseq (phi n)) =
      (fun n => waitProxyCausalWeightProfile c e (z (phi n))) := by
    funext n
    exact hzp (phi n)
  rw [hpseqEq] at hpseqSub
  have hprofileLim :
      Filter.Tendsto
        (fun n => waitProxyCausalWeightProfile c e (z (phi n)))
        Filter.atTop (𝓝 (waitProxyCausalWeightProfile c e zlim)) :=
    ((continuous_waitProxyCausalWeightProfile c e).tendsto zlim).comp hzlim
  have heq : p = waitProxyCausalWeightProfile c e zlim :=
    tendsto_nhds_unique hpseqSub hprofileLim
  exact ⟨zlim, hzlimSub, heq⟩

theorem closure_waitProxyCausalRaw_eq_completed
    (c : ℕ → ℝ)
    (e : ℕ ≃ CausalNativeTest (WaitProxyAction A) WaitProxyObservation) :
    closure (waitProxyCausalRawProfiles c e) =
      waitProxyCausalCompletedProfiles c e := by
  apply Set.Subset.antisymm
  · exact closure_waitProxyCausalRaw_subset_completed c e
  · exact waitProxyCausalCompleted_subset_closure_raw c e

theorem causalProfileClosure_waitProxy_eq_completed
    (c : ℕ → ℝ) (hc0 : ∀ r, 0 ≤ c r)
    (hclt : ∀ r, c r < 1 / 2)
    (hcofinal : ∀ x < (1 / 2 : ℝ), ∃ s, x < c s)
    (e : ℕ ≃ CausalNativeTest (WaitProxyAction A) WaitProxyObservation) :
    causalProfileClosure (waitProxyResponse c)
        (waitProxyResponse_valid c hc0 (fun r => (hclt r).le)) e =
      waitProxyCausalCompletedProfiles c e := by
  unfold causalProfileClosure
  rw [causalPolicyProfiles_waitProxy_eq_raw c hc0 hclt hcofinal e,
    closure_waitProxyCausalRaw_eq_completed c e]





def waitProxyCanonicalPlan (s : ℕ) (a : A) :
    CausalPlan (WaitProxyAction A) WaitProxyObservation (s + 1) :=
  fun x => if x.1.val < s then WaitProxyAction.wait
    else WaitProxyAction.test a

theorem waitProxyCanonicalPlan_firstTestsAt (s : ℕ) (a : A) :
    WaitProxyPlanFirstTestsAt (waitProxyCanonicalPlan s a) s a := by
  refine ⟨Nat.lt_succ_self s, ?_, ?_⟩
  · simp [waitProxyPlanSilentAction, waitProxyCanonicalPlan,
      causalDecisionPointOfHistory, waitProxySilentHistory]
  · intro r hr
    simp [waitProxyPlanSilentAction, waitProxyCanonicalPlan,
      causalDecisionPointOfHistory, waitProxySilentHistory, hr]

theorem waitProxyCausalCoordinate_canonical
    (c : ℕ → ℝ) (z : A → ℝ) (s : ℕ) (a : A) :
    waitProxyCausalCoordinate c z
        ⟨s + 1, waitProxyCanonicalPlan s a⟩ =
      waitProxyProfile c z (s, a) := by
  rw [waitProxyCausalCoordinate_eq_of_first
    c z (waitProxyCanonicalPlan s a)
    (waitProxyCanonicalPlan_firstTestsAt s a)]
  rfl

theorem waitProxyCausalCoordinate_antitone
    (c : ℕ → ℝ) {z u : A → ℝ}
    (hzu : ∀ a, z a ≤ u a)
    (q : CausalNativeTest (WaitProxyAction A) WaitProxyObservation) :
    waitProxyCausalCoordinate c u q ≤ waitProxyCausalCoordinate c z q := by
  unfold waitProxyCausalCoordinate
  cases h : waitProxyPlanCoordinate q.2 with
  | none => simp
  | some p =>
      exact waitProxyProfile_antitone c hzu p

theorem waitProxyCausalWeightProfile_antitone
    (c : ℕ → ℝ)
    (e : ℕ ≃ CausalNativeTest (WaitProxyAction A) WaitProxyObservation)
    {z u : A → ℝ} (hzu : ∀ a, z a ≤ u a) :
    waitProxyCausalWeightProfile c e u ≤
      waitProxyCausalWeightProfile c e z := by
  intro j
  change min (waitProxyCausalCoordinate c u (e j)) 1 ≤
    min (waitProxyCausalCoordinate c z (e j)) 1
  exact min_le_min
    (waitProxyCausalCoordinate_antitone c hzu (e j)) le_rfl

theorem weight_le_of_waitProxyCausalWeightProfile_le
    (c : ℕ → ℝ) (hchalf : ∀ s, c s ≤ 1 / 2)
    (hcofinal : ∀ x < (1 / 2 : ℝ), ∃ s, x < c s)
    (e : ℕ ≃ CausalNativeTest (WaitProxyAction A) WaitProxyObservation)
    {u v : A → ℝ}
    (hu0 : ∀ a, 0 ≤ u a) (hv0 : ∀ a, 0 ≤ v a)
    (hv1 : ∀ a, v a ≤ 1)
    (hprof : waitProxyCausalWeightProfile c e u ≤
      waitProxyCausalWeightProfile c e v) :
    ∀ a, v a ≤ u a := by
  apply weight_le_of_waitProxyProfile_le c hcofinal hu0 hv1
  rintro ⟨s, a⟩
  have hj := hprof (e.symm
    (⟨s + 1, waitProxyCanonicalPlan s a⟩ :
      CausalNativeTest (WaitProxyAction A) WaitProxyObservation))
  change
    ((waitProxyCausalWeightProfile c e u
      (e.symm ⟨s + 1, waitProxyCanonicalPlan s a⟩) :
        Set.Icc (0 : ℝ) 1) : ℝ) ≤
    ((waitProxyCausalWeightProfile c e v
      (e.symm ⟨s + 1, waitProxyCanonicalPlan s a⟩) :
        Set.Icc (0 : ℝ) 1) : ℝ) at hj
  rw [waitProxyCausalWeightProfile_coe_eq_coordinate c hchalf e u hu0,
    waitProxyCausalWeightProfile_coe_eq_coordinate c hchalf e v hv0,
    e.apply_symm_apply, waitProxyCausalCoordinate_canonical,
    waitProxyCausalCoordinate_canonical] at hj
  exact hj

def waitProxyCausalFrontierProfiles
    (c : ℕ → ℝ)
    (e : ℕ ≃ CausalNativeTest (WaitProxyAction A) WaitProxyObservation) :
    Set ProfileCube :=
  {p | ∃ v, IsDist v ∧ p = waitProxyCausalWeightProfile c e v}

theorem waitProxySubprobability_le_one
    {z : A → ℝ} (hz : IsSubprobability z) (a : A) :
    z a ≤ 1 := by
  exact (Finset.single_le_sum (fun b _ => hz.1 b)
    (Finset.mem_univ a)).trans hz.2


theorem exists_waitProxyCausalFrontierProfile_le
    (c : ℕ → ℝ)
    (hcofinal : ∀ x < (1 / 2 : ℝ), ∃ s, x < c s)
    (e : ℕ ≃ CausalNativeTest (WaitProxyAction A) WaitProxyObservation)
    {p : ProfileCube} (hp : p ∈ waitProxyCausalCompletedProfiles c e) :
    ∃ m ∈ waitProxyCausalFrontierProfiles c e, m ≤ p := by
  rcases hp with ⟨z, hz, rfl⟩
  obtain ⟨u, hu, hprof⟩ :=
    exists_probability_dominating_waitProxyProfile c z hz
  have hzu : ∀ a, z a ≤ u a :=
    weight_le_of_waitProxyProfile_le c hcofinal hu.1
      (waitProxySubprobability_le_one hz) hprof
  exact ⟨waitProxyCausalWeightProfile c e u,
    ⟨u, hu, rfl⟩,
    waitProxyCausalWeightProfile_antitone c e hzu⟩

theorem waitProxyCausalFrontierProfile_minimal
    (c : ℕ → ℝ) (hchalf : ∀ s, c s ≤ 1 / 2)
    (hcofinal : ∀ x < (1 / 2 : ℝ), ∃ s, x < c s)
    (e : ℕ ≃ CausalNativeTest (WaitProxyAction A) WaitProxyObservation)
    {m : ProfileCube} (hm : m ∈ waitProxyCausalFrontierProfiles c e) :
    m ∈ waitProxyCausalCompletedProfiles c e ∧
      ∀ q ∈ waitProxyCausalCompletedProfiles c e,
        q ≤ m → m ≤ q := by
  rcases hm with ⟨v, hv, rfl⟩
  have hvsub : IsSubprobability v := ⟨hv.1, hv.2.le⟩
  refine ⟨⟨v, hvsub, rfl⟩, ?_⟩
  rintro q ⟨z, hz, rfl⟩ hdom
  have hvlez : ∀ a, v a ≤ z a :=
    weight_le_of_waitProxyCausalWeightProfile_le
      c hchalf hcofinal e hz.1 hv.1
      (fun a => waitProxySubprobability_le_one hvsub a) hdom
  have hsumz : ∑ a, z a = 1 := by
    apply le_antisymm hz.2
    rw [← hv.2]
    exact Finset.sum_le_sum fun a _ => hvlez a
  have hzv : z = v := by
    apply funext
    have hall := (Finset.sum_eq_sum_iff_of_le
      (s := (Finset.univ : Finset A)) (fun a _ => hvlez a)).mp
        (by rw [hsumz, hv.2])
    exact fun a => (hall a (Finset.mem_univ a)).symm
  subst z
  exact le_rfl

theorem waitProxyCausal_paretoFrontier_eq
    (c : ℕ → ℝ) (hchalf : ∀ s, c s ≤ 1 / 2)
    (hcofinal : ∀ x < (1 / 2 : ℝ), ∃ s, x < c s)
    (e : ℕ ≃ CausalNativeTest (WaitProxyAction A) WaitProxyObservation) :
    ({m : ProfileCube | m ∈ waitProxyCausalCompletedProfiles c e ∧
      ∀ q ∈ waitProxyCausalCompletedProfiles c e,
        q ≤ m → m ≤ q} : Set ProfileCube) =
      waitProxyCausalFrontierProfiles c e := by
  ext m
  constructor
  · rintro ⟨hm, hmin⟩
    obtain ⟨f, hf, hfm⟩ :=
      exists_waitProxyCausalFrontierProfile_le c hcofinal e hm
    have hmf := hmin f
      (waitProxyCausalFrontierProfile_minimal
        c hchalf hcofinal e hf).1 hfm
    have heq : m = f :=
      le_antisymm hmf hfm
    exact heq ▸ hf
  · intro hm
    exact waitProxyCausalFrontierProfile_minimal
      c hchalf hcofinal e hm

theorem causalParetoFrontier_waitProxy_eq
    (c : ℕ → ℝ) (hc0 : ∀ r, 0 ≤ c r)
    (hclt : ∀ r, c r < 1 / 2)
    (hcofinal : ∀ x < (1 / 2 : ℝ), ∃ s, x < c s)
    (e : ℕ ≃ CausalNativeTest (WaitProxyAction A) WaitProxyObservation) :
    causalParetoFrontier (waitProxyResponse c)
        (waitProxyResponse_valid c hc0 (fun r => (hclt r).le)) e =
      waitProxyCausalFrontierProfiles c e := by
  unfold causalParetoFrontier
  rw [causalProfileClosure_waitProxy_eq_completed
      c hc0 hclt hcofinal e,
    waitProxyCausal_paretoFrontier_eq
      c (fun r => (hclt r).le) hcofinal e]


theorem waitProxyCausalWeightProfile_injectiveOn_probability
    (c : ℕ → ℝ) (hchalf : ∀ s, c s ≤ 1 / 2)
    (hcofinal : ∀ x < (1 / 2 : ℝ), ∃ s, x < c s)
    (e : ℕ ≃ CausalNativeTest (WaitProxyAction A) WaitProxyObservation) :
    Set.InjOn (waitProxyCausalWeightProfile c e)
      {v : A → ℝ | IsDist v} := by
  intro u hu v hv heq
  apply waitProxyProfile_probability_antichain c hcofinal hu hv
  rintro ⟨s, a⟩
  have h := congrArg
    (fun p : ProfileCube =>
      ((p (e.symm
        (⟨s + 1, waitProxyCanonicalPlan s a⟩ :
          CausalNativeTest (WaitProxyAction A) WaitProxyObservation)) :
            Set.Icc (0 : ℝ) 1) : ℝ)) heq
  rw [waitProxyCausalWeightProfile_coe_eq_coordinate c hchalf e u hu.1,
    waitProxyCausalWeightProfile_coe_eq_coordinate c hchalf e v hv.1,
    e.apply_symm_apply, waitProxyCausalCoordinate_canonical,
    waitProxyCausalCoordinate_canonical] at h
  exact h.le

/-- The wait--proxy frontier contains an injective copy of the real unit
interval.  This makes the continuum-sized family in the causal construction
literal, without identifying the frontier merely up to its simplex
parameterization. -/
theorem exists_injective_unitInterval_to_causalParetoFrontier_waitProxy
    [Nontrivial A]
    (c : ℕ → ℝ) (hc0 : ∀ r, 0 ≤ c r)
    (hclt : ∀ r, c r < 1 / 2)
    (hcofinal : ∀ x < (1 / 2 : ℝ), ∃ s, x < c s)
    (e : ℕ ≃ CausalNativeTest (WaitProxyAction A) WaitProxyObservation) :
    ∃ f : Set.Icc (0 : ℝ) 1 →
        {p : ProfileCube // p ∈ causalParetoFrontier (waitProxyResponse c)
          (waitProxyResponse_valid c hc0 (fun r => (hclt r).le)) e},
      Function.Injective f := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne A
  let v : Set.Icc (0 : ℝ) 1 → A → ℝ := fun x q =>
    (if q = a then (x : ℝ) else 0) +
      (if q = b then 1 - (x : ℝ) else 0)
  have hv : ∀ x, IsDist (v x) := by
    intro x
    constructor
    · intro q
      dsimp [v]
      split_ifs <;> linarith [x.property.1, x.property.2]
    · dsimp [v]
      rw [Finset.sum_add_distrib]
      simp
  let f : Set.Icc (0 : ℝ) 1 →
      {p : ProfileCube // p ∈ causalParetoFrontier (waitProxyResponse c)
        (waitProxyResponse_valid c hc0 (fun r => (hclt r).le)) e} := fun x =>
    ⟨waitProxyCausalWeightProfile c e (v x), by
      rw [causalParetoFrontier_waitProxy_eq c hc0 hclt hcofinal e]
      exact ⟨v x, hv x, rfl⟩⟩
  refine ⟨f, ?_⟩
  intro x y hxy
  have hprofiles :
      waitProxyCausalWeightProfile c e (v x) =
        waitProxyCausalWeightProfile c e (v y) :=
    congrArg Subtype.val hxy
  have hweights : v x = v y :=
    waitProxyCausalWeightProfile_injectiveOn_probability
      c (fun r => (hclt r).le) hcofinal e (hv x) (hv y) hprofiles
  apply Subtype.ext
  simpa [v, hab] using congrFun hweights a

private theorem cardinalMk_ProfileCube_eq_continuum :
    Cardinal.mk ProfileCube = Cardinal.continuum := by
  change Cardinal.mk (ℕ → Set.Icc (0 : ℝ) 1) = Cardinal.continuum
  rw [Cardinal.mk_pi, Cardinal.prod_const',
    Cardinal.mk_Icc_real zero_lt_one, Cardinal.mk_nat,
    Cardinal.continuum_power_aleph0]

/-- The causal wait--proxy Pareto frontier has exactly continuum cardinality. -/
theorem cardinalMk_causalParetoFrontier_waitProxy_eq_continuum
    [Nontrivial A]
    (c : ℕ → ℝ) (hc0 : ∀ r, 0 ≤ c r)
    (hclt : ∀ r, c r < 1 / 2)
    (hcofinal : ∀ x < (1 / 2 : ℝ), ∃ s, x < c s)
    (e : ℕ ≃ CausalNativeTest (WaitProxyAction A) WaitProxyObservation) :
    Cardinal.mk {p : ProfileCube // p ∈ causalParetoFrontier (waitProxyResponse c)
      (waitProxyResponse_valid c hc0 (fun r => (hclt r).le)) e} =
      Cardinal.continuum := by
  apply le_antisymm
  · exact (Cardinal.mk_subtype_le _).trans_eq
      cardinalMk_ProfileCube_eq_continuum
  · obtain ⟨f, hf⟩ :=
      exists_injective_unitInterval_to_causalParetoFrontier_waitProxy
        c hc0 hclt hcofinal e
    rw [← Cardinal.mk_Icc_real zero_lt_one]
    exact Cardinal.mk_le_of_injective hf

theorem waitProxyCausalFrontierProfiles_nonzero [Nontrivial A]
    (c : ℕ → ℝ) (hchalf : ∀ s, c s ≤ 1 / 2)
    (hcofinal : ∀ x < (1 / 2 : ℝ), ∃ s, x < c s)
    (e : ℕ ≃ CausalNativeTest (WaitProxyAction A) WaitProxyObservation)
    {p : ProfileCube} (hp : p ∈ waitProxyCausalFrontierProfiles c e) :
    p ≠ zeroProfile := by
  rcases hp with ⟨v, hv, rfl⟩
  obtain ⟨a, ha⟩ := exists_probability_weight_lt_one v hv
  obtain ⟨s, hs⟩ := hcofinal (v a / 2) (by linarith)
  intro hzero
  have hj : ((waitProxyCausalWeightProfile c e v
      (e.symm
        (⟨s + 1, waitProxyCanonicalPlan s a⟩ :
          CausalNativeTest (WaitProxyAction A) WaitProxyObservation)) :
        Set.Icc (0 : ℝ) 1) : ℝ) = 0 := by
    have h := congrArg
      (fun q : ProfileCube =>
        ((q (e.symm
          (⟨s + 1, waitProxyCanonicalPlan s a⟩ :
            CausalNativeTest (WaitProxyAction A) WaitProxyObservation)) :
              Set.Icc (0 : ℝ) 1) : ℝ)) hzero
    simpa [zeroProfile] using h
  rw [waitProxyCausalWeightProfile_coe_eq_coordinate c hchalf e v hv.1,
    e.apply_symm_apply, waitProxyCausalCoordinate_canonical] at hj
  unfold waitProxyProfile at hj
  rw [max_eq_left (by linarith)] at hj
  linarith

theorem waitProxyPolicyProfile_not_mem_frontier
    (c : ℕ → ℝ) (hc0 : ∀ r, 0 ≤ c r)
    (hclt : ∀ r, c r < 1 / 2)
    (hcofinal : ∀ x < (1 / 2 : ℝ), ∃ s, x < c s)
    (e : ℕ ≃ CausalNativeTest (WaitProxyAction A) WaitProxyObservation)
    (pi : ValidCausalPolicy (WaitProxyAction A) WaitProxyObservation) :
    causalPolicyProfile (waitProxyResponse c)
        (waitProxyResponse_valid c hc0 (fun r => (hclt r).le)) e pi ∉
      causalParetoFrontier (waitProxyResponse c)
        (waitProxyResponse_valid c hc0 (fun r => (hclt r).le)) e := by
  rw [causalParetoFrontier_waitProxy_eq c hc0 hclt hcofinal e,
    causalPolicyProfile_eq_waitProxyCausalWeightProfile
      pi c hc0 (fun r => (hclt r).le) e]
  rintro ⟨v, hv, heq⟩
  let z := waitProxyEffectiveWeight pi.1 c
  have hz : IsStrictSubprobability z :=
    waitProxyEffectiveWeight_strictSubprobability pi.1 pi.2 c hc0 hclt
  have hdom :
      waitProxyCausalWeightProfile c e z ≤
        waitProxyCausalWeightProfile c e v :=
    heq.le
  have hvlez : ∀ a, v a ≤ z a :=
    weight_le_of_waitProxyCausalWeightProfile_le
      c (fun r => (hclt r).le) hcofinal e
      hz.1 hv.1
      (fun a => waitProxySubprobability_le_one
        (⟨hv.1, hv.2.le⟩ : IsSubprobability v) a)
      hdom
  have hsum : ∑ a, v a ≤ ∑ a, z a :=
    Finset.sum_le_sum fun a _ => hvlez a
  rw [hv.2] at hsum
  exact (not_le_of_gt hz.2) hsum

theorem causalParetoFrontier_waitProxy_nonzero [Nontrivial A]
    (c : ℕ → ℝ) (hc0 : ∀ r, 0 ≤ c r)
    (hclt : ∀ r, c r < 1 / 2)
    (hcofinal : ∀ x < (1 / 2 : ℝ), ∃ s, x < c s)
    (e : ℕ ≃ CausalNativeTest (WaitProxyAction A) WaitProxyObservation)
    {p : ProfileCube}
    (hp : p ∈ causalParetoFrontier (waitProxyResponse c)
      (waitProxyResponse_valid c hc0 (fun r => (hclt r).le)) e) :
    p ≠ zeroProfile := by
  rw [causalParetoFrontier_waitProxy_eq c hc0 hclt hcofinal e] at hp
  exact waitProxyCausalFrontierProfiles_nonzero
    c (fun r => (hclt r).le) hcofinal e hp

theorem waitProxyCausal_unattained_nonzero_frontier [Nontrivial A]
    (c : ℕ → ℝ) (hc0 : ∀ r, 0 ≤ c r)
    (hclt : ∀ r, c r < 1 / 2)
    (hcofinal : ∀ x < (1 / 2 : ℝ), ∃ s, x < c s)
    (e : ℕ ≃ CausalNativeTest (WaitProxyAction A) WaitProxyObservation) :
    causalParetoFrontier (waitProxyResponse c)
        (waitProxyResponse_valid c hc0 (fun r => (hclt r).le)) e =
      waitProxyCausalFrontierProfiles c e ∧
    (∀ p ∈ causalParetoFrontier (waitProxyResponse c)
        (waitProxyResponse_valid c hc0 (fun r => (hclt r).le)) e,
      p ≠ zeroProfile) ∧
    Set.InjOn (waitProxyCausalWeightProfile c e)
      {v : A → ℝ | IsDist v} ∧
    (∀ pi : ValidCausalPolicy (WaitProxyAction A) WaitProxyObservation,
      causalPolicyProfile (waitProxyResponse c)
          (waitProxyResponse_valid c hc0 (fun r => (hclt r).le)) e pi ∉
        causalParetoFrontier (waitProxyResponse c)
          (waitProxyResponse_valid c hc0 (fun r => (hclt r).le)) e) := by
  exact ⟨causalParetoFrontier_waitProxy_eq c hc0 hclt hcofinal e,
    fun _ hp => causalParetoFrontier_waitProxy_nonzero
      c hc0 hclt hcofinal e hp,
    waitProxyCausalWeightProfile_injectiveOn_probability
      c (fun r => (hclt r).le) hcofinal e,
    waitProxyPolicyProfile_not_mem_frontier c hc0 hclt hcofinal e⟩

theorem waitProxyGeometricCausal_unattained_nonzero_frontier
    [Nontrivial A] {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (e : ℕ ≃ CausalNativeTest (WaitProxyAction A) WaitProxyObservation) :
    causalParetoFrontier (waitProxyResponse (waitProxyStrength lam))
        (waitProxyResponse_valid (waitProxyStrength lam)
          (fun s => waitProxyStrength_nonneg hlam0.le hlam1.le s)
          (fun s => (waitProxyStrength_lt_half hlam1 s).le)) e =
      waitProxyCausalFrontierProfiles (waitProxyStrength lam) e ∧
    (∀ p ∈ causalParetoFrontier
        (waitProxyResponse (waitProxyStrength lam))
        (waitProxyResponse_valid (waitProxyStrength lam)
          (fun s => waitProxyStrength_nonneg hlam0.le hlam1.le s)
          (fun s => (waitProxyStrength_lt_half hlam1 s).le)) e,
      p ≠ zeroProfile) ∧
    Set.InjOn (waitProxyCausalWeightProfile (waitProxyStrength lam) e)
      {v : A → ℝ | IsDist v} ∧
    (∀ pi : ValidCausalPolicy (WaitProxyAction A) WaitProxyObservation,
      causalPolicyProfile (waitProxyResponse (waitProxyStrength lam))
          (waitProxyResponse_valid (waitProxyStrength lam)
            (fun s => waitProxyStrength_nonneg hlam0.le hlam1.le s)
            (fun s => (waitProxyStrength_lt_half hlam1 s).le)) e pi ∉
        causalParetoFrontier (waitProxyResponse (waitProxyStrength lam))
          (waitProxyResponse_valid (waitProxyStrength lam)
            (fun s => waitProxyStrength_nonneg hlam0.le hlam1.le s)
            (fun s => (waitProxyStrength_lt_half hlam1 s).le)) e) := by
  exact waitProxyCausal_unattained_nonzero_frontier
    (waitProxyStrength lam)
    (fun s => waitProxyStrength_nonneg hlam0.le hlam1.le s)
    (waitProxyStrength_lt_half hlam1)
    (waitProxyStrength_cofinal hlam0 hlam1.le) e

/-- The geometric hidden-repair instance has a literal injective family of
frontier profiles indexed by the real unit interval. -/
theorem exists_injective_unitInterval_to_geometricWaitProxyFrontier
    [Nontrivial A] {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (e : ℕ ≃ CausalNativeTest (WaitProxyAction A) WaitProxyObservation) :
    ∃ f : Set.Icc (0 : ℝ) 1 →
        {p : ProfileCube // p ∈ causalParetoFrontier
          (waitProxyResponse (waitProxyStrength lam))
          (waitProxyResponse_valid (waitProxyStrength lam)
            (fun s => waitProxyStrength_nonneg hlam0.le hlam1.le s)
            (fun s => (waitProxyStrength_lt_half hlam1 s).le)) e},
      Function.Injective f :=
  exists_injective_unitInterval_to_causalParetoFrontier_waitProxy
    (waitProxyStrength lam)
    (fun s => waitProxyStrength_nonneg hlam0.le hlam1.le s)
    (waitProxyStrength_lt_half hlam1)
    (waitProxyStrength_cofinal hlam0 hlam1.le) e

/-- The geometric hidden-repair frontier has exactly continuum cardinality. -/
theorem cardinalMk_geometricWaitProxyFrontier_eq_continuum
    [Nontrivial A] {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (e : ℕ ≃ CausalNativeTest (WaitProxyAction A) WaitProxyObservation) :
    Cardinal.mk {p : ProfileCube // p ∈ causalParetoFrontier
      (waitProxyResponse (waitProxyStrength lam))
      (waitProxyResponse_valid (waitProxyStrength lam)
        (fun s => waitProxyStrength_nonneg hlam0.le hlam1.le s)
        (fun s => (waitProxyStrength_lt_half hlam1 s).le)) e} =
      Cardinal.continuum :=
  cardinalMk_causalParetoFrontier_waitProxy_eq_continuum
    (waitProxyStrength lam)
    (fun s => waitProxyStrength_nonneg hlam0.le hlam1.le s)
    (waitProxyStrength_lt_half hlam1)
    (waitProxyStrength_cofinal hlam0 hlam1.le) e


end

end IdExp

