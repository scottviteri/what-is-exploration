import Formal.LocalDominanceWithoutProgress
import Formal.StrictFinitaryObjectives
import Formal.DeterministicDeficiency

/-!
# Strict finitary monotonicity can forbid continuity in the policy tables

Two concrete proofs of the paper's `prop:finitary-continuity-obstruction`.
The first uses the three-observation absorbing wait/test class; the final
`BinaryWaitReveal` section checks the literal two-observation nonabsorbing
paper interface, including continuity on the product/subtype topology.  One hidden bit; a test reveals it exactly at any time (strength `1/2`
throughout, `lookaheadStrength 0`); testing absorbs.  Waiting `m` steps and
then testing is natively sufficient for every `m`, so all these policies are
finitarily equivalent to testing immediately, which strictly finitarily
dominates never testing.  Yet their policy tables converge coordinatewise to
the never-test table.  Hence any objective that is strictly finitarily
monotone cannot be sequentially continuous in the product topology of policy
tables; in particular it is not continuous.  Only the coordinatewise
(sequential) form of continuity is used, so no topology instance on the
policy type is needed.
-/

namespace IdExp

open Filter Topology

noncomputable section

/-- The exact-test class: worlds are one bit, every test has strength `1/2`. -/
abbrev exactTestClass : (Unit → Bool) → CausalResponse (WaitProxyAction Unit) WaitProxyObservation :=
  waitProxyResponse (lookaheadStrength 0)

theorem exactTestClass_valid (θ : Unit → Bool) : IsCausalResponse (exactTestClass θ) :=
  waitProxyResponse_valid _ (lookaheadStrength_nonneg 0) (lookaheadStrength_le_half 0) θ

/-- Wait `m` steps, then test in the three-observation comparison interface. -/
abbrev delayedTestPolicy (m : ℕ) : ValidCausalPolicy (WaitProxyAction Unit) WaitProxyObservation :=
  lookaheadPolicy m

/-- Never test in the three-observation comparison interface. -/
def alwaysWaitPolicy : ValidCausalPolicy (WaitProxyAction Unit) WaitProxyObservation :=
  ⟨waitProxyOneShotPolicy 0 (fun _ : Unit => 0),
    waitProxyOneShotPolicy_valid 0 _ (by intros; norm_num) (by simp)⟩

/-- After its test, a delayed-test policy's record is an exact substitute for
every native experiment. -/
theorem delayedTest_exact (m : ℕ) {n : ℕ}
    (τ : CausalPlan (WaitProxyAction Unit) WaitProxyObservation n) {t : ℕ} (ht : m < t) :
    finiteDeficiency
      (causalFiniteExperiment (delayedTestPolicy m).1 exactTestClass t)
      (causalPlanObservationExperiment n τ exactTestClass) = 0 := by
  rcases waitProxyPlan_alwaysWait_or_firstTestsAt τ with hall | ⟨s, a, hfirst⟩
  · exact waitProxyNativePlan_alwaysWait_deficiency _
      (causalFiniteExperiment_valid _ (delayedTestPolicy m).2 _ exactTestClass_valid t)
      τ _ (lookaheadStrength_nonneg 0) (lookaheadStrength_le_half 0) hall
  · have hf := waitProxyPolicyTestDeficiency_eq_of_first (a := a)
      (delayedTestPolicy m) (lookaheadStrength 0) (lookaheadStrength_nonneg 0)
      (lookaheadStrength_le_half 0) τ hfirst.1 hfirst t
    change finiteDeficiency _ _ = _ at hf
    cases a
    rw [lookaheadPolicy_effective m 0 t ht] at hf
    simp only [lookaheadStrength, Nat.not_lt_zero, ↓reduceIte] at hf
    norm_num at hf
    exact hf

theorem delayedTest_nativelySufficient (m : ℕ) :
    CausalNativelySufficient exactTestClass (delayedTestPolicy m) := by
  intro n ε hε
  refine ⟨m + 1, fun t ht τ => ?_⟩
  rw [delayedTest_exact m τ (by omega)]
  exact hε

theorem delayedTest_greatest (m : ℕ) :
    CausalFinitarilyGreatest exactTestClass (delayedTestPolicy m) :=
  (causalNativelySufficient_iff_finitarilyGreatest _ exactTestClass_valid _).1
    (delayedTest_nativelySufficient m)

/-- All delayed-test policies are finitarily equivalent. -/
theorem delayedTest_mutual (m k : ℕ) :
    CausalFinitaryDominates exactTestClass (delayedTestPolicy m) (delayedTestPolicy k) :=
  delayedTest_greatest m _

theorem alwaysWait_effectiveWeight (t : ℕ) :
    waitProxyEffectiveWeightFinite alwaysWaitPolicy.1 (lookaheadStrength 0) t () = 0 := by
  unfold waitProxyEffectiveWeightFinite alwaysWaitPolicy
  simp [waitProxyOneShot_firstTestMass]

/-- Never testing leaves the immediate test at deficiency `1/2` forever. -/
theorem alwaysWait_immediate_deficiency (t : ℕ) :
    finiteDeficiency
      (causalFiniteExperiment alwaysWaitPolicy.1 exactTestClass t)
      (causalPlanObservationExperiment (0 + 1) (waitProxyCanonicalPlan 0 ()) exactTestClass)
      = 1 / 2 := by
  have hf := waitProxyPolicyTestDeficiency_eq_of_first (a := ())
    alwaysWaitPolicy (lookaheadStrength 0) (lookaheadStrength_nonneg 0)
    (lookaheadStrength_le_half 0) (waitProxyCanonicalPlan 0 ()) (Nat.lt_succ_self 0)
    (waitProxyCanonicalPlan_firstTestsAt 0 ()) t
  change finiteDeficiency _ _ = _ at hf
  rw [alwaysWait_effectiveWeight t] at hf
  norm_num [lookaheadStrength] at hf ⊢
  exact hf

theorem alwaysWait_not_nativelySufficient :
    ¬ CausalNativelySufficient exactTestClass alwaysWaitPolicy := by
  intro h
  obtain ⟨T, hT⟩ := h (0 + 1) (1 / 2) (by norm_num)
  have he := hT T le_rfl (waitProxyCanonicalPlan 0 ())
  rw [alwaysWait_immediate_deficiency T] at he
  exact lt_irrefl _ he

/-- Never testing does not finitarily dominate the immediate test. -/
theorem alwaysWait_not_dominates_immediate :
    ¬ CausalFinitaryDominates exactTestClass alwaysWaitPolicy (delayedTestPolicy 0) := by
  intro h
  apply alwaysWait_not_nativelySufficient
  rw [causalNativelySufficient_iff_finitarilyGreatest _ exactTestClass_valid]
  intro ρ
  exact causalFinitaryDominates_trans _ exactTestClass_valid h (delayedTest_greatest 0 ρ)

/-! ## Convergence of the policy tables -/

/-- The policy table of a valid policy, as a point of the product space of rows. -/
def policyTable (π : ValidCausalPolicy (WaitProxyAction Unit) WaitProxyObservation) :
    CausalHistory (WaitProxyAction Unit) WaitProxyObservation → WaitProxyAction Unit → ℝ :=
  π.1

/-- Away from its test depth, a delayed-test policy's row is the wait row. -/
theorem delayedTest_row_eq_wait (m : ℕ)
    (h : CausalHistory (WaitProxyAction Unit) WaitProxyObservation) (hm : h.length ≠ m)
    (act : WaitProxyAction Unit) :
    (delayedTestPolicy m).1 h act = alwaysWaitPolicy.1 h act := by
  show waitProxyOneShotPolicy m (fun _ : Unit => 1) h act =
    waitProxyOneShotPolicy 0 (fun _ : Unit => 0) h act
  unfold waitProxyOneShotPolicy
  by_cases h0 : h.length = 0
  · have hm' : (0 : ℕ) ≠ m := h0 ▸ hm
    cases act <;> simp [h0, hm']
  · cases act <;> simp [hm, h0]

/-- **The delayed-test tables converge to the never-test table**, coordinate
by coordinate. -/
theorem tendsto_delayedTest_policyTable :
    Tendsto (fun m => policyTable (delayedTestPolicy m)) atTop (𝓝 (policyTable alwaysWaitPolicy)) := by
  refine tendsto_pi_nhds.2 fun h => tendsto_pi_nhds.2 fun act => ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop h.length] with m hm
  exact (delayedTest_row_eq_wait m h (by omega) act).symm

/-! ## The obstruction -/

/-- **No strictly finitarily monotone objective is sequentially continuous in
the policy tables.**  If `J` respects finitary dominance, strictly for one-sided
dominance, and sends every sequence of policies whose tables converge to a
convergent sequence of scores, a contradiction follows. -/
theorem no_tableContinuous_strictly_finitary_objective
    (J : ValidCausalPolicy (WaitProxyAction Unit) WaitProxyObservation → ℝ)
    (hmono : ∀ π σ, CausalFinitaryDominates exactTestClass π σ → J σ ≤ J π)
    (hstrict : ∀ π σ, CausalFinitaryDominates exactTestClass π σ →
      ¬ CausalFinitaryDominates exactTestClass σ π → J σ < J π)
    (hcont : ∀ (π : ℕ → ValidCausalPolicy (WaitProxyAction Unit) WaitProxyObservation)
      (πlim : ValidCausalPolicy (WaitProxyAction Unit) WaitProxyObservation),
      Tendsto (fun m => policyTable (π m)) atTop (𝓝 (policyTable πlim)) →
      Tendsto (fun m => J (π m)) atTop (𝓝 (J πlim))) : False := by
  have hlim := hcont _ _ tendsto_delayedTest_policyTable
  have hconst : (fun m => J (delayedTestPolicy m)) = fun _ => J (delayedTestPolicy 0) := by
    funext m
    exact le_antisymm (hmono _ _ (delayedTest_mutual 0 m)) (hmono _ _ (delayedTest_mutual m 0))
  rw [hconst] at hlim
  have heq : J alwaysWaitPolicy = J (delayedTestPolicy 0) :=
    tendsto_nhds_unique hlim tendsto_const_nhds
  have hlt := hstrict _ _ (delayedTest_greatest 0 alwaysWaitPolicy) alwaysWait_not_dominates_immediate
  linarith

/-! ## The paper's literal two-observation, nonabsorbing witness

`false` is WAIT and also the silent observation; `true` is REVEAL. REVEAL
returns the hidden bit at every history. The action remains recorded, so a
zero from WAIT and a zero from REVEAL need no separate observation symbols.
-/

namespace BinaryWaitReveal

abbrev History := CausalHistory Bool Bool

local instance : TopologicalSpace (CausalPolicy Bool Bool) :=
  inferInstanceAs (TopologicalSpace (History → Bool → ℝ))

def response (θ : Bool) (_h : History) (a : Bool) : Bool := if a then θ else false

noncomputable def worlds (θ : Bool) : CausalResponse Bool Bool := detResponse (response θ)

theorem worlds_valid (θ : Bool) : IsCausalResponse (worlds θ) :=
  isCausalResponse_detResponse _

def delayedAction (m : ℕ) (h : History) : Bool := decide (m ≤ h.length)

noncomputable def delayedPolicy (m : ℕ) : ValidCausalPolicy Bool Bool :=
  validDetPolicy (delayedAction m)

noncomputable def waitPolicy : ValidCausalPolicy Bool Bool := validDetPolicy (fun _ => false)

/-- The first REVEAL identifies the bit, however long revelation was delayed. -/
theorem delayed_trace_injective (m t : ℕ) (ht : m < t) :
    Function.Injective (fun θ => detTraceFin (delayedAction m) (response θ) t) := by
  intro θ η he
  have hl := (detTraceFin_eq_iff (delayedAction m) (response θ) (response η) t).mp he
  have hp := detTraceList_eq_of_le (delayedAction m) (show m + 1 ≤ t by omega) hl
  have hlast := congrArg List.getLast? hp
  simpa [detTraceList_succ, delayedAction, response] using hlast

/-- Every delayed revealer eventually simulates every prefix of every
other deterministic policy; this is enough for the continuity obstruction. -/
theorem delayed_dominates_det (m : ℕ) (p : History → Bool) :
    CausalFinitaryDominates worlds (delayedPolicy m) (validDetPolicy p) := by
  intro n ε hε
  refine ⟨m + 1, fun t ht => ?_⟩
  change finiteDeficiency
    (causalFiniteExperiment (detPolicy (delayedAction m)) (fun θ => detResponse (response θ)) t)
    (causalFiniteExperiment (detPolicy p) (fun θ => detResponse (response θ)) n) < ε
  rw [causalFiniteExperiment_det, causalFiniteExperiment_det]
  have hz : finiteDeficiency
      (diracExp (fun θ => detTraceFin (delayedAction m) (response θ) t))
      (diracExp (fun θ => detTraceFin p (response θ) n)) = 0 := by
    apply finiteDeficiency_diracExp_eq_zero_of_separates
    intro θ η he
    exact congrArg (fun θ => detTraceFin p (response θ) n)
      (delayed_trace_injective m t (by omega) he)
  rwa [hz]

/-- All finite never-REVEAL records coincide in the two worlds. -/
theorem wait_trace_eq (t : ℕ) :
    detTraceFin (fun _ => false) (response false) t =
      detTraceFin (fun _ => false) (response true) t := by
  apply (detTraceFin_eq_iff _ _ _ _).mpr
  induction t with
  | zero => rfl
  | succ t ih => simp [detTraceList_succ, response, ih]

/-- Never revealing cannot simulate even the first immediate-REVEAL record. -/
theorem wait_not_dominates_immediate :
    ¬ CausalFinitaryDominates worlds waitPolicy (delayedPolicy 0) := by
  intro h
  obtain ⟨T, hT⟩ := h 1 (1/2) (by norm_num)
  have hb := hT T le_rfl
  change finiteDeficiency
    (causalFiniteExperiment (detPolicy (fun _ => false)) (fun θ => detResponse (response θ)) T)
    (causalFiniteExperiment (detPolicy (delayedAction 0)) (fun θ => detResponse (response θ)) 1)
      < 1/2 at hb
  rw [causalFiniteExperiment_det, causalFiniteExperiment_det] at hb
  have hl := half_le_finiteDeficiency_diracExp_of_merge
    (e := fun θ => detTraceFin (fun _ => false) (response θ) T)
    (f := fun θ => detTraceFin (delayedAction 0) (response θ) 1)
    ⟨false, true, wait_trace_eq T, fun he => Bool.false_ne_true
      (delayed_trace_injective 0 1 (by omega) he)⟩
  linarith

/-- Convergence in the actual subtype topology inherited from the product
of all behavioral-policy rows, including rows at histories of probability zero. -/
theorem tendsto_delayedPolicy :
    Tendsto delayedPolicy atTop (𝓝 waitPolicy) := by
  apply tendsto_subtype_rng.mpr
  refine tendsto_pi_nhds.2 fun h => tendsto_pi_nhds.2 fun a => ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop h.length] with m hm
  simp [delayedPolicy, waitPolicy, validDetPolicy, detPolicy, delayedAction, not_le.mpr hm]

/-- **Literal paper endpoint:** on two worlds, two actions, and two
observations, with nonabsorbing revelation, no continuous real score is
monotone for finitary dominance and strict for one-sided dominance. -/
theorem no_continuous_strictly_finitary_objective
    (J : ValidCausalPolicy Bool Bool → ℝ)
    (hmono : ∀ π σ, CausalFinitaryDominates worlds π σ → J σ ≤ J π)
    (hstrict : ∀ π σ, CausalFinitaryDominates worlds π σ →
      ¬ CausalFinitaryDominates worlds σ π → J σ < J π)
    (hcont : Continuous J) : False := by
  have hlim := hcont.continuousAt.tendsto.comp tendsto_delayedPolicy
  have hconst : (fun m => J (delayedPolicy m)) = fun _ => J (delayedPolicy 0) := by
    funext m
    exact le_antisymm (hmono _ _ (delayed_dominates_det 0 (delayedAction m)))
      (hmono _ _ (delayed_dominates_det m (delayedAction 0)))
  change Tendsto (fun m => J (delayedPolicy m)) atTop (𝓝 (J waitPolicy)) at hlim
  rw [hconst] at hlim
  have heq : J waitPolicy = J (delayedPolicy 0) :=
    tendsto_nhds_unique hlim tendsto_const_nhds
  have hlt := hstrict _ _ (delayed_dominates_det 0 (fun _ => false))
    wait_not_dominates_immediate
  change J waitPolicy < J (delayedPolicy 0) at hlt
  linarith

end BinaryWaitReveal

local instance : TopologicalSpace (CausalPolicy Bool Bool) :=
  inferInstanceAs (TopologicalSpace (CausalHistory Bool Bool → Bool → ℝ))

/-- Public reader-index endpoint for the literal Boolean WAIT/REVEAL witness. -/
theorem binaryWaitReveal_no_continuous_strictly_finitary_objective
    (J : ValidCausalPolicy Bool Bool → ℝ)
    (hmono : ∀ π σ, CausalFinitaryDominates BinaryWaitReveal.worlds π σ → J σ ≤ J π)
    (hstrict : ∀ π σ, CausalFinitaryDominates BinaryWaitReveal.worlds π σ →
      ¬ CausalFinitaryDominates BinaryWaitReveal.worlds σ π → J σ < J π)
    (hcont : Continuous J) : False :=
  BinaryWaitReveal.no_continuous_strictly_finitary_objective J hmono hstrict hcont

end

end IdExp
