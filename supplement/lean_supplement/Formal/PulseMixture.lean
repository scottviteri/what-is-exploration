import Formal.PulseBehavior

/-!
# Recorded root randomization in the pulse example

The source is the actual causal history experiment of a policy that queries
with probability `s`. The root action is part of the signal. The proof does
not replace the countable class with a finite truncation.
-/

namespace IdExp

open Finset Set

/-- Query with probability `s` at the root and wait at every later step. -/
noncomputable def pulseMixPolicy (s : ℝ) : CausalPolicy Bool Bool :=
  fun h a => if h = [] then (if a then s else 1 - s) else if a then 0 else 1

theorem pulseMixPolicy_valid {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    IsCausalPolicy (pulseMixPolicy s) := by
  intro h
  constructor
  · intro a
    cases a <;> by_cases hh : h = [] <;> simp [pulseMixPolicy, hh] <;> linarith [hs.1, hs.2]
  · by_cases hh : h = [] <;> simp [pulseMixPolicy, hh]

/-- Root randomization mixes whole history laws, because the subsequent
policy is the same in both branches. -/
theorem pulseMix_trace (s : ℝ) (θ : WaitingQueryWorld) (h : CausalHistory Bool Bool) :
    causalTraceProb (pulseMixPolicy s) (detResponse (pulseOutput θ)) h =
      (1 - s) * causalTraceProb (pulsePolicy false).1 (detResponse (pulseOutput θ)) h +
      s * causalTraceProb (pulsePolicy true).1 (detResponse (pulseOutput θ)) h := by
  induction h using List.reverseRecOn with
  | nil => simp [causalTraceProb, causalTraceProbFrom]
  | append_singleton h ao ih =>
    rw [causalTraceProb_append_singleton, causalTraceProb_append_singleton,
      causalTraceProb_append_singleton]
    by_cases hh : h = []
    · subst h
      cases ha : ao.1 <;>
        simp [pulseMixPolicy, pulsePolicy, validDetPolicy, detPolicy, pulseAction,
          causalTraceProb, causalTraceProbFrom, mul_comm]
    · have h0 : (pulsePolicy false).1 h ao.1 = (if ao.1 then 0 else 1) := by
        cases ha : ao.1 <;> simp [pulsePolicy, validDetPolicy, detPolicy, pulseAction, hh]
      have h1 : (pulsePolicy true).1 h ao.1 = (if ao.1 then 0 else 1) := by
        cases ha : ao.1 <;> simp [pulsePolicy, validDetPolicy, detPolicy, pulseAction, hh]
      rw [h0, h1, ih]
      simp only [pulseMixPolicy, if_neg hh]
      ring

noncomputable def pulseMixExperiment (s : ℝ) (t : ℕ) :
    FiniteExperiment WaitingQueryWorld (CausalFiniteTrace Bool Bool t) :=
  causalBehaviorFiniteExperiment (pulseMixPolicy s) pulseBehavior t

theorem pulseMixExperiment_eq (s : ℝ) (t : ℕ) :
    pulseMixExperiment s t = fun θ x =>
      (1 - s) * diracExp (pulseTrace false t) θ x + s * diracExp (pulseTrace true t) θ x := by
  unfold pulseMixExperiment pulseBehavior
  rw [causalBehaviorFiniteExperiment_ofResponse]
  funext θ x
  change causalTraceProb (pulseMixPolicy s) (detResponse (pulseOutput θ)) (List.ofFn x) = _
  rw [pulseMix_trace]
  have hb (b : Bool) :
      causalTraceProb (pulsePolicy b).1 (detResponse (pulseOutput θ)) (List.ofFn x) =
        diracExp (pulseTrace b t) θ x := by
    have he := congrFun (congrFun (pulseExperiment_eq_dirac b t) θ) x
    change causalBehaviorFiniteExperiment (pulsePolicy b).1
      (fun θ => CausalBehavior.ofResponse (detResponse (pulseOutput θ))
        (isCausalResponse_detResponse _)) t θ x = _ at he
    rw [causalBehaviorFiniteExperiment_ofResponse] at he
    exact he
  rw [hb false, hb true]

theorem pulseMixExperiment_valid {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (t : ℕ) :
    IsFiniteExperiment (pulseMixExperiment s t) := by
  rw [pulseMixExperiment_eq]
  intro θ
  constructor
  · intro x
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hs.2) (diracExp_nonneg _ _ _))
      (mul_nonneg hs.1 (diracExp_nonneg _ _ _))
  · change (∑ x, ((1 - s) * diracExp (pulseTrace false t) θ x +
        s * diracExp (pulseTrace true t) θ x)) = 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_diracExp, sum_diracExp]
    ring

/-- Decoding the root mixture is the same recorded mixture of decoder rows. -/
theorem pulseMix_decisionLaw {Y : Type*} [Fintype Y] (s : ℝ) (t : ℕ)
    (G : CausalFiniteTrace Bool Bool t → Y → ℝ) (θ : WaitingQueryWorld) (y : Y) :
    finiteDecisionLaw (pulseMixExperiment s t) G θ y =
      (1 - s) * G (pulseTrace false t θ) y + s * G (pulseTrace true t θ) y := by
  classical
  rw [pulseMixExperiment_eq]
  simp only [finiteDecisionLaw, add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp [diracExp]

/-- Error to an arbitrary deterministic target is one minus the decoded
probability of that target signal. The world class may be infinite. -/
theorem decodeErr_to_diracExp {Θ X Y : Type*} [Fintype X] [Fintype Y]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E) (f : Θ → Y)
    (G : X → Y → ℝ) (hG : G ∈ stochasticRules X Y) (θ : Θ) :
    decodeErr E (diracExp f) G θ = 1 - finiteDecisionLaw E G θ (f θ) := by
  classical
  have hp := finiteDecisionLaw_valid E hE G hG θ
  have hpθ : finiteDecisionLaw E G θ (f θ) ≤ 1 := by
    rw [← hp.2]
    exact Finset.single_le_sum (fun y _ => hp.1 y) (Finset.mem_univ _)
  have hterm (y : Y) :
      |finiteDecisionLaw E G θ y - diracExp f θ y| =
        finiteDecisionLaw E G θ y +
          if y = f θ then 1 - 2 * finiteDecisionLaw E G θ (f θ) else 0 := by
    by_cases hy : y = f θ
    · subst y
      rw [diracExp_self, abs_of_nonpos (by linarith), if_pos rfl]
      ring
    · simp [diracExp_apply, hy, abs_of_nonneg (hp.1 y)]
  change (1 / 2 : ℝ) * ∑ y, |finiteDecisionLaw E G θ y - diracExp f θ y| = _
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, hp.2]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- Uniform upper bound for every native plan up to the collection horizon. -/
theorem pulseMix_native_deficiency_le {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {t m : ℕ} (ht : 1 ≤ t) (hm : m ≤ t) (σ : CausalObservationPlan Bool Bool m) :
    finiteDeficiency (pulseMixExperiment s t)
      (CausalObservationPlan.behaviorPlanExperiment σ pulseBehavior) ≤ (1 - s) / 2 := by
  let f := fun θ => detPlanObs m σ.toCausalPlan (pulseOutput θ)
  obtain ⟨W, hW, hcW⟩ := exists_one_missing_bit_decoder
    (pulseTrace false t) Option.isSome f (pulse_wait_bit_separates_plan hm σ)
  let Q := diracPreimageDecoder (pulseTrace true t) f
  have hQ : Q ∈ stochasticRules _ _ := diracPreimageDecoder_mem_stochasticRules _ _
  have hcQ θ : Q (pulseTrace true t θ) (f θ) = 1 :=
    diracPreimageDecoder_apply_of_separates (pulse_query_separates_plan hm σ) θ
  let G : CausalFiniteTrace Bool Bool t → CausalObservationTrace Bool m → ℝ :=
    fun x y => if (x ⟨0, by omega⟩).1 then Q x y else W x y
  have hG : G ∈ stochasticRules _ _ := by
    intro x _
    by_cases hx : (x ⟨0, by omega⟩).1 = true
    · simpa [G, hx] using hQ x trivial
    · simpa [G, hx] using hW x trivial
  rw [pulse_nativePlan_dirac]
  apply finiteDeficiency_le_of_decoder _ _ G hG
  intro θ
  rw [decodeErr_to_diracExp _ (pulseMixExperiment_valid hs t) _ _ hG θ, pulseMix_decisionLaw]
  change 1 - ((1 - s) * G (pulseTrace false t θ) (f θ) + s * G (pulseTrace true t θ) (f θ)) ≤ _
  simp only [G, pulseTrace, ↓reduceIte]
  change 1 - ((1 - s) * W (pulseTrace false t θ) (f θ) + s * Q (pulseTrace true t θ) (f θ)) ≤ _
  rw [hcQ θ]
  nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr (hcW θ))]

/-- Two still-merged waiting worlds give a lower bound for every randomized
decoder; the queried branch has total mass only `s`. -/
theorem pulseMix_rootQuery_deficiency_ge {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (t : ℕ) :
    (1 - s) / 2 ≤ finiteDeficiency (pulseMixExperiment s t)
      (CausalObservationPlan.behaviorPlanExperiment waitingQueryRootPlan pulseBehavior) := by
  rw [pulse_nativePlan_dirac]
  simp_rw [pulse_rootQuery_observation]
  let f : WaitingQueryWorld → CausalObservationTrace Bool 1 := fun θ _ => θ.isSome
  apply le_csInf (finiteDeficiencyCandidates_nonempty_of_valid _ _
    (pulseMixExperiment_valid hs t) (diracExp_valid f))
  rintro c ⟨G, hG, herr⟩
  have hn := herr none
  have hk := herr (some t)
  rw [decodeErr_to_diracExp _ (pulseMixExperiment_valid hs t) f G hG none,
    pulseMix_decisionLaw] at hn
  rw [decodeErr_to_diracExp _ (pulseMixExperiment_valid hs t) f G hG (some t),
    pulseMix_decisionLaw] at hk
  have hmerge : pulseTrace false t (some t) = pulseTrace false t none := by
    simpa using waitingQueryTrace_undetected t t (by omega)
  rw [hmerge] at hk
  have hf : f none ≠ f (some t) := by
    intro he
    have := congrFun he 0
    simp [f] at this
  have hsum := stochasticRules_add_le_one hG (pulseTrace false t none) hf
  have hqn := stochasticRules_le_one hG (pulseTrace true t none) (f none)
  have hqk := stochasticRules_le_one hG (pulseTrace true t (some t)) (f (some t))
  nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hqn),
    mul_nonneg hs.1 (sub_nonneg.mpr hqk),
    mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hsum)]

/-- The literal native audit of every recorded root mixture, at every
`t ≥ n ≥ 1`, is exactly `(1-s)/2`. -/
theorem pulseMix_nativeAudit_eq {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {t n : ℕ} (ht : n ≤ t) (hn : 1 ≤ n) :
    causalBehaviorNativeDeficiencyUpTo (pulseMixExperiment s t) pulseBehavior n = (1 - s) / 2 := by
  have hbound : ∀ d ∈ causalBehaviorNativeDeficiencyValuesUpTo
      (pulseMixExperiment s t) pulseBehavior n, d ≤ (1 - s) / 2 := by
    rintro d ⟨m, hm, σ, rfl⟩
    exact pulseMix_native_deficiency_le hs (hn.trans ht) (hm.trans ht) σ
  have hmem : finiteDeficiency (pulseMixExperiment s t)
      (CausalObservationPlan.behaviorPlanExperiment waitingQueryRootPlan pulseBehavior) ∈
        causalBehaviorNativeDeficiencyValuesUpTo (pulseMixExperiment s t) pulseBehavior n :=
    ⟨1, hn, waitingQueryRootPlan, rfl⟩
  exact le_antisymm (csSup_le ⟨_, hmem⟩ hbound)
    ((pulseMix_rootQuery_deficiency_ge hs t).trans (le_csSup ⟨_, hbound⟩ hmem))

/-- Among all recorded root mixtures, exactly certain querying is NES. -/
theorem pulseMix_nativelySufficient_iff {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    CausalBehaviorNativelySufficient pulseBehavior ⟨pulseMixPolicy s, pulseMixPolicy_valid hs⟩ ↔ s = 1 := by
  constructor
  · intro h
    by_contra hne
    have hpos : 0 < (1 - s) / 4 := by
      have hlt := lt_of_le_of_ne hs.2 hne
      linarith
    obtain ⟨T, hT⟩ := h 1 ((1 - s) / 4) hpos
    have hu := hT T le_rfl waitingQueryRootPlan
    have hl := pulseMix_rootQuery_deficiency_ge hs T
    change finiteDeficiency (pulseMixExperiment s T) _ < _ at hu
    linarith
  · rintro rfl n ε hε
    refine ⟨max n 1, fun t ht σ => ?_⟩
    have hle := pulseMix_native_deficiency_le hs ((le_max_right n 1).trans ht)
      ((le_max_left n 1).trans ht) σ
    change finiteDeficiency (pulseMixExperiment 1 t) _ < ε
    exact hle.trans_lt (by simpa using hε)

end IdExp
