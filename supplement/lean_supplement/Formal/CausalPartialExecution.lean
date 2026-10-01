import Formal.CausalEpisodicCoverage

/-!
# Partial execution and the from-ignorance certificate

This module proves the finite-experiment geometry in `prop:episodic`(c),
including its sharpness condition, for an arbitrary nonempty world class.
The from-ignorance radius is the actual directed deficiency from a one-point
experiment, not an assumed decoder error. No center-attainment hypothesis is
needed. The maximum over unexecuted tests is completed by zero, so executing
every test gives zero rather than an undefined empty maximum.

The final theorems instantiate the certificate on the actual independent
reset transcript of a fixed heterogeneous schedule. Execution requires
agreement at every node of the target's contingency tree before its horizon;
suffix behavior and action histories outside that tree are unrestricted.
This is not selection based on consistency along
the realized branch. `AdaptiveEpisodicExecution.lean` supplies the separate
predictable/adaptive almost-sure execution assembly; the general geometric
theorem here keeps exact simulation explicit.
-/

set_option linter.unusedSectionVars false

namespace IdExp

open Finset Set

noncomputable section

variable {Θ X Y : Type*}

/-- The experiment that reveals no information about its world. -/
def finiteIgnoranceExperiment (Θ : Type*) : FiniteExperiment Θ Unit :=
  fun _ _ => 1

theorem finiteIgnoranceExperiment_valid :
    IsFiniteExperiment (finiteIgnoranceExperiment Θ) := by
  intro θ
  constructor
  · intro x
    norm_num [finiteIgnoranceExperiment]
  · simp [finiteIgnoranceExperiment]

/-- A decoder out of a one-point experiment is precisely a randomized
constant response. Thus its deficiency is the TV Chebyshev-radius infimum. -/
theorem finiteDeficiencyCandidates_ignorance [Fintype Y]
    (F : FiniteExperiment Θ Y) :
    finiteDeficiencyCandidates (finiteIgnoranceExperiment Θ) F =
      {c | ∃ q : Y → ℝ, IsDist q ∧ ∀ θ, finiteTV q (F θ) ≤ c} := by
  ext c
  constructor
  · rintro ⟨G, hG, herr⟩
    refine ⟨G (), hG () (Set.mem_univ _), ?_⟩
    intro θ
    simpa [decodeErr, finiteTV, finiteDecisionLaw, finiteIgnoranceExperiment] using herr θ
  · rintro ⟨q, hq, herr⟩
    refine ⟨fun _ => q, fun _ _ => hq, ?_⟩
    intro θ
    simpa [decodeErr, finiteTV, finiteDecisionLaw, finiteIgnoranceExperiment] using herr θ

/-- Discarding a valid experiment produces the one-point experiment exactly. -/
theorem finiteIgnoranceExperiment_blackwellLE [Fintype X]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E) :
    FiniteBlackwellLE (finiteIgnoranceExperiment Θ) E := by
  refine ⟨fun _ _ => 1, ?_, ?_⟩
  · intro x _
    constructor
    · intro u
      norm_num
    · simp
  · funext θ u
    simpa [finiteDecisionLaw, finiteIgnoranceExperiment] using (hE θ).2

/-- Every valid source can ignore its signal, so it is at least as useful
as ignorance, without assuming an optimal constant decoder is attained. -/
theorem finiteDeficiency_le_from_ignorance
    [Fintype X] [Fintype Y] [Nonempty Θ] [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F) :
    finiteDeficiency E F ≤ finiteDeficiency (finiteIgnoranceExperiment Θ) F :=
  finiteDeficiency_mono_source_of_blackwellLE_arbitrary E
    (finiteIgnoranceExperiment Θ) F finiteIgnoranceExperiment_valid hF
    (finiteIgnoranceExperiment_blackwellLE E hE)

/-- An exact Blackwell garbling has zero directed deficiency. -/
theorem finiteDeficiency_eq_zero_of_blackwellLE
    [Fintype X] [Fintype Y] [Nonempty Θ] [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F)
    (hFE : FiniteBlackwellLE F E) : finiteDeficiency E F = 0 := by
  obtain ⟨G, hG, heq⟩ := hFE
  apply le_antisymm
  · apply finiteDeficiency_le_of_decoder E F G hG 0
    intro θ
    change finiteTV (finiteDecisionLaw E G θ) (F θ) ≤ 0
    rw [congrFun heq θ]
    simp [finiteTV]
  · exact finiteDeficiency_nonneg_of_valid E F hE hF

/-- Pairwise separation advantage lower-bounds the actual decoder infimum,
not merely the error of one chosen decoder. The world class need not be finite. -/
theorem finiteDeficiency_pairwise_lower
    [Fintype X] [Fintype Y] [Nonempty Y]
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (hE : IsFiniteExperiment E) (hF : IsFiniteExperiment F) (θ θ' : Θ) :
    (finiteTV (F θ) (F θ') - finiteTV (E θ) (E θ')) / 2 ≤
      finiteDeficiency E F := by
  apply le_csInf (finiteDeficiencyCandidates_nonempty_of_valid E F hE hF)
  rintro c ⟨G, hG, herr⟩
  exact finiteTV_pairwise_decoder_lower E F G hG θ θ' c (herr θ) (herr θ')

variable {A O : Type*} [Fintype A] [Fintype O] [Nonempty A]

/-- The finite heterogeneous family of all native tests of depth at most `n`. -/
abbrev CausalBoundedTest (A O : Type*) (n : ℕ) :=
  Σ m : Fin (n + 1), CausalPlan A O m.1

instance causalBoundedTest_nonempty (n : ℕ) : Nonempty (CausalBoundedTest A O n) :=
  ⟨⟨⟨0, Nat.zero_lt_succ n⟩, fun _ => Classical.arbitrary A⟩⟩

/-- The paper's `r_σ`, with a possibly infinite world class. -/
def causalFromIgnoranceRadius
    (Qs : Θ → CausalResponse A O) {n : ℕ} (t : CausalBoundedTest A O n) : ℝ :=
  finiteDeficiency (finiteIgnoranceExperiment Θ)
    (causalPlanObservationExperiment t.1.1 t.2 Qs)

/-- Maximum from-ignorance radius among the unexecuted tests, completed by
zero on executed tests. In particular the value is zero when all are executed. -/
def causalPartialExecutionBound
    (Qs : Θ → CausalResponse A O) (n : ℕ) (S : Set (CausalBoundedTest A O n)) : ℝ := by
  classical
  exact (Finset.univ : Finset (CausalBoundedTest A O n)).sup'
    Finset.univ_nonempty (fun t => if t ∈ S then 0 else causalFromIgnoranceRadius Qs t)

theorem causalPartialExecutionBound_univ
    (Qs : Θ → CausalResponse A O) (n : ℕ) :
    causalPartialExecutionBound Qs n Set.univ = 0 := by
  classical
  simp [causalPartialExecutionBound]

/-- Each unexecuted test contributes its own ignorance radius to the bound. -/
theorem causalFromIgnoranceRadius_le_partialExecutionBound
    (Qs : Θ → CausalResponse A O) (n : ℕ) (S : Set (CausalBoundedTest A O n))
    (t : CausalBoundedTest A O n) (ht : t ∉ S) :
    causalFromIgnoranceRadius Qs t ≤ causalPartialExecutionBound Qs n S := by
  classical
  unfold causalPartialExecutionBound
  simpa only [if_neg ht] using
    (Finset.le_sup'
      (fun s : CausalBoundedTest A O n =>
        if s ∈ S then (0 : ℝ) else causalFromIgnoranceRadius Qs s)
      (Finset.mem_univ t))

/-- When an unexecuted test exists, the zero-completed bound is literally
attained by an unexecuted test: it is the paper's maximum over the complement. -/
theorem exists_unexecuted_eq_partialExecutionBound
    [Nonempty Θ] [Nonempty O]
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (n : ℕ) (S : Set (CausalBoundedTest A O n))
    (hmiss : ∃ t, t ∉ S) :
    ∃ t, t ∉ S ∧ causalFromIgnoranceRadius Qs t =
      causalPartialExecutionBound Qs n S := by
  classical
  obtain ⟨t, _, ht⟩ := Finset.exists_mem_eq_sup'
    (Finset.univ_nonempty :
      (Finset.univ : Finset (CausalBoundedTest A O n)).Nonempty)
    (fun s : CausalBoundedTest A O n =>
      if s ∈ S then (0 : ℝ) else causalFromIgnoranceRadius Qs s)
  change causalPartialExecutionBound Qs n S =
    (if t ∈ S then 0 else causalFromIgnoranceRadius Qs t) at ht
  by_cases hs : t ∈ S
  · rw [if_pos hs] at ht
    obtain ⟨s, hs⟩ := hmiss
    refine ⟨s, hs, le_antisymm
      (causalFromIgnoranceRadius_le_partialExecutionBound Qs n S s hs) ?_⟩
    rw [ht]
    exact finiteDeficiency_nonneg_of_valid _ _ finiteIgnoranceExperiment_valid
      (causalPlanObservationExperiment_valid s.1.1 s.2 Qs hQ)
  · exact ⟨t, hs, (ht.trans (if_neg hs)).symm⟩

/-- The geometric partial-execution bound. Exact simulation of the executed
tests is an explicit input here; the fixed-schedule theorem below discharges
that input from actual causal policy agreement. -/
theorem causalNativeDeficiencyUpTo_le_partialExecution
    [Fintype X] [Nonempty Θ] [Nonempty O]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (n : ℕ) (S : Set (CausalBoundedTest A O n))
    (hexec : ∀ t ∈ S, FiniteBlackwellLE
      (causalPlanObservationExperiment t.1.1 t.2 Qs) E) :
    causalNativeDeficiencyUpTo E Qs n ≤ causalPartialExecutionBound Qs n S := by
  classical
  apply csSup_le (causalNativeDeficiencyValuesUpTo_nonempty E Qs n)
  rintro d ⟨m, hmn, τ, rfl⟩
  let t : CausalBoundedTest A O n := ⟨⟨m, Nat.lt_succ_of_le hmn⟩, τ⟩
  have hle : (if t ∈ S then 0 else causalFromIgnoranceRadius Qs t) ≤
      causalPartialExecutionBound Qs n S := by
    unfold causalPartialExecutionBound
    exact Finset.le_sup'
      (fun s : CausalBoundedTest A O n =>
        if s ∈ S then (0 : ℝ) else causalFromIgnoranceRadius Qs s)
      (Finset.mem_univ t)
  by_cases ht : t ∈ S
  · rw [if_pos ht] at hle
    rw [finiteDeficiency_eq_zero_of_blackwellLE E _ hE
      (causalPlanObservationExperiment_valid m τ Qs hQ) (hexec t ht)]
    exact hle
  · rw [if_neg ht] at hle
    exact (finiteDeficiency_le_from_ignorance E _ hE
      (causalPlanObservationExperiment_valid m τ Qs hQ)).trans hle

/-- Sharpness in part (c): a maximizing unexecuted test with a pair of
identical acquired rows and target half-separation equal to its radius
forces equality in the partial-execution certificate. -/
theorem causalNativeDeficiencyUpTo_eq_partialExecution_of_pair
    [Fintype X] [Nonempty Θ] [Nonempty O]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (n : ℕ) (S : Set (CausalBoundedTest A O n))
    (hexec : ∀ t ∈ S, FiniteBlackwellLE
      (causalPlanObservationExperiment t.1.1 t.2 Qs) E)
    (t : CausalBoundedTest A O n) (_ht : t ∉ S)
    (hmax : causalFromIgnoranceRadius Qs t = causalPartialExecutionBound Qs n S)
    (θ θ' : Θ) (hsame : E θ = E θ')
    (hsep : finiteTV (causalPlanObservationExperiment t.1.1 t.2 Qs θ)
      (causalPlanObservationExperiment t.1.1 t.2 Qs θ') / 2 =
        causalFromIgnoranceRadius Qs t) :
    causalNativeDeficiencyUpTo E Qs n = causalPartialExecutionBound Qs n S := by
  apply le_antisymm
  · exact causalNativeDeficiencyUpTo_le_partialExecution E hE Qs hQ n S hexec
  · have hlower := finiteDeficiency_pairwise_lower E
      (causalPlanObservationExperiment t.1.1 t.2 Qs) hE
      (causalPlanObservationExperiment_valid t.1.1 t.2 Qs hQ) θ θ'
    have hzero : finiteTV (E θ) (E θ') = 0 := by simp [hsame, finiteTV]
    rw [hzero, sub_zero, hsep, hmax] at hlower
    apply hlower.trans
    apply le_csSup (causalNativeDeficiencyValuesUpTo_bddAbove E hE Qs hQ n)
    exact ⟨t.1.1, Nat.le_of_lt_succ t.1.2, t.2, rfl⟩

/-! ## Actual causal fixed schedules, with unrestricted suffix behavior -/

/-- A behavior policy executes a native plan when it agrees at every node
of the plan's contingency tree, not just on the realized observation branch.
Nonzero policy likelihood means the history's actions follow the plan; this
condition is independent of the world's observation probabilities, so even
world-null observation branches are included. Histories with incompatible
past actions and histories at or after the target horizon are unrestricted. -/
def CausalPolicyExecutesPlan (ρ : CausalPolicy A O) {m : ℕ}
    (τ : CausalPlan A O m) : Prop :=
  ∀ (h : CausalHistory A O), h.length < m →
    causalPolicyProb (causalPolicyOfPlan m τ) h ≠ 0 → ∀ a,
    ρ h a = causalPolicyOfPlan m τ h a

/-- Agreement on every target-tree node makes all prefix policy likelihoods
identical; incompatible action histories have zero likelihood on both sides. -/
theorem causalPolicyProb_eq_of_executesPlan
    (ρ : CausalPolicy A O) {m : ℕ} (τ : CausalPlan A O m)
    (hexec : CausalPolicyExecutesPlan ρ τ)
    (h : CausalHistory A O) (hh : h.length ≤ m) :
    causalPolicyProb ρ h = causalPolicyProb (causalPolicyOfPlan m τ) h := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h ao ih =>
    have hlt : h.length < m := by simpa using hh
    rw [causalPolicyProb_append_singleton, causalPolicyProb_append_singleton,
      ih (by omega)]
    by_cases hp : causalPolicyProb (causalPolicyOfPlan m τ) h = 0
    · simp [hp]
    · rw [hexec h hlt hp ao.1]

/-- Whole-plan agreement gives the actual target prefix law. -/
theorem causalFiniteExperiment_eq_of_executesPlan
    (ρ : CausalPolicy A O) (Qs : Θ → CausalResponse A O)
    {m : ℕ} (τ : CausalPlan A O m) (hexec : CausalPolicyExecutesPlan ρ τ) :
    causalFiniteExperiment ρ Qs m =
      causalFiniteExperiment (causalPolicyOfPlan m τ) Qs m := by
  funext θ w
  unfold causalFiniteExperiment
  rw [causalTraceProb_factor, causalTraceProb_factor]
  congr 1
  exact causalPolicyProb_eq_of_executesPlan ρ τ hexec _ (by simp)

/-- An executed depth-`m` plan is exactly available from the actual full
reset transcript at any episode horizon `H ≥ m`. -/
theorem causalScheduled_plan_blackwell_of_executes
    {I : Type*} [Fintype I] [DecidableEq I]
    (ρ : I → CausalPolicy A O) (hρ : ∀ i, IsCausalPolicy (ρ i))
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {m H : ℕ} (hmH : m ≤ H) (τ : CausalPlan A O m) (k : I)
    (hexec : CausalPolicyExecutesPlan (ρ k) τ) :
    FiniteBlackwellLE (causalPlanObservationExperiment m τ Qs)
      (causalScheduledEpisodicExperiment ρ Qs H) := by
  apply causalScheduled_target_blackwell ρ hρ Qs hQ H k
  apply finiteBlackwellLE_trans ?_
    (causalFiniteExperiment_prefix_blackwell_of_le (ρ k) (hρ k) Qs hQ hmH)
  rw [causalFiniteExperiment_eq_of_executesPlan (ρ k) Qs τ hexec]
  exact (causalPlan_full_observation_blackwell_equiv m τ Qs).1

/-- Part (c) on the actual fixed-schedule causal transcript. Each named
test may be executed by a different episode, and shorter tests are included. -/
theorem causalNativeDeficiencyUpTo_causalScheduled_le_partialExecution
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty Θ] [Nonempty O]
    (ρ : I → CausalPolicy A O) (hρ : ∀ i, IsCausalPolicy (ρ i))
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {n H : ℕ} (hnH : n ≤ H) (S : Set (CausalBoundedTest A O n))
    (hexec : ∀ t ∈ S, ∃ k, CausalPolicyExecutesPlan (ρ k) t.2) :
    causalNativeDeficiencyUpTo (causalScheduledEpisodicExperiment ρ Qs H) Qs n ≤
      causalPartialExecutionBound Qs n S := by
  apply causalNativeDeficiencyUpTo_le_partialExecution _
    (causalScheduledEpisodicExperiment_valid ρ hρ Qs hQ H) Qs hQ n S
  intro t ht
  obtain ⟨k, hk⟩ := hexec t ht
  exact causalScheduled_plan_blackwell_of_executes ρ hρ Qs hQ
    ((Nat.le_of_lt_succ t.1.2).trans hnH) t.2 k hk

/-- The sharpness criterion on the actual fixed-schedule causal transcript;
the indistinguishability hypothesis concerns its literal acquired rows. -/
theorem causalNativeDeficiencyUpTo_causalScheduled_eq_partialExecution_of_pair
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty Θ] [Nonempty O]
    (ρ : I → CausalPolicy A O) (hρ : ∀ i, IsCausalPolicy (ρ i))
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {n H : ℕ} (hnH : n ≤ H) (S : Set (CausalBoundedTest A O n))
    (hexec : ∀ t ∈ S, ∃ k, CausalPolicyExecutesPlan (ρ k) t.2)
    (t : CausalBoundedTest A O n) (ht : t ∉ S)
    (hmax : causalFromIgnoranceRadius Qs t = causalPartialExecutionBound Qs n S)
    (θ θ' : Θ)
    (hsame : causalScheduledEpisodicExperiment ρ Qs H θ =
      causalScheduledEpisodicExperiment ρ Qs H θ')
    (hsep : finiteTV (causalPlanObservationExperiment t.1.1 t.2 Qs θ)
      (causalPlanObservationExperiment t.1.1 t.2 Qs θ') / 2 =
        causalFromIgnoranceRadius Qs t) :
    causalNativeDeficiencyUpTo (causalScheduledEpisodicExperiment ρ Qs H) Qs n =
      causalPartialExecutionBound Qs n S := by
  apply causalNativeDeficiencyUpTo_eq_partialExecution_of_pair _
    (causalScheduledEpisodicExperiment_valid ρ hρ Qs hQ H) Qs hQ n S ?_
    t ht hmax θ θ' hsame hsep
  intro s hs
  obtain ⟨k, hk⟩ := hexec s hs
  exact causalScheduled_plan_blackwell_of_executes ρ hρ Qs hQ
    ((Nat.le_of_lt_succ s.1.2).trans hnH) s.2 k hk

end

end IdExp
