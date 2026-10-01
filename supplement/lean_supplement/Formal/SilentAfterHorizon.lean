import Formal.CausalSharedTail
import Formal.CausalSilentTail
import Formal.DeterministicDeficiency

/-!
# Causal classes that become silent after a finite horizon

This module formalizes the structural part of T10(1) in
`TheoryDocs/approach_case_synthesis.tex`.  If every candidate world emits the
same fixed observation after histories of length `H`, then no experiment gains
information after `H`:

* a deterministic native test is Blackwell-equivalent to the restriction of
  its contingency plan to depth `min n H`;
* every acquired experiment at depth `t >= H` is Blackwell-equivalent to the
  acquired depth-`H` experiment; and
* every limiting native-profile coordinate is already its depth-`H`
  deficiency.

The continuation decoder still samples later actions from the policy.  Thus
silence concerns observations, not actions.  The experiment-level proofs use
the more general shared-tail construction in `CausalSharedTail.lean`.
-/

namespace IdExp

open Set

set_option linter.unusedSectionVars false

variable {A O Θ : Type*} [Fintype A] [Fintype O]
  [Nonempty A] [Nonempty O] [Nonempty Θ]

/-- Every world emits the same fixed symbol after histories of length `H`.
This is the literal finite-alphabet form of
`Q(· | h, a) = delta_oStar` used in T10. -/
noncomputable def CausalSilentAfterHorizon (Qs : Θ → CausalResponse A O)
    (H : ℕ) (oStar : O) : Prop := by
  classical
  exact ∀ θ h a o, H ≤ h.length →
    Qs θ h a o = if o = oStar then 1 else 0

/-- A common silent suffix is a special case of a shared causal tail. -/
theorem causalSilentAfterHorizon_hasSharedCausalTail
    [DecidableEq A] [DecidableEq O]
    (Qs : Θ → CausalResponse A O) (H : ℕ) (oStar : O)
    (hsilent : CausalSilentAfterHorizon Qs H oStar) :
    HasSharedCausalTail Qs H (silentSymbolResponse (A := A) oStar) := by
  classical
  intro θ h a o hh
  rw [hsilent θ h a o hh]
  by_cases ho : o = oStar <;> simp [silentSymbolResponse, ho]

/-- Restrict a depth-`n` deterministic contingency plan to the decisions
strictly before `min n H`.  `planAction` completes the finite plan to a
deterministic history policy, and `deterministicPrefixPlan` restricts that
same policy to the shorter horizon. -/
noncomputable def causalPlanTruncation {n : ℕ} (H : ℕ)
    (τ : CausalPlan A O n) : CausalPlan A O (min n H) :=
  deterministicPrefixPlan (planAction n τ) (min n H)

/-- Package deterministic-plan truncation as a truncation of native tests. -/
noncomputable def causalNativeTestTruncation (H : ℕ)
    (q : CausalNativeTest A O) : CausalNativeTest A O :=
  ⟨min q.1 H, causalPlanTruncation H q.2⟩

/-- At the full-trace level, a deterministic plan and its truncated plan are
Blackwell-equivalent whenever the worlds have a shared continuation after
`H`.  Silence is not needed for this more general helper. -/
theorem causalFiniteExperiment_planTruncation_blackwell_equiv
    (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (R : CausalResponse A O) (hR : IsCausalResponse R)
    (H n : ℕ) (τ : CausalPlan A O n)
    (htail : HasSharedCausalTail Qs H R) :
    FiniteBlackwellLE
        (causalFiniteExperiment (causalPolicyOfPlan n τ) Qs n)
        (causalFiniteExperiment
          (causalPolicyOfPlan (min n H) (causalPlanTruncation H τ)) Qs (min n H)) ∧
      FiniteBlackwellLE
        (causalFiniteExperiment
          (causalPolicyOfPlan (min n H) (causalPlanTruncation H τ)) Qs (min n H))
        (causalFiniteExperiment (causalPolicyOfPlan n τ) Qs n) := by
  classical
  let p : CausalHistory A O → A := planAction n τ
  have hn :
      causalFiniteExperiment (causalPolicyOfPlan n τ) Qs n =
        causalFiniteExperiment (detPolicy p) Qs n := by
    rw [causalPolicyOfPlan_eq_detPolicy]
  have hk :
      causalFiniteExperiment
          (causalPolicyOfPlan (min n H) (causalPlanTruncation H τ)) Qs (min n H) =
        causalFiniteExperiment (detPolicy p) Qs (min n H) := by
    simpa only [causalPlanTruncation, p] using
      causalFiniteExperiment_deterministicPrefixPlan p Qs (min n H)
  rcases le_total n H with hnH | hHn
  · have hmin : min n H = n := Nat.min_eq_left hnH
    rw [hn, hk, hmin]
    exact ⟨finiteBlackwellLE_refl _, finiteBlackwellLE_refl _⟩
  · have hmin : min n H = H := Nat.min_eq_right hHn
    have heq := causalFiniteExperiment_sharedTail_blackwell_equiv
      (detPolicy p) (isCausalPolicy_detPolicy p) Qs hQ R hR H htail hHn
    rw [hn, hk, hmin]
    exact heq

/-- Every deterministic native observation test is Blackwell-equivalent to
its depth-`min n H` restriction under a shared causal tail.  The decoder
recursively follows the original plan after the cutoff; in the silent case
its appended observations are all the fixed silent symbol. -/
theorem causalPlanObservationExperiment_planTruncation_blackwell_equiv
    (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (R : CausalResponse A O) (hR : IsCausalResponse R)
    (H n : ℕ) (τ : CausalPlan A O n)
    (htail : HasSharedCausalTail Qs H R) :
    FiniteBlackwellLE
        (causalPlanObservationExperiment n τ Qs)
        (causalPlanObservationExperiment (min n H) (causalPlanTruncation H τ) Qs) ∧
      FiniteBlackwellLE
        (causalPlanObservationExperiment (min n H) (causalPlanTruncation H τ) Qs)
        (causalPlanObservationExperiment n τ Qs) := by
  have hfull := causalFiniteExperiment_planTruncation_blackwell_equiv
    Qs hQ R hR H n τ htail
  have hn := causalPlan_full_observation_blackwell_equiv n τ Qs
  have hk := causalPlan_full_observation_blackwell_equiv
    (min n H) (causalPlanTruncation H τ) Qs
  exact ⟨finiteBlackwellLE_trans (finiteBlackwellLE_trans hn.1 hfull.1) hk.2,
    finiteBlackwellLE_trans (finiteBlackwellLE_trans hk.1 hfull.2) hn.2⟩

/-- T10(1a), stated on the repository's native-test sigma type and under
the paper's literal common-silent-symbol hypothesis. -/
theorem causalNativeTestExperiment_truncation_blackwell_equiv
    (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (H : ℕ) (oStar : O) (hsilent : CausalSilentAfterHorizon Qs H oStar)
    (q : CausalNativeTest A O) :
    FiniteBlackwellLE (causalNativeTestExperiment Qs q)
        (causalNativeTestExperiment Qs (causalNativeTestTruncation H q)) ∧
      FiniteBlackwellLE
        (causalNativeTestExperiment Qs (causalNativeTestTruncation H q))
        (causalNativeTestExperiment Qs q) := by
  classical
  rcases q with ⟨n, τ⟩
  exact causalPlanObservationExperiment_planTruncation_blackwell_equiv
    Qs hQ (silentSymbolResponse (A := A) oStar)
    (silentSymbolResponse_valid oStar) H n τ
    (causalSilentAfterHorizon_hasSharedCausalTail Qs H oStar hsilent)

/-- T10(1b): every acquired experiment after the silent horizon is exactly
Blackwell-equivalent to the horizon-`H` acquired experiment. -/
theorem causalFiniteExperiment_silentAfterHorizon_blackwell_equiv
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (H : ℕ) (oStar : O) (hsilent : CausalSilentAfterHorizon Qs H oStar)
    {t : ℕ} (hHt : H ≤ t) :
    FiniteBlackwellLE (causalFiniteExperiment π Qs t)
        (causalFiniteExperiment π Qs H) ∧
      FiniteBlackwellLE (causalFiniteExperiment π Qs H)
        (causalFiniteExperiment π Qs t) := by
  classical
  exact causalFiniteExperiment_sharedTail_blackwell_equiv π hπ Qs hQ
    (silentSymbolResponse (A := A) oStar) (silentSymbolResponse_valid oStar)
    H (causalSilentAfterHorizon_hasSharedCausalTail Qs H oStar hsilent) hHt

/-! ## Deficiency and profile-coordinate stabilization -/

/-- Source monotonicity of finite deficiency over an arbitrary nonempty
world class, provided the intermediate and target matrices are valid.  This
is the validity-based version needed for T10; unlike the older duality-era
helper it does not assume that the world class is finite. -/
theorem finiteDeficiency_mono_source_of_finiteBlackwellLE_of_valid
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z] [Nonempty Z]
    (E : FiniteExperiment Θ X) (D : FiniteExperiment Θ Y)
    (F : FiniteExperiment Θ Z)
    (hD : IsFiniteExperiment D) (hF : IsFiniteExperiment F)
    (hDE : FiniteBlackwellLE D E) :
    finiteDeficiency E F ≤ finiteDeficiency D F := by
  rcases hDE with ⟨G, hG, heq⟩
  apply le_csInf (finiteDeficiencyCandidates_nonempty_of_valid D F hD hF)
  rintro c ⟨K, hK, herr⟩
  apply finiteDeficiency_le_of_decoder E F (stochasticRuleComp G K)
    (stochasticRuleComp_mem_stochasticRules hG hK) c
  intro θ
  change finiteTV (finiteDecisionLaw E (stochasticRuleComp G K) θ) (F θ) ≤ c
  rw [finiteDecisionLaw_stochasticRuleComp, heq]
  exact herr θ

/-- Blackwell-equivalent valid source encodings have the same deficiency to
every valid finite target, without any finiteness assumption on the world
class. -/
theorem finiteDeficiency_eq_of_source_blackwellEquiv_of_valid
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z] [Nonempty Z]
    (E : FiniteExperiment Θ X) (D : FiniteExperiment Θ Y)
    (F : FiniteExperiment Θ Z)
    (hE : IsFiniteExperiment E) (hD : IsFiniteExperiment D)
    (hF : IsFiniteExperiment F)
    (hED : FiniteBlackwellLE E D) (hDE : FiniteBlackwellLE D E) :
    finiteDeficiency E F = finiteDeficiency D F := by
  exact le_antisymm
    (finiteDeficiency_mono_source_of_finiteBlackwellLE_of_valid E D F hD hF hDE)
    (finiteDeficiency_mono_source_of_finiteBlackwellLE_of_valid D E F hE hF hED)

/-- From horizon `H` onward, deficiency from the acquired experiment to any
fixed native target is literally constant. -/
theorem causalPolicyTestDeficiency_silentAfterHorizon_eq
    (π : ValidCausalPolicy A O)
    (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (H : ℕ) (oStar : O) (hsilent : CausalSilentAfterHorizon Qs H oStar)
    (q : CausalNativeTest A O) {t : ℕ} (hHt : H ≤ t) :
    causalPolicyTestDeficiency π Qs q t =
      causalPolicyTestDeficiency π Qs q H := by
  classical
  have heq := causalFiniteExperiment_silentAfterHorizon_blackwell_equiv
    π.1 π.2 Qs hQ H oStar hsilent hHt
  exact finiteDeficiency_eq_of_source_blackwellEquiv_of_valid
    (causalFiniteExperiment π.1 Qs t)
    (causalFiniteExperiment π.1 Qs H)
    (causalNativeTestExperiment Qs q)
    (causalFiniteExperiment_valid π.1 π.2 Qs hQ t)
    (causalFiniteExperiment_valid π.1 π.2 Qs hQ H)
    (causalNativeTestExperiment_valid Qs hQ q) heq.1 heq.2

/-- T10(1c): the limiting profile coordinate is already attained by the
depth-`H` acquired experiment. -/
theorem causalPolicyProfileValue_silentAfterHorizon_eq
    (π : ValidCausalPolicy A O)
    (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (e : ℕ ≃ CausalNativeTest A O)
    (H : ℕ) (oStar : O) (hsilent : CausalSilentAfterHorizon Qs H oStar)
    (j : ℕ) :
    causalPolicyProfileValue π Qs e j =
      causalPolicyTestDeficiency π Qs (e j) H := by
  let f : ℕ → ℝ := causalPolicyTestDeficiency π Qs (e j)
  have hbdd : BddBelow (Set.range f) := by
    refine ⟨0, ?_⟩
    rintro d ⟨t, rfl⟩
    exact finiteDeficiency_nonneg_of_valid
      (causalFiniteExperiment π.1 Qs t)
      (causalNativeTestExperiment Qs (e j))
      (causalFiniteExperiment_valid π.1 π.2 Qs hQ t)
      (causalNativeTestExperiment_valid Qs hQ (e j))
  apply le_antisymm
  · exact csInf_le hbdd ⟨H, rfl⟩
  · apply le_csInf (Set.range_nonempty f)
    rintro d ⟨t, rfl⟩
    by_cases htH : t ≤ H
    · exact causalPolicyTestDeficiency_antitone π Qs hQ (e j) htH
    · have hHt : H ≤ t := Nat.le_of_lt (Nat.lt_of_not_ge htH)
      exact le_of_eq (causalPolicyTestDeficiency_silentAfterHorizon_eq
        π Qs hQ H oStar hsilent (e j) hHt).symm

/-- The same stabilization statement at the bundled profile-cube level. -/
theorem causalPolicyProfile_silentAfterHorizon_coe
    (π : ValidCausalPolicy A O)
    (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (e : ℕ ≃ CausalNativeTest A O)
    (H : ℕ) (oStar : O) (hsilent : CausalSilentAfterHorizon Qs H oStar)
    (j : ℕ) :
    ((causalPolicyProfile Qs hQ e π j : Set.Icc (0 : ℝ) 1) : ℝ) =
      causalPolicyTestDeficiency π Qs (e j) H := by
  rw [causalPolicyProfile_coe,
    causalPolicyProfileValue_silentAfterHorizon_eq π Qs hQ e H oStar hsilent j]

end IdExp
