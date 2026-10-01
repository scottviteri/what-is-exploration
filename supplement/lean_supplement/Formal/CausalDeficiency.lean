import Formal.CausalUniversality
import Formal.DualCertificate

/-!
# Directed deficiency form of finite-horizon causal universality

This module closes the outer order-theoretic layer of the paper's
finite-horizon universality theorem. It turns the fixed-error decoder theorem
from CausalUniversality into an exact equality between:

* the finite maximum of deficiencies to deterministic observation tests at
  the terminal horizon; and
* the supremum of deficiencies to full-trace experiments induced by every
  behavioral causal policy at every shorter horizon.

The proof keeps the world class arbitrary and nonempty. Its substantive steps
are the deficiency-infimum approximation within positive eta, exact
observation/full-trace Blackwell equivalence for deterministic plans, Kuhn
mixture decoding, repeated prefix marginalization, and the limit eta down to
zero.
-/

set_option linter.unusedSectionVars false

namespace IdExp

open Finset Set

variable {A O Θ X : Type*} [Fintype A] [Fintype O] [Fintype X]

/-- The paper's Gamma at depth n, written as the actual finite maximum over
depth-n deterministic native observation experiments. Shorter deterministic
tests need not be listed separately because they extend to depth n and are
prefix marginals; the theorem below proves the stronger all-policy statement. -/
noncomputable def causalNativeDeficiency [Nonempty A]
    (E : FiniteExperiment Θ X) (Qs : Θ → CausalResponse A O) (n : ℕ) : ℝ := by
  classical
  exact (Finset.univ : Finset (CausalPlan A O n)).sup'
    Finset.univ_nonempty
    (fun τ => finiteDeficiency E (causalPlanObservationExperiment n τ Qs))

/-- Every deterministic depth-n native test is bounded by Gamma. -/
theorem finiteDeficiency_causalPlan_le_native [Nonempty A]
    (E : FiniteExperiment Θ X) (Qs : Θ → CausalResponse A O)
    (n : ℕ) (τ : CausalPlan A O n) :
    finiteDeficiency E (causalPlanObservationExperiment n τ Qs) ≤
      causalNativeDeficiency E Qs n := by
  classical
  unfold causalNativeDeficiency
  exact Finset.le_sup'
    (fun τ' : CausalPlan A O n =>
      finiteDeficiency E (causalPlanObservationExperiment n τ' Qs)) (Finset.mem_univ τ)

/-- Because the plan family is finite and nonempty, some deterministic plan
attains Gamma exactly. -/
theorem exists_causalPlan_eq_nativeDeficiency [Nonempty A]
    (E : FiniteExperiment Θ X) (Qs : Θ → CausalResponse A O) (n : ℕ) :
    ∃ τ : CausalPlan A O n,
      causalNativeDeficiency E Qs n =
        finiteDeficiency E (causalPlanObservationExperiment n τ Qs) := by
  classical
  unfold causalNativeDeficiency
  obtain ⟨τ, _, hτ⟩ := Finset.exists_mem_eq_sup'
    (Finset.univ_nonempty : (Finset.univ :
      Finset (CausalPlan A O n)).Nonempty)
    (fun τ => finiteDeficiency E (causalPlanObservationExperiment n τ Qs))
  exact ⟨τ, hτ⟩

/-- The observation-only and full-trace encodings of a deterministic plan
have exactly the same directed deficiency from every valid source experiment. -/
theorem finiteDeficiency_causalPlanObservation_eq_full
    [Nonempty A] [Nonempty O] [Nonempty Θ]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (n : ℕ) (τ : CausalPlan A O n) :
    finiteDeficiency E (causalPlanObservationExperiment n τ Qs) =
      finiteDeficiency E
        (causalFiniteExperiment (causalPolicyOfPlan n τ) Qs n) := by
  exact finiteDeficiency_eq_of_target_blackwellEquiv E
    (causalPlanObservationExperiment n τ Qs)
    (causalFiniteExperiment (causalPolicyOfPlan n τ) Qs n)
    hE
    (causalPlanObservationExperiment_valid n τ Qs hQ)
    (causalFiniteExperiment_valid (causalPolicyOfPlan n τ)
      (isCausalPolicy_causalPolicyOfPlan n τ) Qs hQ n)
    (causalPlan_full_observation_blackwell_equiv n τ Qs).1
    (causalPlan_full_observation_blackwell_equiv n τ Qs).2

/-- At one fixed horizon, every behavioral policy experiment has deficiency
at most Gamma. This is where the decoder infima are approached within eta,
mixed using the world-independent Kuhn weights, and eta is sent to zero. -/
theorem finiteDeficiency_causalPolicy_le_native_at_horizon
    [Nonempty A] [Nonempty O] [Nonempty Θ]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (n : ℕ) :
    finiteDeficiency E (causalFiniteExperiment π Qs n) ≤
      causalNativeDeficiency E Qs n := by
  classical
  apply le_of_forall_pos_le_add
  intro η hη
  have hplans : ∀ τ : CausalPlan A O n,
      ∃ G ∈ stochasticRules X (CausalObservationTrace O n),
        ∀ θ, decodeErr E (causalPlanObservationExperiment n τ Qs) G θ ≤
          causalNativeDeficiency E Qs n + η := by
    intro τ
    obtain ⟨G, hG, herr⟩ :=
      exists_decoder_le_finiteDeficiency_add E
        (causalPlanObservationExperiment n τ Qs) hE
        (causalPlanObservationExperiment_valid n τ Qs hQ) hη
    refine ⟨G, hG, ?_⟩
    intro θ
    exact (herr θ).trans (by
      simpa [add_comm] using add_le_add_right
        (finiteDeficiency_causalPlan_le_native E Qs n τ) η)
  obtain ⟨G, hG, herr⟩ :=
    exists_decoder_to_causalPolicy_of_observation_plan_decoders
      E π hπ Qs n (causalNativeDeficiency E Qs n + η) hplans
  exact finiteDeficiency_le_of_decoder E
    (causalFiniteExperiment π Qs n) G hG
    (causalNativeDeficiency E Qs n + η) herr

/-- Every shorter-horizon behavioral-policy experiment is also bounded by the
depth-n native maximum. The longer experiment is first decoded and then
garbled by the exact prefix projection. -/
theorem finiteDeficiency_causalPolicy_le_native_of_le
    [Nonempty A] [Nonempty O] [Nonempty Θ]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {t n : ℕ} (htn : t ≤ n) :
    finiteDeficiency E (causalFiniteExperiment π Qs t) ≤
      causalNativeDeficiency E Qs n := by
  obtain ⟨H, hH, hEq⟩ :=
    causalFiniteExperiment_prefix_blackwell_of_le π hπ Qs hQ htn
  rw [← hEq]
  exact (finiteDeficiency_decisionLaw_le E
    (causalFiniteExperiment π Qs n) hE
    (causalFiniteExperiment_valid π hπ Qs hQ n) H hH).trans
    (finiteDeficiency_causalPolicy_le_native_at_horizon
      E hE π hπ Qs hQ n)


/-- Deficiencies to deterministic native observation interventions at every
horizon at most n. This is the literal set in the paper's definition of
Gamma_{<=n}. -/
def causalNativeDeficiencyValuesUpTo [Nonempty A]
    (E : FiniteExperiment Θ X) (Qs : Θ → CausalResponse A O) (n : ℕ) :
    Set ℝ :=
  {d | ∃ m, m ≤ n ∧ ∃ τ : CausalPlan A O m,
    d = finiteDeficiency E (causalPlanObservationExperiment m τ Qs)}

/-- The paper's literal maximum-over-shorter-tests quantity, represented as a
supremum before proving that the terminal-horizon finite maximum attains it. -/
noncomputable def causalNativeDeficiencyUpTo [Nonempty A]
    (E : FiniteExperiment Θ X) (Qs : Θ → CausalResponse A O) (n : ℕ) : ℝ :=
  sSup (causalNativeDeficiencyValuesUpTo E Qs n)

/-- Deficiency values attained by valid causal policies at horizons at most n. -/
def causalPolicyDeficiencyValuesUpTo
    (E : FiniteExperiment Θ X) (Qs : Θ → CausalResponse A O) (n : ℕ) :
    Set ℝ :=
  {d | ∃ t, t ≤ n ∧ ∃ π : CausalPolicy A O,
    IsCausalPolicy π ∧
      d = finiteDeficiency E (causalFiniteExperiment π Qs t)}

/-- The outer supremum on the right side of the paper's displayed equality. -/
noncomputable def causalPolicyDeficiencyUpTo
    (E : FiniteExperiment Θ X) (Qs : Θ → CausalResponse A O) (n : ℕ) : ℝ :=
  sSup (causalPolicyDeficiencyValuesUpTo E Qs n)

theorem causalPolicyDeficiencyValuesUpTo_nonempty [Nonempty A]
    (E : FiniteExperiment Θ X) (Qs : Θ → CausalResponse A O) (n : ℕ) :
    (causalPolicyDeficiencyValuesUpTo E Qs n).Nonempty := by
  classical
  let τ : CausalPlan A O n := Classical.arbitrary _
  let π : CausalPolicy A O := causalPolicyOfPlan n τ
  exact ⟨finiteDeficiency E (causalFiniteExperiment π Qs n),
    n, le_rfl, π, isCausalPolicy_causalPolicyOfPlan n τ, rfl⟩

theorem causalPolicyDeficiencyValuesUpTo_bddAbove
    [Nonempty A] [Nonempty O] [Nonempty Θ]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (n : ℕ) :
    BddAbove (causalPolicyDeficiencyValuesUpTo E Qs n) := by
  refine ⟨causalNativeDeficiency E Qs n, ?_⟩
  rintro d ⟨t, htn, π, hπ, rfl⟩
  exact finiteDeficiency_causalPolicy_le_native_of_le
    E hE π hπ Qs hQ htn

theorem causalNativeDeficiencyValuesUpTo_nonempty [Nonempty A]
    (E : FiniteExperiment Θ X) (Qs : Θ → CausalResponse A O) (n : ℕ) :
    (causalNativeDeficiencyValuesUpTo E Qs n).Nonempty := by
  classical
  let τ : CausalPlan A O n := Classical.arbitrary _
  exact ⟨finiteDeficiency E (causalPlanObservationExperiment n τ Qs),
    n, le_rfl, τ, rfl⟩

theorem causalNativeDeficiencyValuesUpTo_bddAbove
    [Nonempty A] [Nonempty O] [Nonempty Θ]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (n : ℕ) :
    BddAbove (causalNativeDeficiencyValuesUpTo E Qs n) := by
  refine ⟨causalNativeDeficiency E Qs n, ?_⟩
  rintro d ⟨m, hmn, τ, rfl⟩
  rw [finiteDeficiency_causalPlanObservation_eq_full E hE Qs hQ m τ]
  exact finiteDeficiency_causalPolicy_le_native_of_le E hE
    (causalPolicyOfPlan m τ) (isCausalPolicy_causalPolicyOfPlan m τ)
    Qs hQ hmn

/-- Taking the supremum over all shorter deterministic native tests adds no
value beyond the finite maximum at depth n: shorter tests are exact prefix
garblings, while every depth-n plan is already in the shorter-test set. -/
theorem causalNativeDeficiencyUpTo_eq_terminal
    [Nonempty A] [Nonempty O] [Nonempty Θ]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (n : ℕ) :
    causalNativeDeficiencyUpTo E Qs n =
      causalNativeDeficiency E Qs n := by
  unfold causalNativeDeficiencyUpTo
  apply le_antisymm
  · apply csSup_le (causalNativeDeficiencyValuesUpTo_nonempty E Qs n)
    rintro d ⟨m, hmn, τ, rfl⟩
    rw [finiteDeficiency_causalPlanObservation_eq_full E hE Qs hQ m τ]
    exact finiteDeficiency_causalPolicy_le_native_of_le E hE
      (causalPolicyOfPlan m τ) (isCausalPolicy_causalPolicyOfPlan m τ)
      Qs hQ hmn
  · obtain ⟨τ, hτ⟩ := exists_causalPlan_eq_nativeDeficiency E Qs n
    rw [hτ]
    apply le_csSup
      (causalNativeDeficiencyValuesUpTo_bddAbove E hE Qs hQ n)
    exact ⟨n, le_rfl, τ, rfl⟩

/-- Terminal-horizon maximum form of finite-horizon universality.

For any nonempty, possibly infinite world class, the maximum directed
deficiency from E to a deterministic native observation intervention at
depth n equals the supremum of directed deficiencies from E to the full-trace
experiment induced by every randomized causal policy at every horizon t at
most n. -/
theorem causalNativeDeficiency_eq_policyDeficiencyUpTo
    [Nonempty A] [Nonempty O] [Nonempty Θ]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (n : ℕ) :
    causalNativeDeficiency E Qs n =
      causalPolicyDeficiencyUpTo E Qs n := by
  unfold causalPolicyDeficiencyUpTo
  apply le_antisymm
  · obtain ⟨τ, hτ⟩ := exists_causalPlan_eq_nativeDeficiency E Qs n
    rw [hτ, finiteDeficiency_causalPlanObservation_eq_full E hE Qs hQ n τ]
    apply le_csSup
      (causalPolicyDeficiencyValuesUpTo_bddAbove E hE Qs hQ n)
    exact ⟨n, le_rfl, causalPolicyOfPlan n τ,
      isCausalPolicy_causalPolicyOfPlan n τ, rfl⟩
  · apply csSup_le (causalPolicyDeficiencyValuesUpTo_nonempty E Qs n)
    rintro d ⟨t, htn, π, hπ, rfl⟩
    exact finiteDeficiency_causalPolicy_le_native_of_le
      E hE π hπ Qs hQ htn

/-- **Finite-horizon causal universality, exact deficiency form.**

For any nonempty, possibly infinite world class, the supremum over
deterministic native observation interventions at every horizon m <= n equals
the supremum over full-trace experiments induced by every valid randomized
causal policy at every horizon t <= n. The left supremum is in fact a finite
maximum attained by a depth-n plan. -/
theorem causal_finiteHorizonUniversality
    [Nonempty A] [Nonempty O] [Nonempty Θ]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (n : ℕ) :
    causalNativeDeficiencyUpTo E Qs n =
      causalPolicyDeficiencyUpTo E Qs n := by
  calc
    causalNativeDeficiencyUpTo E Qs n =
        causalNativeDeficiency E Qs n :=
      causalNativeDeficiencyUpTo_eq_terminal E hE Qs hQ n
    _ = causalPolicyDeficiencyUpTo E Qs n :=
      causalNativeDeficiency_eq_policyDeficiencyUpTo E hE Qs hQ n

/-- Operational epsilon form of the exact equality: Gamma is at most epsilon
exactly when every valid behavioral policy experiment at every shorter
horizon has deficiency at most epsilon. -/
theorem causalNativeDeficiency_le_iff_all_policy
    [Nonempty A] [Nonempty O] [Nonempty Θ]
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (n : ℕ) (ε : ℝ) :
    causalNativeDeficiencyUpTo E Qs n ≤ ε ↔
      ∀ (π : CausalPolicy A O), IsCausalPolicy π →
        ∀ t, t ≤ n →
          finiteDeficiency E (causalFiniteExperiment π Qs t) ≤ ε := by
  rw [causalNativeDeficiencyUpTo_eq_terminal E hE Qs hQ n]
  constructor
  · intro hGamma π hπ t htn
    exact (finiteDeficiency_causalPolicy_le_native_of_le
      E hE π hπ Qs hQ htn).trans hGamma
  · intro hall
    obtain ⟨τ, hτ⟩ := exists_causalPlan_eq_nativeDeficiency E Qs n
    rw [hτ, finiteDeficiency_causalPlanObservation_eq_full E hE Qs hQ n τ]
    exact hall (causalPolicyOfPlan n τ)
      (isCausalPolicy_causalPolicyOfPlan n τ) n le_rfl

end IdExp
