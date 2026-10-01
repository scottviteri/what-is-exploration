import Formal.CompactAdmissibilityModulus
import Formal.SilentHorizonProfileCompact

/-!
# The fixed-horizon policy polytope is a uniformly row-continuous compact family

The paper's application of the compact admissibility modulus: "for all
randomized policies at a fixed finite horizon, the finite product of policy
simplexes is compact and its full-record experiment map is continuous in
uniform row-TV".  The repository already has the compact bounded policy-row
polytope `SilentHorizonPolicyRows A O H`, its extension to valid policies, and
the policy-perturbation bound

`TV(K_x(θ), K_y(θ)) ≤ H · (|A|/2) · dist x y`

uniformly over an arbitrary response-world class.  This module packages those
facts as a `UniformRowFamily` and derives the joint optimization/dominance
tolerance for every continuous score that strictly preserves Blackwell
domination on horizon-`H` complete records: an `η`-optimal policy table
simulates every `ρ`-dominating table within `ε`.  No prior, finite world
class, decoder attainment, or rate is assumed; the score's strictness is a
hypothesis discharged separately for particular objectives.
-/

namespace IdExp

open Set Filter Topology

noncomputable section

set_option linter.unusedSectionVars false

variable {A O Θ : Type*} [Fintype A] [Fintype O] [Nonempty A] [Nonempty O] [Nonempty Θ]

/-- The complete horizon-`H` recorded experiment of a bounded policy table. -/
def policyRowExperiment (Qs : Θ → CausalResponse A O) (H : ℕ)
    (x : SilentHorizonPolicyRows A O H) : FiniteExperiment Θ (CausalFiniteTrace A O H) :=
  causalFiniteExperiment (silentHorizonPolicyOfRows H x).1 Qs H

omit [Nonempty Θ] in
/-- Restricting and extending a policy preserves its complete finite record. -/
theorem policyRowExperiment_rowsOfPolicy (Qs : Θ → CausalResponse A O)
    (H : ℕ) (π : ValidCausalPolicy A O) :
    policyRowExperiment Qs H (silentHorizonRowsOfPolicy H π) =
      causalFiniteExperiment π.1 Qs H := by
  unfold policyRowExperiment silentHorizonPolicyOfRows
  rw [causalFiniteExperiment_boundedCausalPolicy]
  simpa [silentHorizonRowsOfPolicy] using
    (causalFiniteExperiment_eq_boundedCausalTraceMass Qs π H).symm

theorem policyRowExperiment_valid (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (H : ℕ) (x : SilentHorizonPolicyRows A O H) :
    IsFiniteExperiment (policyRowExperiment Qs H x) :=
  causalFiniteExperiment_valid _ (silentHorizonPolicyOfRows H x).2 Qs hQ H

/-- **The policy-row polytope as a uniformly row-continuous family.**  Rows
move by at most `H · (|A|/2) · dist x y`, uniformly in the world. -/
def policyRowFamily (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (H : ℕ) : UniformRowFamily Θ (CausalFiniteTrace A O H) (SilentHorizonPolicyRows A O H) where
  exp := policyRowExperiment Qs H
  valid := policyRowExperiment_valid Qs hQ H
  uniformRow := by
    intro x₀ ε hε
    set C : ℝ := (H : ℝ) * ((Fintype.card A : ℝ) / 2) with hC
    have hC0 : 0 ≤ C := by positivity
    have hr : 0 < ε / (C + 1) := by positivity
    have hev : ∀ᶠ x in 𝓝 x₀, dist x x₀ < ε / (C + 1) :=
      Metric.eventually_nhds_iff.mpr ⟨ε / (C + 1), hr, fun _ h => h⟩
    refine hev.mono fun x hx θ => ?_
    have h := finiteTV_silentHorizonPolicyOfRows_experiment_le Qs hQ H x x₀ θ
    have hCd : C * dist x x₀ ≤ C * (ε / (C + 1)) :=
      mul_le_mul_of_nonneg_left hx.le hC0
    have hfrac : C * (ε / (C + 1)) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity : (0:ℝ) < C + 1)]
      nlinarith
    calc finiteTV (policyRowExperiment Qs H x θ) (policyRowExperiment Qs H x₀ θ)
        ≤ (H : ℝ) * (((Fintype.card A : ℝ) / 2) * dist x x₀) := h
      _ = C * dist x x₀ := by rw [hC]; ring
      _ ≤ ε := hCd.trans hfrac

/-- **Admissibility modulus on the horizon-`H` policy polytope.**  For every
continuous score on policy tables that strictly preserves Blackwell
domination of their complete records, every `ε > 0` has joint tolerances
`η, ρ > 0`: a table simulating another within `ρ` and scoring at most `η`
better is itself simulated within `ε`. -/
theorem policyRow_admissibility_modulus (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (H : ℕ)
    (J : SilentHorizonPolicyRows A O H → ℝ) (hJ : Continuous J)
    (hstrict : ∀ s t, finiteDeficiency (policyRowExperiment Qs H t) (policyRowExperiment Qs H s) = 0 →
      J t ≤ J s → finiteDeficiency (policyRowExperiment Qs H s) (policyRowExperiment Qs H t) = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ s t : SilentHorizonPolicyRows A O H,
      finiteDeficiency (policyRowExperiment Qs H t) (policyRowExperiment Qs H s) ≤ ρ →
        J t ≤ J s + η →
          finiteDeficiency (policyRowExperiment Qs H s) (policyRowExperiment Qs H t) ≤ ε :=
  compact_admissibility_modulus (policyRowFamily Qs hQ H) J hJ hstrict

/-- **Approximately optimal policy tables are approximately admissible.**
An `η`-optimal table for such a score simulates every feasible
`ρ`-dominating table within `ε`. -/
theorem policyRow_eta_optimal_simulates_rho_dominators (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (H : ℕ)
    (J : SilentHorizonPolicyRows A O H → ℝ) (hJ : Continuous J)
    (hstrict : ∀ s t, finiteDeficiency (policyRowExperiment Qs H t) (policyRowExperiment Qs H s) = 0 →
      J t ≤ J s → finiteDeficiency (policyRowExperiment Qs H s) (policyRowExperiment Qs H t) = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ s : SilentHorizonPolicyRows A O H,
      (∀ t, J t ≤ J s + η) →
        ∀ t, finiteDeficiency (policyRowExperiment Qs H t) (policyRowExperiment Qs H s) ≤ ρ →
          finiteDeficiency (policyRowExperiment Qs H s) (policyRowExperiment Qs H t) ≤ ε :=
  eta_optimal_simulates_rho_dominators (policyRowFamily Qs hQ H) J hJ hstrict

/-- Deficiency between two policy tables' records is jointly continuous on
the polytope. -/
theorem continuous_policyRow_deficiency (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (H : ℕ) :
    Continuous (fun p : SilentHorizonPolicyRows A O H × SilentHorizonPolicyRows A O H =>
      finiteDeficiency (policyRowExperiment Qs H p.1) (policyRowExperiment Qs H p.2)) :=
  (policyRowFamily Qs hQ H).continuous_deficiency

end

end IdExp
