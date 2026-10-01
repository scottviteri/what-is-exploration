import Formal.ApproximateResetWord

/-!
# Variable reset schedules and asymptotically exact collapse

The reset word and its length may change at every block. The actual policy
uses the same prefix-compatible construction as exact reset scheduling,
with each local block containing its own reset word. The finite projection
bound is then applied to the true finite-prefix experiment. Vanishing reset
errors give the written Pareto-attainment conclusion for convergent schemes.
-/

namespace IdExp

open Finset Set Filter Topology
open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

variable {A O Θ : Type*} [Fintype A] [Fintype O]
  [Nonempty A] [Nonempty O] [Nonempty Θ]

theorem causalResetSplicePolicy_empty (m : ℕ) (ρ π : CausalPolicy A O) :
    causalResetSplicePolicy m ρ (Fin.elim0 : Fin 0 → A) π =
      causalSplicePolicy m ρ π := by
  funext h
  by_cases hm : h.length < m <;>
    simp [causalResetSplicePolicy, causalSplicePolicy, causalResetPrefixPolicy, hm]

/-- Resetting at the start of the local block is identical to resetting at
the global splice time; local-history dropping does not alter the word. -/
theorem causalSplicePolicy_resetBlock {ℓ : ℕ} (m : ℕ)
    (ρ ρ₀ π : CausalPolicy A O) (r : Fin ℓ → A) :
    causalSplicePolicy m ρ (causalResetSplicePolicy 0 ρ₀ r π) =
      causalResetSplicePolicy m ρ r π := by
  funext h
  by_cases hm : h.length < m
  · have hmℓ : h.length < m + ℓ := by omega
    simp [causalSplicePolicy, causalResetSplicePolicy, causalResetPrefixPolicy, hm, hmℓ]
  · by_cases hmℓ : h.length < m + ℓ
    · have hsub : h.length - m < ℓ := by omega
      simp [causalSplicePolicy, causalResetSplicePolicy, causalResetPrefixPolicy,
        hm, hmℓ, List.length_drop, hsub]
    · have hsub : ¬ h.length - m < ℓ := by omega
      have hcomm : ¬ h.length < ℓ + m := by omega
      simp [causalSplicePolicy, causalResetSplicePolicy, hm, hcomm,
        List.length_drop, hsub, List.drop_drop, Nat.add_comm]

/-- Local policy for reset word `r k` followed by target `π k`. -/
def varyingResetBlockPolicies (ℓ : ℕ → ℕ) (r : (k : ℕ) → Fin (ℓ k) → A)
    (π : ℕ → ValidCausalPolicy A O) (k : ℕ) : ValidCausalPolicy A O :=
  ⟨causalResetSplicePolicy 0 defaultValidCausalPolicy.1 (r k) (π k).1,
    causalResetSplicePolicy_valid 0 _ defaultValidCausalPolicy.2 (r k) (π k).1 (π k).2⟩

/-- Cumulative duration of the first `k` variable reset/target blocks. -/
def varyingResetClock (ℓ t : ℕ → ℕ) (k : ℕ) : ℕ :=
  uniformResetClock 0 (fun i => ℓ i + t i) k

theorem varyingResetClock_succ (ℓ t : ℕ → ℕ) (k : ℕ) :
    varyingResetClock ℓ t (k + 1) = (varyingResetClock ℓ t k + ℓ k) + t k := by
  simp [varyingResetClock, uniformResetClock_succ, Nat.add_assoc]

/-- An actual infinite one-run policy with a possibly different reset word
at every stage, again without an artificial positive-duration condition. -/
def varyingResetSchedulePolicy (ℓ : ℕ → ℕ) (r : (k : ℕ) → Fin (ℓ k) → A)
    (π : ℕ → ValidCausalPolicy A O) (t : ℕ → ℕ) : CausalPolicy A O :=
  uniformResetSchedulePolicy (Fin.elim0 : Fin 0 → A)
    (varyingResetBlockPolicies ℓ r π) (fun k => ℓ k + t k)

theorem varyingResetSchedulePolicy_valid (ℓ : ℕ → ℕ)
    (r : (k : ℕ) → Fin (ℓ k) → A) (π : ℕ → ValidCausalPolicy A O) (t : ℕ → ℕ) :
    IsCausalPolicy (varyingResetSchedulePolicy ℓ r π t) :=
  uniformResetSchedulePolicy_valid _ _ _

/-- Finite-stage prefix acquisition preceding reset `k`. -/
def varyingResetPrefixPolicy (ℓ : ℕ → ℕ) (r : (k : ℕ) → Fin (ℓ k) → A)
    (π : ℕ → ValidCausalPolicy A O) (t : ℕ → ℕ) (k : ℕ) : ValidCausalPolicy A O :=
  uniformResetApproxPolicy (Fin.elim0 : Fin 0 → A)
    (varyingResetBlockPolicies ℓ r π) (fun i => ℓ i + t i) k

/-- The actual prefix ending at stage `k` is the concrete finite reset
splice, so subsequent bounds do not assume a conditional block law. -/
theorem varyingResetSchedule_experiment_eq (ℓ : ℕ → ℕ)
    (r : (k : ℕ) → Fin (ℓ k) → A) (π : ℕ → ValidCausalPolicy A O) (t : ℕ → ℕ)
    (Qs : Θ → CausalResponse A O) (k : ℕ) :
    causalFiniteExperiment (varyingResetSchedulePolicy ℓ r π t) Qs
      ((varyingResetClock ℓ t k + ℓ k) + t k) =
    causalFiniteExperiment
      (causalResetSplicePolicy (varyingResetClock ℓ t k)
        (varyingResetPrefixPolicy ℓ r π t k).1 (r k) (π k).1)
      Qs ((varyingResetClock ℓ t k + ℓ k) + t k) := by
  have heq := uniformResetSchedule_experiment_eq (Fin.elim0 : Fin 0 → A)
    (varyingResetBlockPolicies ℓ r π) (fun i => ℓ i + t i) Qs (k + 1)
  change causalFiniteExperiment (varyingResetSchedulePolicy ℓ r π t) Qs
    (varyingResetClock ℓ t (k + 1)) =
    causalFiniteExperiment
      (uniformResetApproxPolicy (Fin.elim0 : Fin 0 → A)
        (varyingResetBlockPolicies ℓ r π) (fun i => ℓ i + t i) (k + 1)).1
      Qs (varyingResetClock ℓ t (k + 1)) at heq
  rw [varyingResetClock_succ] at heq
  apply heq.trans
  apply congrArg (fun ρ => causalFiniteExperiment ρ Qs
    ((varyingResetClock ℓ t k + ℓ k) + t k))
  change causalResetSplicePolicy (varyingResetClock ℓ t k)
    (varyingResetPrefixPolicy ℓ r π t k).1 (Fin.elim0 : Fin 0 → A)
    (causalResetSplicePolicy 0 defaultValidCausalPolicy.1 (r k) (π k).1) = _
  rw [causalResetSplicePolicy_empty, causalSplicePolicy_resetBlock]

/-- The stage-`k` projection of the actual infinite run has worldwise TV
error at most `δ k`, using that stage's own reset word and target horizon. -/
theorem varyingResetSchedule_block_projection_tv_le (ℓ : ℕ → ℕ)
    (r : (k : ℕ) → Fin (ℓ k) → A) (π : ℕ → ValidCausalPolicy A O) (t : ℕ → ℕ)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (δ : ℕ → ℝ)
    (hr : ∀ k θ, IsCausalResetWordAtDepth (Qs θ) (hQ θ) (r k) (t k) (δ k))
    (k : ℕ) (θ : Θ) :
    finiteTV
      (finiteDecisionLaw
        (causalFiniteExperiment (varyingResetSchedulePolicy ℓ r π t) Qs
          ((varyingResetClock ℓ t k + ℓ k) + t k))
        (finiteMapRule (causalBlockProjection (varyingResetClock ℓ t k + ℓ k) (t k))) θ)
      (causalFiniteExperiment (π k).1 Qs (t k) θ) ≤ δ k := by
  rw [varyingResetSchedule_experiment_eq]
  exact approximateResetWord_block_projection_tv_le _ _ _
    (varyingResetPrefixPolicy ℓ r π t k).2 (r k) (π k).1 (π k).2 Qs hQ (δ k) (hr k) θ

/-- Finite-budget directed deficiency of each scheduled experiment is
bounded by the corresponding native reset error. -/
theorem varyingResetSchedule_block_deficiency_le (ℓ : ℕ → ℕ)
    (r : (k : ℕ) → Fin (ℓ k) → A) (π : ℕ → ValidCausalPolicy A O) (t : ℕ → ℕ)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (δ : ℕ → ℝ)
    (hr : ∀ k θ, IsCausalResetWordAtDepth (Qs θ) (hQ θ) (r k) (t k) (δ k)) (k : ℕ) :
    finiteDeficiency
      (causalFiniteExperiment (varyingResetSchedulePolicy ℓ r π t) Qs
        (varyingResetClock ℓ t (k + 1)))
      (causalFiniteExperiment (π k).1 Qs (t k)) ≤ δ k := by
  rw [varyingResetClock_succ, varyingResetSchedule_experiment_eq]
  exact approximateResetWord_block_deficiency_le _ _ _
    (varyingResetPrefixPolicy ℓ r π t k).2 (r k) (π k).1 (π k).2 Qs hQ (δ k) (hr k)

/-- The written coordinate inequality, with actual causal worlds and
actual one-run acquisition: reset error plus the member's test deficiency. -/
theorem varyingResetSchedule_profileValue_le (ℓ : ℕ → ℕ)
    (r : (k : ℕ) → Fin (ℓ k) → A) (π : ℕ → ValidCausalPolicy A O) (t : ℕ → ℕ)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (δ : ℕ → ℝ)
    (hr : ∀ k θ, IsCausalResetWordAtDepth (Qs θ) (hQ θ) (r k) (t k) (δ k))
    (e : ℕ ≃ CausalNativeTest A O) (j k : ℕ) :
    causalPolicyProfileValue
      ⟨varyingResetSchedulePolicy ℓ r π t, varyingResetSchedulePolicy_valid ℓ r π t⟩ Qs e j ≤
      δ k + causalPolicyTestDeficiency (π k) Qs (e j) (t k) := by
  let πs : ValidCausalPolicy A O :=
    ⟨varyingResetSchedulePolicy ℓ r π t, varyingResetSchedulePolicy_valid ℓ r π t⟩
  calc
    causalPolicyProfileValue πs Qs e j ≤
        causalPolicyTestDeficiency πs Qs (e j) (varyingResetClock ℓ t (k + 1)) :=
      causalPolicyProfileValue_le_testDeficiency Qs hQ e πs j _
    _ ≤ finiteDeficiency
        (causalFiniteExperiment πs.1 Qs (varyingResetClock ℓ t (k + 1)))
        (causalFiniteExperiment (π k).1 Qs (t k)) +
          causalPolicyTestDeficiency (π k) Qs (e j) (t k) :=
      finiteDeficiency_triangle _ _ _
        (causalFiniteExperiment_valid πs.1 πs.2 Qs hQ _)
        (causalFiniteExperiment_valid (π k).1 (π k).2 Qs hQ (t k))
        (causalNativeTestExperiment_valid Qs hQ (e j))
    _ ≤ δ k + causalPolicyTestDeficiency (π k) Qs (e j) (t k) := by
      have hbound := varyingResetSchedule_block_deficiency_le ℓ r π t Qs hQ δ hr k
      dsimp only [πs]
      linarith

/-- **Collapse under asymptotically exact resets.** The actual spliced
policy attains the Pareto limit whenever reset errors vanish and the
scheduled finite-member deficiencies converge coordinatewise to that limit. -/
theorem varyingResetSchedule_profile_eq_of_pareto (ℓ : ℕ → ℕ)
    (r : (k : ℕ) → Fin (ℓ k) → A) (π : ℕ → ValidCausalPolicy A O) (t : ℕ → ℕ)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hr : ∀ k θ, IsCausalResetWordAtDepth (Qs θ) (hQ θ) (r k) (t k) (δ k))
    (e : ℕ ≃ CausalNativeTest A O) (p : ProfileCube)
    (hp : p ∈ causalParetoFrontier Qs hQ e)
    (hlim : ∀ j, Tendsto
      (fun k => causalPolicyTestDeficiency (π k) Qs (e j) (t k)) atTop (𝓝 (p j : ℝ))) :
    causalPolicyProfile Qs hQ e
      ⟨varyingResetSchedulePolicy ℓ r π t, varyingResetSchedulePolicy_valid ℓ r π t⟩ = p := by
  let πs : ValidCausalPolicy A O :=
    ⟨varyingResetSchedulePolicy ℓ r π t, varyingResetSchedulePolicy_valid ℓ r π t⟩
  change causalPolicyProfile Qs hQ e πs = p
  apply eq_of_le_of_pareto hp.2 (subset_closure ⟨πs, rfl⟩)
  intro j
  apply Subtype.coe_le_coe.mp
  change causalPolicyProfileValue πs Qs e j ≤ (p j : ℝ)
  have ht : Tendsto
      (fun k => δ k + causalPolicyTestDeficiency (π k) Qs (e j) (t k))
      atTop (𝓝 (p j : ℝ)) := by simpa using hδ.add (hlim j)
  exact ge_of_tendsto ht (Eventually.of_forall fun k =>
    varyingResetSchedule_profileValue_le ℓ r π t Qs hQ δ hr e j k)

end
end IdExp
