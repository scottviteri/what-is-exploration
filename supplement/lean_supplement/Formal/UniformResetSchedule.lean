import Formal.UniformResetWord
import Formal.ApproachScheme

/-!
# One-run infinite schedules under a uniform reset word

A prefix-compatible sequence of finite splice policies defines one genuine
infinite causal policy. Each scheduled block has its original experiment as
an exact deterministic projection at the cumulative, unpadded time budget.
Zero-length resets and zero-length target blocks are allowed. Enumerating
the native tests then gives native sufficiency after an explicit finite
budget at every fixed depth, for arbitrary nonempty world classes.
-/

namespace IdExp

open Finset Set Filter Topology
open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

/-- End of the first `k` reset/target blocks, without padding or idle steps. -/
def uniformResetClock (ℓ : ℕ) (t : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, (ℓ + t i)

@[simp] theorem uniformResetClock_zero (ℓ : ℕ) (t : ℕ → ℕ) :
    uniformResetClock ℓ t 0 = 0 := by simp [uniformResetClock]

theorem uniformResetClock_succ (ℓ : ℕ) (t : ℕ → ℕ) (k : ℕ) :
    uniformResetClock ℓ t (k + 1) = (uniformResetClock ℓ t k + ℓ) + t k := by
  simp [uniformResetClock, Finset.sum_range_succ, Nat.add_assoc]

theorem uniformResetClock_monotone (ℓ : ℕ) (t : ℕ → ℕ) :
    Monotone (uniformResetClock ℓ t) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [uniformResetClock_succ]
  omega

variable {A O Θ : Type*} [Fintype A] [Fintype O] [Nonempty A] [Nonempty O] [Nonempty Θ]

/-- Finite-stage policies freeze all rows used by earlier completed blocks. -/
def uniformResetApproxPolicy {ℓ : ℕ} (r : Fin ℓ → A)
    (π : ℕ → ValidCausalPolicy A O) (t : ℕ → ℕ) : ℕ → ValidCausalPolicy A O
  | 0 => defaultValidCausalPolicy
  | k + 1 =>
      ⟨causalResetSplicePolicy (uniformResetClock ℓ t k)
        (uniformResetApproxPolicy r π t k).1 r (π k).1,
        causalResetSplicePolicy_valid _ _ (uniformResetApproxPolicy r π t k).2
          r (π k).1 (π k).2⟩

theorem uniformResetApproxPolicy_step_agrees {ℓ : ℕ} (r : Fin ℓ → A)
    (π : ℕ → ValidCausalPolicy A O) (t : ℕ → ℕ) (k : ℕ)
    (h : CausalHistory A O) (hh : h.length < uniformResetClock ℓ t k) :
    (uniformResetApproxPolicy r π t (k + 1)).1 h =
      (uniformResetApproxPolicy r π t k).1 h := by
  have hlt : h.length < uniformResetClock ℓ t k + ℓ := by omega
  simp [uniformResetApproxPolicy, causalResetSplicePolicy, causalSplicePolicy,
    causalResetPrefixPolicy, hlt, hh]

theorem uniformResetApproxPolicy_agrees {ℓ : ℕ} (r : Fin ℓ → A)
    (π : ℕ → ValidCausalPolicy A O) (t : ℕ → ℕ)
    {i j : ℕ} (hij : i ≤ j) (h : CausalHistory A O)
    (hh : h.length < uniformResetClock ℓ t i) :
    (uniformResetApproxPolicy r π t j).1 h =
      (uniformResetApproxPolicy r π t i).1 h := by
  induction j with
  | zero => have hi : i = 0 := by omega
            subst i
            rfl
  | succ j ih =>
      by_cases hle : i ≤ j
      · rw [uniformResetApproxPolicy_step_agrees r π t j h
          (hh.trans_le (uniformResetClock_monotone ℓ t hle)), ih hle]
      · have heq : i = j + 1 := by omega
        subst i
        rfl

/-- The actual infinite one-run policy. At a history lying within some
completed stage, use the first such finite-stage policy. If all scheduled
blocks have already exhausted a bounded total duration, continue with the
fixed default policy. This also handles schedules made entirely of empty
blocks, without a hidden positive-duration hypothesis. -/
def uniformResetSchedulePolicy {ℓ : ℕ} (r : Fin ℓ → A)
    (π : ℕ → ValidCausalPolicy A O) (t : ℕ → ℕ) : CausalPolicy A O :=
  fun h => if hk : ∃ k, h.length < uniformResetClock ℓ t k then
    (uniformResetApproxPolicy r π t (Nat.find hk)).1 h
  else defaultValidCausalPolicy.1 h

theorem uniformResetSchedulePolicy_valid {ℓ : ℕ} (r : Fin ℓ → A)
    (π : ℕ → ValidCausalPolicy A O) (t : ℕ → ℕ) :
    IsCausalPolicy (uniformResetSchedulePolicy r π t) := by
  intro h
  simp only [uniformResetSchedulePolicy]
  split_ifs with hk
  · exact (uniformResetApproxPolicy r π t (Nat.find hk)).2 h
  · exact defaultValidCausalPolicy.2 h

theorem uniformResetSchedulePolicy_agrees {ℓ : ℕ} (r : Fin ℓ → A)
    (π : ℕ → ValidCausalPolicy A O) (t : ℕ → ℕ) (k : ℕ)
    (h : CausalHistory A O) (hh : h.length < uniformResetClock ℓ t k) :
    uniformResetSchedulePolicy r π t h =
      (uniformResetApproxPolicy r π t k).1 h := by
  have hex : ∃ j, h.length < uniformResetClock ℓ t j := ⟨k, hh⟩
  rw [uniformResetSchedulePolicy, dif_pos hex]
  have hj := Nat.find_spec hex
  rcases le_total (Nat.find hex) k with hjk | hkj
  · exact (uniformResetApproxPolicy_agrees r π t hjk h hj).symm
  · exact uniformResetApproxPolicy_agrees r π t hkj h hh

/-- Its actual completed-prefix experiment is exactly the finite splice
experiment, derived from equality of all policy rows used by the trace law. -/
theorem uniformResetSchedule_experiment_eq {ℓ : ℕ} (r : Fin ℓ → A)
    (π : ℕ → ValidCausalPolicy A O) (t : ℕ → ℕ)
    (Qs : Θ → CausalResponse A O) (k : ℕ) :
    causalFiniteExperiment (uniformResetSchedulePolicy r π t) Qs
      (uniformResetClock ℓ t k) =
    causalFiniteExperiment (uniformResetApproxPolicy r π t k).1 Qs
      (uniformResetClock ℓ t k) :=
  causalFiniteExperiment_congr_of_agree _ _ Qs _
    (uniformResetSchedulePolicy_agrees r π t k)

/-- Exact projection of the `k`-th block of the single infinite run. The
acquisition budget is precisely the sum of the reset and target lengths. -/
theorem uniformResetSchedule_block_projection_exact {ℓ : ℕ} (r : Fin ℓ → A)
    (π : ℕ → ValidCausalPolicy A O) (t : ℕ → ℕ)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hr : ∀ θ, IsUniformCausalResetWord (Qs θ) r) (k : ℕ) :
    finiteDecisionLaw
      (causalFiniteExperiment (uniformResetSchedulePolicy r π t) Qs
        ((uniformResetClock ℓ t k + ℓ) + t k))
      (finiteMapRule (causalBlockProjection (uniformResetClock ℓ t k + ℓ) (t k))) =
      causalFiniteExperiment (π k).1 Qs (t k) := by
  have heq := uniformResetSchedule_experiment_eq r π t Qs (k + 1)
  rw [uniformResetClock_succ] at heq
  rw [heq]
  exact uniformResetWord_block_projection_exact _ _ _
    (uniformResetApproxPolicy r π t k).2 r (π k).1 (π k).2 Qs hQ hr

/-- Every scheduled experiment is exactly available at its completion time. -/
theorem uniformResetSchedule_block_blackwell {ℓ : ℕ} (r : Fin ℓ → A)
    (π : ℕ → ValidCausalPolicy A O) (t : ℕ → ℕ)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hr : ∀ θ, IsUniformCausalResetWord (Qs θ) r) (k : ℕ) :
    FiniteBlackwellLE (causalFiniteExperiment (π k).1 Qs (t k))
      (causalFiniteExperiment (uniformResetSchedulePolicy r π t) Qs
        (uniformResetClock ℓ t (k + 1))) := by
  rw [uniformResetClock_succ]
  exact ⟨finiteMapRule (causalBlockProjection (uniformResetClock ℓ t k + ℓ) (t k)),
    finiteMapRule_mem _, uniformResetSchedule_block_projection_exact r π t Qs hQ hr k⟩

theorem uniformResetSchedule_block_blackwell_of_le {ℓ : ℕ} (r : Fin ℓ → A)
    (π : ℕ → ValidCausalPolicy A O) (t : ℕ → ℕ)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hr : ∀ θ, IsUniformCausalResetWord (Qs θ) r) (k s : ℕ)
    (hs : uniformResetClock ℓ t (k + 1) ≤ s) :
    FiniteBlackwellLE (causalFiniteExperiment (π k).1 Qs (t k))
      (causalFiniteExperiment (uniformResetSchedulePolicy r π t) Qs s) :=
  finiteBlackwellLE_trans (uniformResetSchedule_block_blackwell r π t Qs hQ hr k)
    (causalFiniteExperiment_prefix_blackwell_of_le _
      (uniformResetSchedulePolicy_valid r π t) Qs hQ hs)

theorem uniformResetSchedule_block_deficiency_zero
    {ℓ : ℕ} (r : Fin ℓ → A) (π : ℕ → ValidCausalPolicy A O) (t : ℕ → ℕ)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hr : ∀ θ, IsUniformCausalResetWord (Qs θ) r) (k s : ℕ)
    (hs : uniformResetClock ℓ t (k + 1) ≤ s) :
    finiteDeficiency (causalFiniteExperiment (uniformResetSchedulePolicy r π t) Qs s)
      (causalFiniteExperiment (π k).1 Qs (t k)) = 0 :=
  finiteDeficiency_eq_zero_of_blackwellLE _ _
    (causalFiniteExperiment_valid _ (uniformResetSchedulePolicy_valid r π t) Qs hQ s)
    (causalFiniteExperiment_valid (π k).1 (π k).2 Qs hQ (t k))
    (uniformResetSchedule_block_blackwell_of_le r π t Qs hQ hr k s hs)

/-- The complete exact reset-word collapse theorem: convergence of the
scheduled finite experiments to a Pareto point is realized by the actual
one-run splice, not by an assumed sequential dominator. -/
theorem uniformResetSchedule_profile_eq_of_pareto
    {ℓ : ℕ} (r : Fin ℓ → A) (π : ℕ → ValidCausalPolicy A O) (t : ℕ → ℕ)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hr : ∀ θ, IsUniformCausalResetWord (Qs θ) r)
    (e : ℕ ≃ CausalNativeTest A O) (p : ProfileCube)
    (hp : p ∈ causalParetoFrontier Qs hQ e)
    (hlim : ∀ j, Tendsto
      (fun k => causalPolicyTestDeficiency (π k) Qs (e j) (t k)) atTop (𝓝 (p j : ℝ))) :
    causalPolicyProfile Qs hQ e
      ⟨uniformResetSchedulePolicy r π t, uniformResetSchedulePolicy_valid r π t⟩ = p := by
  let πs : ValidCausalPolicy A O :=
    ⟨uniformResetSchedulePolicy r π t, uniformResetSchedulePolicy_valid r π t⟩
  change causalPolicyProfile Qs hQ e πs = p
  apply causalPolicyProfile_eq_of_dominates_of_pareto Qs hQ e πs π
    (fun k => uniformResetClock ℓ t (k + 1)) t ?_ p hp hlim
  intro k
  change finiteDeficiency
    (causalFiniteExperiment (uniformResetSchedulePolicy r π t) Qs
      (uniformResetClock ℓ t (k + 1))) (causalFiniteExperiment (π k).1 Qs (t k)) = 0
  exact uniformResetSchedule_block_deficiency_zero r π t Qs hQ hr k _ le_rfl

/-! ## Cycling through all native tests -/

/-- Target policy of the `k`-th native test in a fixed enumeration. -/
def uniformResetNativePolicies (e : ℕ ≃ CausalNativeTest A O) (k : ℕ) :
    ValidCausalPolicy A O :=
  ⟨causalPolicyOfPlan (e k).1 (e k).2, isCausalPolicy_causalPolicyOfPlan (e k).1 (e k).2⟩

/-- One policy executes each native test after its own reset. -/
def uniformResetNativePolicy {ℓ : ℕ} (r : Fin ℓ → A)
    (e : ℕ ≃ CausalNativeTest A O) : CausalPolicy A O :=
  uniformResetSchedulePolicy r (uniformResetNativePolicies e) (fun k => (e k).1)

theorem uniformResetNativePolicy_valid {ℓ : ℕ} (r : Fin ℓ → A)
    (e : ℕ ≃ CausalNativeTest A O) : IsCausalPolicy (uniformResetNativePolicy r e) :=
  uniformResetSchedulePolicy_valid r _ _

/-- Number of scheduled blocks needed to have executed every depth-`n`
native plan at least once. This is a finite maximum, not an asymptotic or
world-dependent selection. -/
def uniformResetNativeStage (e : ℕ ≃ CausalNativeTest A O) (n : ℕ) : ℕ :=
  Finset.univ.sup (fun τ : CausalPlan A O n => e.symm ⟨n, τ⟩ + 1)

/-- Explicit finite acquisition budget for the depth-at-most-`n` audit:
sum the reset and target lengths through the largest index of a depth-`n`
plan. Prefix marginalization simultaneously covers every shorter test. -/
def uniformResetNativeBudget (ℓ : ℕ) (e : ℕ ≃ CausalNativeTest A O) (n : ℕ) : ℕ :=
  uniformResetClock ℓ (fun k => (e k).1) (uniformResetNativeStage e n)

theorem uniformResetNative_index_le_stage (e : ℕ ≃ CausalNativeTest A O)
    (n : ℕ) (τ : CausalPlan A O n) :
    e.symm ⟨n, τ⟩ + 1 ≤ uniformResetNativeStage e n :=
  Finset.le_sup (f := fun σ : CausalPlan A O n => e.symm ⟨n, σ⟩ + 1)
    (Finset.mem_univ τ)

/-- A decoder for every target at every time beyond its explicit native
budget: project the target's own block and then discard its recorded actions. -/
theorem uniformResetNative_plan_blackwell {ℓ : ℕ} (r : Fin ℓ → A)
    (e : ℕ ≃ CausalNativeTest A O)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hr : ∀ θ, IsUniformCausalResetWord (Qs θ) r)
    {n s : ℕ} (hs : uniformResetNativeBudget ℓ e n ≤ s) (τ : CausalPlan A O n) :
    FiniteBlackwellLE (causalPlanObservationExperiment n τ Qs)
      (causalFiniteExperiment (uniformResetNativePolicy r e) Qs s) := by
  have htime : uniformResetClock ℓ (fun k => (e k).1) (e.symm ⟨n, τ⟩ + 1) ≤ s :=
    (uniformResetClock_monotone ℓ (fun k => (e k).1)
      (uniformResetNative_index_le_stage e n τ)).trans hs
  have hb := uniformResetSchedule_block_blackwell_of_le r
    (uniformResetNativePolicies e) (fun k => (e k).1) Qs hQ hr (e.symm ⟨n, τ⟩) s htime
  have hb' : FiniteBlackwellLE (causalFiniteExperiment (causalPolicyOfPlan n τ) Qs n)
      (causalFiniteExperiment (uniformResetNativePolicy r e) Qs s) := by
    change FiniteBlackwellLE
      (causalFiniteExperiment
        (causalPolicyOfPlan (e (e.symm ⟨n, τ⟩)).1 (e (e.symm ⟨n, τ⟩)).2)
        Qs (e (e.symm ⟨n, τ⟩)).1)
      (causalFiniteExperiment (uniformResetNativePolicy r e) Qs s) at hb
    exact Eq.mp (congrArg
      (fun q : CausalNativeTest A O => FiniteBlackwellLE
        (causalFiniteExperiment (causalPolicyOfPlan q.1 q.2) Qs q.1)
        (causalFiniteExperiment (uniformResetNativePolicy r e) Qs s))
      (e.apply_symm_apply ⟨n, τ⟩)) hb
  exact finiteBlackwellLE_trans (causalPlan_full_observation_blackwell_equiv n τ Qs).1 hb'

/-- Exact zero directed deficiency on an arbitrary nonempty resettable class. -/
theorem uniformResetNative_plan_deficiency_zero
    {ℓ : ℕ} (r : Fin ℓ → A) (e : ℕ ≃ CausalNativeTest A O)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hr : ∀ θ, IsUniformCausalResetWord (Qs θ) r)
    {n s : ℕ} (hs : uniformResetNativeBudget ℓ e n ≤ s) (τ : CausalPlan A O n) :
    finiteDeficiency (causalFiniteExperiment (uniformResetNativePolicy r e) Qs s)
      (causalPlanObservationExperiment n τ Qs) = 0 :=
  finiteDeficiency_eq_zero_of_blackwellLE _ _
    (causalFiniteExperiment_valid _ (uniformResetNativePolicy_valid r e) Qs hQ s)
    (causalPlanObservationExperiment_valid n τ Qs hQ)
    (uniformResetNative_plan_blackwell r e Qs hQ hr hs τ)

/-- Every test through depth `n` is already exactly simulable at the explicit
finite budget, and the same guarantee persists at all later acquired times. -/
theorem uniformResetNative_nativeDeficiencyUpTo_zero
    {ℓ : ℕ} (r : Fin ℓ → A) (e : ℕ ≃ CausalNativeTest A O)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hr : ∀ θ, IsUniformCausalResetWord (Qs θ) r)
    {n s : ℕ} (hs : uniformResetNativeBudget ℓ e n ≤ s) :
    causalNativeDeficiencyUpTo
      (causalFiniteExperiment (uniformResetNativePolicy r e) Qs s) Qs n = 0 := by
  rw [causalNativeDeficiencyUpTo_eq_terminal _
    (causalFiniteExperiment_valid _ (uniformResetNativePolicy_valid r e) Qs hQ s)
    Qs hQ n]
  unfold causalNativeDeficiency
  apply le_antisymm
  · apply Finset.sup'_le
    intro τ _
    exact le_of_eq (uniformResetNative_plan_deficiency_zero r e Qs hQ hr hs τ)
  · let τ : CausalPlan A O n := Classical.arbitrary _
    have h := Finset.le_sup'
      (fun σ : CausalPlan A O n => finiteDeficiency
        (causalFiniteExperiment (uniformResetNativePolicy r e) Qs s)
        (causalPlanObservationExperiment n σ Qs)) (Finset.mem_univ τ)
    simpa only [uniformResetNative_plan_deficiency_zero r e Qs hQ hr hs] using h

/-- Uniform reset implies native sufficiency of one concrete infinite
policy, without a finite class, repeated-sampling limit, or identification. -/
theorem uniformResetNative_nativelySufficient
    {ℓ : ℕ} (r : Fin ℓ → A) (e : ℕ ≃ CausalNativeTest A O)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hr : ∀ θ, IsUniformCausalResetWord (Qs θ) r) :
    CausalNativelySufficient Qs
      ⟨uniformResetNativePolicy r e, uniformResetNativePolicy_valid r e⟩ := by
  intro n ε hε
  refine ⟨uniformResetNativeBudget ℓ e n, ?_⟩
  intro s hs τ
  rw [uniformResetNative_plan_deficiency_zero r e Qs hQ hr hs τ]
  exact hε

/-- Zero is attained, not merely approached in the closure of profiles. -/
theorem uniformResetNative_zeroProfile_attained
    {ℓ : ℕ} (r : Fin ℓ → A) (e : ℕ ≃ CausalNativeTest A O)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hr : ∀ θ, IsUniformCausalResetWord (Qs θ) r) :
    causalPolicyProfile Qs hQ e
      ⟨uniformResetNativePolicy r e, uniformResetNativePolicy_valid r e⟩ = zeroProfile :=
  (causalPolicyProfile_eq_zeroProfile_iff_nativelySufficient Qs hQ e _).2
    (uniformResetNative_nativelySufficient r e Qs hQ hr)

/-- The completed Pareto frontier of any resettable class is the singleton
zero profile, and the preceding theorem supplies an actual attaining policy. -/
theorem uniformResetNative_paretoFrontier_singleton
    {ℓ : ℕ} (r : Fin ℓ → A) (e : ℕ ≃ CausalNativeTest A O)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hr : ∀ θ, IsUniformCausalResetWord (Qs θ) r) :
    causalParetoFrontier Qs hQ e = {zeroProfile} := by
  apply causalParetoFrontier_eq_singleton_of_zero_mem Qs hQ e
  apply subset_closure
  exact ⟨⟨uniformResetNativePolicy r e, uniformResetNativePolicy_valid r e⟩,
    uniformResetNative_zeroProfile_attained r e Qs hQ hr⟩

end
end IdExp
