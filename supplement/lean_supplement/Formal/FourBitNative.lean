import Formal.FourBitPosteriorControls
import Formal.CausalObjectiveOrder

/-! Attained global optima, the literal native FULL target, and a sufficient
comparator in the same unrestricted causal-policy family. -/
noncomputable section
namespace IdExp.FourBitPosterior
open Finset ScheduledReveal PosteriorMovement

def fixedPolicy (b : Bool) : Policy := ⟨detPolicy (fun _ => b), isCausalPolicy_detPolicy _⟩
@[simp] theorem fixed_probability (b : Bool) : fullProbability (fixedPolicy b) = if b then 1 else 0 := by
  cases b <;> simp [fullProbability, fixedPolicy, detPolicy]

theorem movement_maximizer_iff (kind : Kind) (γ : ℝ) (hγ : (9/10:ℝ) ≤ γ) (π : Policy) :
    (∀ ρ : Policy, objective kind γ ρ ≤ objective kind γ π) ↔ fullProbability π=0 := by
  have hw : objective kind γ (fixedPolicy false)=fairReward kind*(1+γ+γ^2) := by
    simp [objective_eq]
  constructor
  · intro h
    apply (objective_eq_max_iff kind γ hγ π).mp
    exact le_antisymm (objective_le kind γ hγ π) (hw ▸ h (fixedPolicy false))
  · intro hs ρ
    rw [(objective_eq_max_iff kind γ hγ π).mpr hs]
    exact objective_le kind γ hγ ρ

theorem control_maximizer_iff (kind : ControlKind) (γ : ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (π : Policy) :
    (∀ ρ : Policy, controlObjective kind γ ρ ≤ controlObjective kind γ π) ↔ fullProbability π=1 := by
  have hw : controlObjective kind γ (fixedPolicy true)=fullControl kind := by
    simp [controlObjective_eq]
  have hb (ρ : Policy) : controlObjective kind γ ρ ≤ fullControl kind := by
    rw [controlObjective_eq]
    have hg := control_gap kind γ hγ hγ1
    have hs := (probability_bounds ρ).2
    nlinarith
  constructor
  · intro h
    apply (control_eq_max_iff kind γ hγ hγ1 π).mp
    exact le_antisymm (hb π) (hw ▸ h (fixedPolicy true))
  · intro hs ρ
    rw [(control_eq_max_iff kind γ hγ hγ1 π).mpr hs]
    exact hb ρ

def fullTarget := record (fixedPolicy true) 1

theorem fullTarget_from_world : FiniteBlackwellLE fullTarget (diracExp (id : World → World)) := by
  refine ⟨fullTarget, fun θ _ => record_valid (fixedPolicy true) 1 θ, ?_⟩
  funext θ h
  simp [finiteDecisionLaw_diracExp, id_eq]

def extractWorld (h : CausalFiniteTrace Action Observation 1) (θ : World) : ℝ :=
  if θ=(h 0).2 then 1 else 0

theorem world_from_fullTarget : FiniteBlackwellLE (diracExp (id : World → World)) fullTarget := by
  refine ⟨extractWorld, ?_, ?_⟩
  · intro h _; constructor
    · intro θ; unfold extractWorld; split <;> norm_num
    · simp [extractWorld]
  · funext θ η
    have he := ScheduledReveal.firstExpectation signal (fixedPolicy true).1 (fixedPolicy true).2 θ 0
      (fun ao => if η=ao.2 then (1:ℝ) else 0)
    change (∑ h, record (fixedPolicy true) 1 θ h * (if η=(h 0).2 then 1 else 0)) = _
    rw [he, Fintype.sum_prod_type]
    simp [fixedPolicy, detPolicy, ScheduledReveal.response, mode, signal, diracExp, id_eq, mul_ite, eq_comm]

theorem native_deficiency_exact (π : Policy) (n : ℕ) (hn : 3 ≤ n+1) :
    finiteDeficiency (record π (n+1)) fullTarget = (1-fullProbability π)/2 := by
  unfold fullTarget
  rw [finiteDeficiency_eq_of_target_blackwellEquiv _ _ (diracExp (id : World → World))
    (record_valid π _) (record_valid (fixedPolicy true) 1) (diracExp_valid _)
    fullTarget_from_world world_from_fullTarget]
  exact deficiency_exact π n hn

theorem eventual_native_deficiency (π : Policy) :
    sInf (Set.range (fun t => finiteDeficiency (record π t) fullTarget)) =
      (1-fullProbability π)/2 := by
  let f := fun t => finiteDeficiency (record π t) fullTarget
  have ha : Antitone f := by
    intro m n hmn
    exact finiteDeficiency_mono_source_of_finiteBlackwellLE _ _ _
      (causalFiniteExperiment_prefix_blackwell_of_le π.1 π.2 response
        (ScheduledReveal.response_valid signal) hmn)
  have hl (t : ℕ) : (1-fullProbability π)/2 ≤ f t := by
    have h := ha (show t ≤ (t+2)+1 by omega)
    rw [show f ((t+2)+1)=(1-fullProbability π)/2 from native_deficiency_exact π (t+2) (by omega)] at h
    exact h
  change sInf (Set.range f) = _
  apply le_antisymm
  · rw [← native_deficiency_exact π 2 (by omega)]
    exact csInf_le ⟨(1-fullProbability π)/2, by rintro _ ⟨t,rfl⟩; exact hl t⟩ ⟨3,rfl⟩
  · exact le_csInf (Set.range_nonempty _) (by rintro _ ⟨t,rfl⟩; exact hl t)

theorem fullPolicy_sufficient : CausalNativelySufficient response (fixedPolicy true) := by
  intro n ε hε
  refine ⟨3, ?_⟩
  intro t ht τ
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show t≠0 by omega)
  have hdom : FiniteBlackwellLE (causalPlanObservationExperiment n τ response)
      (diracExp (id : World → World)) := by
    refine ⟨causalPlanObservationExperiment n τ response,
      fun θ _ => causalPlanObservationExperiment_valid n τ response (ScheduledReveal.response_valid signal) θ, ?_⟩
    funext θ o; simp [finiteDecisionLaw_diracExp]
  have h := finiteDeficiency_mono_target_of_finiteBlackwellLE
    (record (fixedPolicy true) (k+1)) _ (diracExp (id : World → World))
    (record_valid (fixedPolicy true) _) (diracExp_valid _) hdom
  rw [deficiency_exact (fixedPolicy true) k ht, fixed_probability] at h
  norm_num at h
  exact h.trans_lt hε

/-- The asserted failure is to the actual native one-step FULL intervention. -/
theorem movement_optimum_native_failure (kind : Kind) (γ : ℝ) (hγ : (9/10:ℝ)≤γ)
    (π : Policy) (hopt : ∀ ρ : Policy, objective kind γ ρ ≤ objective kind γ π)
    (n : ℕ) (hn : 3 ≤ n+1) : finiteDeficiency (record π (n+1)) fullTarget=1/2 := by
  rw [native_deficiency_exact π n hn, (movement_maximizer_iff kind γ hγ π).mp hopt]
  norm_num

end IdExp.FourBitPosterior
