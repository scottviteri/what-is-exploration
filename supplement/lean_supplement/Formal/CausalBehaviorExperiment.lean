import Formal.CausalBehavior
import Formal.CausalConsistentFamily

/-!
# Experiments induced directly by controlled-prefix behaviors

`CausalBehavior` is the semantic world object.  This file connects it to the
other three layers that the paper must keep distinct:

1. a finite truncation used by coherent decoders;
2. the observation law of a deterministic native plan;
3. the path law induced after a randomized policy supplies action
   propensities; and
4. the resulting finite statistical experiment over a class of worlds.

All definitions are stated directly in terms of controlled-prefix masses.
The comparison theorems show that they agree exactly with the older
response-kernel presentation.
-/

namespace IdExp

open Finset

set_option linter.unusedSectionVars false

variable {A O Θ J : Type*} [Fintype A] [Fintype O] [Fintype J]

namespace CausalBehavior

/-- Restriction of an infinite controlled-prefix behavior to the finite
consistency interface used by coherent depth-`n` decoders.  The underlying
mass function need not be truncated: `ConsistentFamily` only asks for the
equations below depth `n`. -/
def truncate (p : CausalBehavior A O) (n : ℕ) : ConsistentFamily A O n where
  p := p.mass
  root := p.root
  nonneg := p.nonneg
  consistent := fun h a _ => p.consistent h a

@[simp]
theorem truncate_p (p : CausalBehavior A O) (n : ℕ)
    (h : CausalHistory A O) :
    (p.truncate n).p h = p.mass h :=
  rfl

/-- The old finite family obtained from a raw response is exactly the
truncation of its canonical behavior. -/
theorem truncate_ofResponse (Q : CausalResponse A O)
    (hQ : IsCausalResponse Q) (n : ℕ) :
    (CausalBehavior.ofResponse Q hQ).truncate n =
      ConsistentFamily.ofResponse Q hQ n := by
  rfl

/-- Finite convex mixtures are pointwise mixtures of controlled-prefix
behaviors.  This is the canonical representation of a latent world chosen
once per episode; it is not pointwise mixing of conditional response rows. -/
noncomputable def mix (c : J → ℝ) (hc : IsDist c)
    (p : J → CausalBehavior A O) : CausalBehavior A O where
  mass := fun h => ∑ j, c j * (p j).mass h
  root := by simp [(p _).root, hc.2]
  nonneg := fun h =>
    Finset.sum_nonneg fun j _ => mul_nonneg (hc.1 j) ((p j).nonneg h)
  consistent := by
    intro h a
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.mul_sum, (p j).consistent h a]

@[simp]
theorem mix_mass (c : J → ℝ) (hc : IsDist c)
    (p : J → CausalBehavior A O) (h : CausalHistory A O) :
    (CausalBehavior.mix c hc p).mass h = ∑ j, c j * (p j).mass h :=
  rfl

theorem truncate_mix (c : J → ℝ) (hc : IsDist c)
    (p : J → CausalBehavior A O) (n : ℕ) :
    (CausalBehavior.mix c hc p).truncate n =
      ConsistentFamily.mix c hc (fun j => (p j).truncate n) := by
  rfl

end CausalBehavior

/-! ## Deterministic native plans -/

/-- The depth-`n` observation law of a deterministic adaptive native plan,
evaluated directly from a controlled-prefix behavior. -/
noncomputable def causalBehaviorPlanLaw (n : ℕ) (τ : CausalPlan A O n)
    (p : CausalBehavior A O) : CausalObservationTrace O n → ℝ :=
  familyPlanLaw n τ (p.truncate n)

@[simp]
theorem causalBehaviorPlanLaw_apply (n : ℕ) (τ : CausalPlan A O n)
    (p : CausalBehavior A O) (w : CausalObservationTrace O n) :
    causalBehaviorPlanLaw n τ p w =
      p.mass (List.ofFn (causalTraceOfObservations τ w)) :=
  rfl

theorem causalBehaviorPlanLaw_isDist (n : ℕ) (τ : CausalPlan A O n)
    (p : CausalBehavior A O) : IsDist (causalBehaviorPlanLaw n τ p) :=
  familyPlanLaw_isDist n τ (p.truncate n)

/-- A class of behaviors induces a finite native observation experiment. -/
noncomputable def causalBehaviorPlanExperiment (n : ℕ) (τ : CausalPlan A O n)
    (ps : Θ → CausalBehavior A O) :
    FiniteExperiment Θ (CausalObservationTrace O n) :=
  fun θ => causalBehaviorPlanLaw n τ (ps θ)

theorem causalBehaviorPlanExperiment_valid (n : ℕ) (τ : CausalPlan A O n)
    (ps : Θ → CausalBehavior A O) :
    IsFiniteExperiment (causalBehaviorPlanExperiment n τ ps) :=
  fun θ => causalBehaviorPlanLaw_isDist n τ (ps θ)

/-- The direct native experiment agrees with the response-kernel experiment
for any chosen presentation. -/
theorem causalBehaviorPlanExperiment_ofResponse [Nonempty A]
    (n : ℕ) (τ : CausalPlan A O n) (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) :
    causalBehaviorPlanExperiment n τ
        (fun θ => CausalBehavior.ofResponse (Qs θ) (hQ θ)) =
      causalPlanObservationExperiment n τ Qs := by
  funext θ w
  rw [causalPlanObservationExperiment_eq_responseProb]
  rfl

/-- Native plan evaluation is affine in latent mixtures of behaviors. -/
theorem causalBehaviorPlanLaw_mix (c : J → ℝ) (hc : IsDist c)
    (p : J → CausalBehavior A O) (n : ℕ) (τ : CausalPlan A O n)
    (w : CausalObservationTrace O n) :
    causalBehaviorPlanLaw n τ (CausalBehavior.mix c hc p) w =
      ∑ j, c j * causalBehaviorPlanLaw n τ (p j) w :=
  rfl

/-! ## Randomized policies and acquired experiments -/

/-- A policy supplies the missing action propensities.  Multiplying those by
the controlled-prefix mass produces the probability of a concrete history
under that policy. -/
noncomputable def causalBehaviorTraceProb (π : CausalPolicy A O)
    (p : CausalBehavior A O) (h : CausalHistory A O) : ℝ :=
  causalPolicyProb π h * p.mass h

/-- The direct policy path-law formula is exactly the existing raw-kernel
trace probability for every presentation of the behavior. -/
theorem causalTraceProb_eq_behaviorTraceProb (π : CausalPolicy A O)
    (Q : CausalResponse A O) (hQ : IsCausalResponse Q)
    (h : CausalHistory A O) :
    causalTraceProb π Q h =
      causalBehaviorTraceProb π (CausalBehavior.ofResponse Q hQ) h := by
  rw [causalTraceProb_factor]
  rfl

/-- The exact-horizon statistical experiment induced by a policy, defined
without choosing conditional rows at null histories. -/
noncomputable def causalBehaviorFiniteExperiment (π : CausalPolicy A O)
    (ps : Θ → CausalBehavior A O) (n : ℕ) :
    FiniteExperiment Θ (CausalFiniteTrace A O n) :=
  fun θ w => causalBehaviorTraceProb π (ps θ) (List.ofFn w)

/-- Direct acquired experiments agree exactly with raw-kernel acquired
experiments for every family of presentations. -/
theorem causalBehaviorFiniteExperiment_ofResponse
    (π : CausalPolicy A O) (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (n : ℕ) :
    causalBehaviorFiniteExperiment π
        (fun θ => CausalBehavior.ofResponse (Qs θ) (hQ θ)) n =
      causalFiniteExperiment π Qs n := by
  funext θ w
  symm
  exact causalTraceProb_eq_behaviorTraceProb π (Qs θ) (hQ θ) (List.ofFn w)

/-- Direct acquired experiments are probability kernels whenever the policy
is valid.  The proof transports validity through an arbitrary raw
presentation; the experiment itself contains no such choice. -/
theorem causalBehaviorFiniteExperiment_valid [Nonempty O]
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (ps : Θ → CausalBehavior A O) (n : ℕ) :
    IsFiniteExperiment (causalBehaviorFiniteExperiment π ps n) := by
  let Qs : Θ → CausalResponse A O := fun θ => (ps θ).toResponse
  have hQ : ∀ θ, IsCausalResponse (Qs θ) := fun θ => (ps θ).toResponse_valid
  have hps :
      (fun θ => CausalBehavior.ofResponse (Qs θ) (hQ θ)) = ps := by
    funext θ
    exact CausalBehavior.ofResponse_toResponse (ps θ)
  rw [← hps, causalBehaviorFiniteExperiment_ofResponse π Qs hQ n]
  exact causalFiniteExperiment_valid π hπ Qs hQ n

/-- Direct behavior experiments have the same exact one-step prefix
marginalization as their raw response presentations. -/
theorem causalBehaviorFiniteExperiment_prefix [Nonempty O]
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (ps : Θ → CausalBehavior A O) (n : ℕ) :
    finiteDecisionLaw (causalBehaviorFiniteExperiment π ps (n + 1))
        (causalPrefixRule n) =
      causalBehaviorFiniteExperiment π ps n := by
  let Qs : Θ → CausalResponse A O := fun θ => (ps θ).toResponse
  have hQ : ∀ θ, IsCausalResponse (Qs θ) := fun θ => (ps θ).toResponse_valid
  have hps :
      (fun θ => CausalBehavior.ofResponse (Qs θ) (hQ θ)) = ps := by
    funext θ
    exact CausalBehavior.ofResponse_toResponse (ps θ)
  rw [← hps,
    causalBehaviorFiniteExperiment_ofResponse,
    causalBehaviorFiniteExperiment_ofResponse]
  exact causalFiniteExperiment_prefix π hπ Qs hQ n

/-- Hence the policy experiments induced directly by behaviors form the same
growing Blackwell chain, without making a null-row presentation part of the
statement. -/
theorem causalBehaviorFiniteExperiment_prefix_blackwell [Nonempty O]
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (ps : Θ → CausalBehavior A O) (n : ℕ) :
    FiniteBlackwellLE (causalBehaviorFiniteExperiment π ps n)
      (causalBehaviorFiniteExperiment π ps (n + 1)) := by
  refine ⟨causalPrefixRule n, causalPrefixRule_mem_stochasticRules n, ?_⟩
  exact causalBehaviorFiniteExperiment_prefix π hπ ps n

/-- Under a deterministic native plan, the direct observation experiment and
the direct full-trace experiment are exactly Blackwell equivalent. -/
theorem causalBehaviorPlan_full_observation_blackwell_equiv
    [Nonempty A] [Nonempty O]
    (n : ℕ) (τ : CausalPlan A O n) (ps : Θ → CausalBehavior A O) :
    FiniteBlackwellLE (causalBehaviorPlanExperiment n τ ps)
        (causalBehaviorFiniteExperiment (causalPolicyOfPlan n τ) ps n) ∧
      FiniteBlackwellLE
        (causalBehaviorFiniteExperiment (causalPolicyOfPlan n τ) ps n)
        (causalBehaviorPlanExperiment n τ ps) := by
  let Qs : Θ → CausalResponse A O := fun θ => (ps θ).toResponse
  have hQ : ∀ θ, IsCausalResponse (Qs θ) := fun θ => (ps θ).toResponse_valid
  have hps :
      (fun θ => CausalBehavior.ofResponse (Qs θ) (hQ θ)) = ps := by
    funext θ
    exact CausalBehavior.ofResponse_toResponse (ps θ)
  rw [← hps,
    causalBehaviorPlanExperiment_ofResponse,
    causalBehaviorFiniteExperiment_ofResponse]
  exact causalPlan_full_observation_blackwell_equiv n τ Qs

/-- Policy-induced experiment evaluation is affine in latent mixtures of
behaviors. -/
theorem causalBehaviorTraceProb_mix (π : CausalPolicy A O)
    (c : J → ℝ) (hc : IsDist c) (p : J → CausalBehavior A O)
    (h : CausalHistory A O) :
    causalBehaviorTraceProb π (CausalBehavior.mix c hc p) h =
      ∑ j, c j * causalBehaviorTraceProb π (p j) h := by
  unfold causalBehaviorTraceProb
  rw [CausalBehavior.mix_mass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end IdExp
