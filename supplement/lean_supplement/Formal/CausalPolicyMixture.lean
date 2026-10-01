import Formal.CausalUniversality
import Formal.MixturePurposeValue

/-!
# Mixing collectors and recovering their labels from full histories

A world-independent latent collector can be implemented as a history-dependent
behavioral policy. Its posterior label weights depend only on the collectors'
action likelihoods: the common controlled behavior factor cancels. Consequently
retaining the full action-observation history is Blackwell-equivalent to retaining
both the history and the independently sampled collector label.

The construction allows arbitrary valid causal collectors, zero mixture weights,
null histories, every finite horizon (including zero), and arbitrary world classes.
It does not apply to an observation-only or otherwise compressed record.
-/

namespace IdExp

open Finset Set

noncomputable section

set_option linter.unusedSectionVars false

variable {I A O Θ : Type*} [Fintype I] [Fintype A] [Fintype O]

/-- Action likelihoods of a valid policy are nonnegative on all controlled histories. -/
theorem causalPolicyProb_nonneg (π : CausalPolicy A O) (hπ : IsCausalPolicy π)
    (h : CausalHistory A O) : 0 ≤ causalPolicyProb π h := by
  induction h using List.reverseRecOn with
  | nil => simp [causalPolicyProb, causalPolicyProbFrom]
  | append_singleton h ao ih =>
      rw [causalPolicyProb_append_singleton]
      exact mul_nonneg ih ((hπ h).1 ao.1)

/-- The total action likelihood under an independently sampled collector. -/
def causalPolicyMixtureMass (w : I → ℝ) (π : I → CausalPolicy A O)
    (h : CausalHistory A O) : ℝ := ∑ i, w i * causalPolicyProb (π i) h

/-- The behavioral policy implementing one latent collector for the entire run. -/
def causalPolicyMixture (w : I → ℝ) (π : I → CausalPolicy A O) : CausalPolicy A O :=
  fun h a => if causalPolicyMixtureMass w π h = 0 then (Fintype.card A : ℝ)⁻¹
    else (∑ i, w i * causalPolicyProb (π i) h * π i h a) / causalPolicyMixtureMass w π h

theorem causalPolicyMixtureMass_nonneg (w : I → ℝ) (hw : IsDist w)
    (π : I → CausalPolicy A O) (hπ : ∀ i, IsCausalPolicy (π i)) (h : CausalHistory A O) :
    0 ≤ causalPolicyMixtureMass w π h :=
  sum_nonneg fun i _ => mul_nonneg (hw.1 i) (causalPolicyProb_nonneg _ (hπ i) h)

theorem causalPolicyMixtureMass_append (w : I → ℝ) (π : I → CausalPolicy A O)
    (h : CausalHistory A O) (a : A) (o : O) :
    causalPolicyMixtureMass w π (h ++ [(a, o)]) =
      ∑ i, w i * causalPolicyProb (π i) h * π i h a := by
  simp only [causalPolicyMixtureMass, causalPolicyProb_append_singleton, mul_assoc]

theorem sum_causalPolicyMixtureMass_children (w : I → ℝ) (π : I → CausalPolicy A O)
    (hπ : ∀ i, IsCausalPolicy (π i)) (h : CausalHistory A O) (o : O) :
    ∑ a, causalPolicyMixtureMass w π (h ++ [(a, o)]) = causalPolicyMixtureMass w π h := by
  simp_rw [causalPolicyMixtureMass_append]
  rw [sum_comm]
  simp_rw [← mul_sum, (hπ _ h).2, mul_one]
  rfl

theorem causalPolicyMixtureMass_child_le (w : I → ℝ) (hw : IsDist w)
    (π : I → CausalPolicy A O) (hπ : ∀ i, IsCausalPolicy (π i))
    (h : CausalHistory A O) (a : A) (o : O) :
    causalPolicyMixtureMass w π (h ++ [(a, o)]) ≤ causalPolicyMixtureMass w π h := by
  rw [← sum_causalPolicyMixtureMass_children w π hπ h o]
  exact single_le_sum (fun a' _ => causalPolicyMixtureMass_nonneg w hw π hπ (h ++ [(a', o)])) (mem_univ a)

/-- The mixture is normalized at every history, including null histories. -/
theorem isCausalPolicy_causalPolicyMixture [Nonempty A]
    (w : I → ℝ) (hw : IsDist w) (π : I → CausalPolicy A O)
    (hπ : ∀ i, IsCausalPolicy (π i)) : IsCausalPolicy (causalPolicyMixture w π) := by
  intro h
  by_cases hm : causalPolicyMixtureMass w π h = 0
  · have hc : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    constructor
    · intro a; simp only [causalPolicyMixture, if_pos hm]; positivity
    · simp [causalPolicyMixture, hm, hc]
  · constructor
    · intro a
      simp only [causalPolicyMixture, if_neg hm]
      exact div_nonneg (sum_nonneg fun i _ => mul_nonneg
        (mul_nonneg (hw.1 i) (causalPolicyProb_nonneg _ (hπ i) h)) ((hπ i h).1 a))
        (causalPolicyMixtureMass_nonneg w hw π hπ h)
    · simp only [causalPolicyMixture, if_neg hm]
      rw [← sum_div, sum_comm]
      simp_rw [← mul_sum, (hπ _ h).2, mul_one]
      exact div_self hm

/-- Posterior mixing telescopes to the once-sampled collector likelihood. -/
theorem causalPolicyProb_policyMixture (w : I → ℝ) (hw : IsDist w)
    (π : I → CausalPolicy A O) (hπ : ∀ i, IsCausalPolicy (π i)) (h : CausalHistory A O) :
    causalPolicyProb (causalPolicyMixture w π) h = causalPolicyMixtureMass w π h := by
  induction h using List.reverseRecOn with
  | nil => simpa [causalPolicyProb, causalPolicyProbFrom, causalPolicyMixtureMass] using hw.2.symm
  | append_singleton h ao ih =>
      rw [causalPolicyProb_append_singleton, ih]
      by_cases hm : causalPolicyMixtureMass w π h = 0
      · have hz : causalPolicyMixtureMass w π (h ++ [ao]) = 0 :=
          le_antisymm (by simpa [hm] using causalPolicyMixtureMass_child_le w hw π hπ h ao.1 ao.2)
            (causalPolicyMixtureMass_nonneg w hw π hπ _)
        simp [hm, hz]
      · simp only [causalPolicyMixture, if_neg hm]
        rw [← causalPolicyMixtureMass_append]
        exact mul_div_cancel₀ _ hm

/-- Every full finite record has exactly the mixture of the component laws. -/
theorem causalFiniteExperiment_policyMixture (w : I → ℝ) (hw : IsDist w)
    (π : I → CausalPolicy A O) (hπ : ∀ i, IsCausalPolicy (π i))
    (Qs : Θ → CausalResponse A O) (n : ℕ) :
    causalFiniteExperiment (causalPolicyMixture w π) Qs n =
      fun θ h => ∑ i, w i * causalFiniteExperiment (π i) Qs n θ h := by
  funext θ h
  simp only [causalFiniteExperiment, causalTraceProb_factor, causalPolicyProb_policyMixture w hw π hπ,
    causalPolicyMixtureMass, sum_mul, mul_assoc]

/-- Conditional collector weights; the prior itself supplies a valid null row. -/
def causalPolicyMixturePosterior (w : I → ℝ) (π : I → CausalPolicy A O)
    (h : CausalHistory A O) (i : I) : ℝ :=
  if causalPolicyMixtureMass w π h = 0 then w i
  else w i * causalPolicyProb (π i) h / causalPolicyMixtureMass w π h

theorem causalPolicyMixturePosterior_isDist (w : I → ℝ) (hw : IsDist w)
    (π : I → CausalPolicy A O) (hπ : ∀ i, IsCausalPolicy (π i)) (h : CausalHistory A O) :
    IsDist (causalPolicyMixturePosterior w π h) := by
  unfold causalPolicyMixturePosterior
  by_cases hm : causalPolicyMixtureMass w π h = 0
  · simpa only [if_pos hm] using hw
  · simp only [if_neg hm]
    constructor
    · intro i
      exact div_nonneg (mul_nonneg (hw.1 i) (causalPolicyProb_nonneg _ (hπ i) h))
        (causalPolicyMixtureMass_nonneg w hw π hπ h)
    · rw [← sum_div]
      exact div_self hm

/-- Bayes' cancellation identity, also valid when the total action likelihood is zero. -/
theorem causalPolicyMixtureMass_mul_posterior (w : I → ℝ) (hw : IsDist w)
    (π : I → CausalPolicy A O) (hπ : ∀ i, IsCausalPolicy (π i))
    (h : CausalHistory A O) (i : I) :
    causalPolicyMixtureMass w π h * causalPolicyMixturePosterior w π h i =
      w i * causalPolicyProb (π i) h := by
  by_cases hm : causalPolicyMixtureMass w π h = 0
  · have hi : w i * causalPolicyProb (π i) h ≤ causalPolicyMixtureMass w π h :=
      single_le_sum (fun j _ => mul_nonneg (hw.1 j) (causalPolicyProb_nonneg _ (hπ j) h)) (mem_univ i)
    have hz : w i * causalPolicyProb (π i) h = 0 :=
      le_antisymm (by simpa [hm] using hi) (mul_nonneg (hw.1 i) (causalPolicyProb_nonneg _ (hπ i) h))
    simp [hm, hz]
  · simp only [causalPolicyMixturePosterior, if_neg hm]
    exact mul_div_cancel₀ _ hm

/-- Recover the label while retaining the given complete history. This decoder
depends on the mixture and collectors, and contains no world argument. -/
def causalPolicyMixtureLabelDecoder (w : I → ℝ) (π : I → CausalPolicy A O) (n : ℕ) :
    CausalFiniteTrace A O n → I × CausalFiniteTrace A O n → ℝ := by
  classical
  exact fun h z => if h = z.2 then causalPolicyMixturePosterior w π (List.ofFn h) z.1 else 0

theorem causalPolicyMixtureLabelDecoder_stochastic (w : I → ℝ) (hw : IsDist w)
    (π : I → CausalPolicy A O) (hπ : ∀ i, IsCausalPolicy (π i)) (n : ℕ) :
    causalPolicyMixtureLabelDecoder w π n ∈
      stochasticRules (CausalFiniteTrace A O n) (I × CausalFiniteTrace A O n) := by
  classical
  intro h _
  have hp := causalPolicyMixturePosterior_isDist w hw π hπ (List.ofFn h)
  constructor
  · intro z
    dsimp [causalPolicyMixtureLabelDecoder]
    split_ifs <;> first | exact hp.1 _ | exact le_rfl
  · simpa [causalPolicyMixtureLabelDecoder, Fintype.sum_prod_type] using hp.2

/-- The recovered label and history have their exact joint law in every world. -/
theorem causalPolicyMixtureLabelDecoder_law (w : I → ℝ) (hw : IsDist w)
    (π : I → CausalPolicy A O) (hπ : ∀ i, IsCausalPolicy (π i))
    (Qs : Θ → CausalResponse A O) (n : ℕ) :
    finiteDecisionLaw (causalFiniteExperiment (causalPolicyMixture w π) Qs n)
      (causalPolicyMixtureLabelDecoder w π n) =
        mixtureCollector (fun i => causalFiniteExperiment (π i) Qs n) w := by
  classical
  funext θ z
  simp only [finiteDecisionLaw, causalPolicyMixtureLabelDecoder, mul_ite, mul_zero,
    sum_ite_eq', Finset.mem_univ, if_true, mixtureCollector, causalFiniteExperiment,
    causalTraceProb_factor, causalPolicyProb_policyMixture w hw π hπ]
  rw [mul_right_comm, causalPolicyMixtureMass_mul_posterior w hw π hπ]
  ring

/-- Full histories and explicitly labelled mixtures are exactly equivalent. -/
theorem causalPolicyMixture_recorded_blackwell_equiv (w : I → ℝ) (hw : IsDist w)
    (π : I → CausalPolicy A O) (hπ : ∀ i, IsCausalPolicy (π i))
    (Qs : Θ → CausalResponse A O) (n : ℕ) :
    FiniteBlackwellLE (mixtureCollector (fun i => causalFiniteExperiment (π i) Qs n) w)
      (causalFiniteExperiment (causalPolicyMixture w π) Qs n) ∧
    FiniteBlackwellLE (causalFiniteExperiment (causalPolicyMixture w π) Qs n)
      (mixtureCollector (fun i => causalFiniteExperiment (π i) Qs n) w) := by
  classical
  refine ⟨⟨_, causalPolicyMixtureLabelDecoder_stochastic w hw π hπ n,
    causalPolicyMixtureLabelDecoder_law w hw π hπ Qs n⟩, ?_⟩
  refine ⟨fun z h => if z.2 = h then 1 else 0, ?_, ?_⟩
  · intro z _
    exact ⟨fun h => by dsimp; split_ifs <;> norm_num, by simp⟩
  · rw [causalFiniteExperiment_policyMixture w hw π hπ Qs n]
    funext θ h
    simp [finiteDecisionLaw, mixtureCollector, Fintype.sum_prod_type]

/-- Every randomized policy's horizon experiment is equivalent to its
Kuhn mixture with the deterministic plan label retained. -/
theorem causalFiniteExperiment_kuhn_recorded_equiv [Nonempty A] [DecidableEq A] [DecidableEq O]
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π) (Qs : Θ → CausalResponse A O) (n : ℕ) :
    FiniteBlackwellLE
      (mixtureCollector (fun τ : CausalPlan A O n =>
        causalFiniteExperiment (causalPolicyOfPlan n τ) Qs n) (kuhnWeight π n))
      (causalFiniteExperiment π Qs n) ∧
    FiniteBlackwellLE (causalFiniteExperiment π Qs n)
      (mixtureCollector (fun τ : CausalPlan A O n =>
        causalFiniteExperiment (causalPolicyOfPlan n τ) Qs n) (kuhnWeight π n)) := by
  classical
  have heq : causalFiniteExperiment
      (causalPolicyMixture (kuhnWeight π n) (causalPolicyOfPlan n)) Qs n =
      causalFiniteExperiment π Qs n := by
    rw [causalFiniteExperiment_policyMixture _ (kuhnWeight_isDist π hπ n) _
      (isCausalPolicy_causalPolicyOfPlan n), causalFiniteExperiment_kuhn_decomposition π hπ Qs n]
  simpa only [heq] using causalPolicyMixture_recorded_blackwell_equiv
    (kuhnWeight π n) (kuhnWeight_isDist π hπ n) (causalPolicyOfPlan n)
    (isCausalPolicy_causalPolicyOfPlan n) Qs n

end

end IdExp
