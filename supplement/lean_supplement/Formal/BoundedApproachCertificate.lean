import Formal.ApproachScheme
import Formal.BinaryBlackwell

/-!
# Exact finite-row certificates for bounded-horizon causal approachability

This formalizes the semantic reduction in the supplementary bounded-horizon
approachability theorem: finitely many policy rows, stochastic decoders, and
two-sided slack bounds express precisely the strict or non-strict native
deficiency requirements.  In the non-strict direction, decoder attainment is
proved using compactness; it is not an assumption.  The strict converse uses
finiteness of the nonempty world class to take one strict worst-world bound.

`boundedCausalTraceMass` is the displayed degree-`t` product expression in
policy variables.  Its interpretation as the actual causal experiment is
proved for every table of valid policy rows, including horizon zero.  The
finite certificate constructs a full policy with the repository's default
tail, so finite-variable feasibility does not merely encode a hypothetical
experiment matrix.

This file does not formalize rational-expression encoding size, an ETR
decision procedure, or its PSPACE complexity.  Those computational assertions
in the written theorem remain separate from this checked equivalence.
-/

namespace IdExp

open Finset Set

noncomputable section

set_option linter.unusedSectionVars false

section SlackCertificates

variable {Θ X Y : Type*} [Fintype Θ] [Nonempty Θ]
  [Fintype X] [Fintype Y] [Nonempty Y]

/-- The two polynomial inequalities replacing one absolute-value residual. -/
def DecoderSlackBounds (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y)
    (G : X → Y → ℝ) (s : Θ → Y → ℝ) : Prop :=
  ∀ θ y, -s θ y ≤ (∑ x, E θ x * G x y) - F θ y ∧
    (∑ x, E θ x * G x y) - F θ y ≤ s θ y

/-- Absolute residuals always provide feasible slacks. -/
theorem decoderSlackBounds_abs (E : FiniteExperiment Θ X)
    (F : FiniteExperiment Θ Y) (G : X → Y → ℝ) :
    DecoderSlackBounds E F G
      (fun θ y => |(∑ x, E θ x * G x y) - F θ y|) := by
  intro θ y
  exact ⟨neg_abs_le _, le_abs_self _⟩

/-- Any feasible slack budget bounds the actual total-variation error. -/
theorem decodeErr_le_slack_budget (E : FiniteExperiment Θ X)
    (F : FiniteExperiment Θ Y) (G : X → Y → ℝ) (s : Θ → Y → ℝ)
    (hs : DecoderSlackBounds E F G s) (θ : Θ) :
    decodeErr E F G θ ≤ (1 / 2 : ℝ) * ∑ y, s θ y := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Finset.sum_le_sum fun y _ => abs_le.mpr (hs θ y)

/-- Exact non-strict slack formulation; compact decoder attainment closes
the potentially delicate boundary case `δ = c`. -/
theorem finiteDeficiency_le_iff_slack_certificate
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y) (c : ℝ) :
    finiteDeficiency E F ≤ c ↔
      ∃ G ∈ stochasticRules X Y, ∃ s : Θ → Y → ℝ,
        DecoderSlackBounds E F G s ∧
          ∀ θ, (1 / 2 : ℝ) * ∑ y, s θ y ≤ c := by
  constructor
  · intro hc
    obtain ⟨G, hG, herr⟩ := exists_decoder_eq_finiteDeficiency E F
    exact ⟨G, hG, (fun θ y => |(∑ x, E θ x * G x y) - F θ y|),
      decoderSlackBounds_abs E F G, fun θ => (herr θ).trans hc⟩
  · rintro ⟨G, hG, s, hs, hc⟩
    exact finiteDeficiency_le_of_decoder E F G hG c
      (fun θ => (decodeErr_le_slack_budget E F G s hs θ).trans (hc θ))

/-- Exact strict slack formulation; finitely many strict worldwise budgets
give a common strict worst-world budget. -/
theorem finiteDeficiency_lt_iff_slack_certificate
    (E : FiniteExperiment Θ X) (F : FiniteExperiment Θ Y) (c : ℝ) :
    finiteDeficiency E F < c ↔
      ∃ G ∈ stochasticRules X Y, ∃ s : Θ → Y → ℝ,
        DecoderSlackBounds E F G s ∧
          ∀ θ, (1 / 2 : ℝ) * ∑ y, s θ y < c := by
  constructor
  · intro hc
    obtain ⟨G, hG, herr⟩ := exists_decoder_eq_finiteDeficiency E F
    exact ⟨G, hG, (fun θ y => |(∑ x, E θ x * G x y) - F θ y|),
      decoderSlackBounds_abs E F G, fun θ => (herr θ).trans_lt hc⟩
  · rintro ⟨G, hG, s, hs, hc⟩
    apply (finiteDeficiency_le_of_decoder E F G hG (worstDecodeErr E F G)
      (decodeErr_le_worstDecodeErr E F G)).trans_lt
    unfold worstDecodeErr
    rw [Finset.sup'_lt_iff]
    intro θ _
    exact (decodeErr_le_slack_budget E F G s hs θ).trans_lt (hc θ)

end SlackCertificates

section FiniteRows

variable {A O Θ : Type*} [Fintype A] [Fintype O]
  [Nonempty A] [Nonempty O]

/-- Extend a finite table of behavioral rows by the fixed default tail. -/
def boundedCausalPolicy (t : ℕ) (x : CausalDecisionPoint A O t → A → ℝ)
    (hx : ∀ d, IsDist (x d)) : ValidCausalPolicy A O :=
  ⟨fun h => if hh : h.length < t then x (causalDecisionPointOfHistory t h hh)
      else defaultValidCausalPolicy.1 h, by
    intro h
    dsimp only
    split_ifs
    · exact hx _
    · exact defaultValidCausalPolicy.2 h⟩

theorem boundedCausalPolicy_isFiniteHorizon (t : ℕ)
    (x : CausalDecisionPoint A O t → A → ℝ) (hx : ∀ d, IsDist (x d)) :
    IsFiniteHorizonPolicy (boundedCausalPolicy t x hx) t := by
  intro h hh
  simp [boundedCausalPolicy, not_lt.mpr hh]

/-- The finite product of policy variables and supplied response constants. -/
def boundedCausalTraceMass (Qs : Θ → CausalResponse A O) (t : ℕ)
    (x : CausalDecisionPoint A O t → A → ℝ) :
    FiniteExperiment Θ (CausalFiniteTrace A O t) :=
  fun θ w => ∏ k : Fin t,
    x (causalTraceDecisionPoint w k) (w k).1 *
      Qs θ (causalTracePrefix w k) (w k).1 (w k).2

/-- Finite-row construction has exactly the displayed trace product law. -/
theorem causalFiniteExperiment_boundedCausalPolicy
    (Qs : Θ → CausalResponse A O) (t : ℕ)
    (x : CausalDecisionPoint A O t → A → ℝ) (hx : ∀ d, IsDist (x d)) :
    causalFiniteExperiment (boundedCausalPolicy t x hx).1 Qs t =
      boundedCausalTraceMass Qs t x := by
  funext θ w
  unfold causalFiniteExperiment
  rw [causalTraceProb_factor, causalPolicyProb_ofFn, causalResponseProb_ofFn,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  have hh : (causalTracePrefix w k).length < t := by
    simp [causalTracePrefix, k.isLt]
  simp [boundedCausalPolicy, hh, causalTraceDecisionPoint]

/-- Restricting any infinite behavioral policy gives its exact finite law. -/
theorem causalFiniteExperiment_eq_boundedCausalTraceMass
    (Qs : Θ → CausalResponse A O) (π : ValidCausalPolicy A O) (t : ℕ) :
    causalFiniteExperiment π.1 Qs t =
      boundedCausalTraceMass Qs t (fun d => π.1 (causalDecisionHistory d)) := by
  funext θ w
  unfold causalFiniteExperiment
  rw [causalTraceProb_factor, causalPolicyProb_ofFn, causalResponseProb_ofFn,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  simp only [causalDecisionHistory_traceDecisionPoint]

/-- Valid response tables and finite policy rows produce a valid experiment. -/
theorem boundedCausalTraceMass_valid
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ)) (t : ℕ)
    (x : CausalDecisionPoint A O t → A → ℝ) (hx : ∀ d, IsDist (x d)) :
    IsFiniteExperiment (boundedCausalTraceMass Qs t x) := by
  rw [← causalFiniteExperiment_boundedCausalPolicy Qs t x hx]
  exact causalFiniteExperiment_valid _ (boundedCausalPolicy t x hx).2 Qs hQ t

end FiniteRows

section BoundedFeasibility

variable {A O Θ J : Type*} [Fintype A] [Fintype O]
  [Nonempty A] [Nonempty O] [Fintype Θ] [Nonempty Θ] [Fintype J]

/-- The exact finite non-strict feasibility certificate for a finite menu of
heterogeneous native interventions and a fixed acquired horizon. -/
theorem exists_bounded_causal_deficiency_le_iff_certificate
    (Qs : Θ → CausalResponse A O) (t : ℕ)
    (q : J → CausalNativeTest A O) (c : J → ℝ) :
    (∃ π : ValidCausalPolicy A O, IsFiniteHorizonPolicy π t ∧
      ∀ j, causalPolicyTestDeficiency π Qs (q j) t ≤ c j) ↔
    ∃ x : CausalDecisionPoint A O t → A → ℝ, (∀ d, IsDist (x d)) ∧
      ∀ j, ∃ G ∈ stochasticRules (CausalFiniteTrace A O t)
          (CausalObservationTrace O (q j).1), ∃ s : Θ → CausalObservationTrace O (q j).1 → ℝ,
        DecoderSlackBounds (boundedCausalTraceMass Qs t x)
          (causalNativeTestExperiment Qs (q j)) G s ∧
        ∀ θ, (1 / 2 : ℝ) * ∑ y, s θ y ≤ c j := by
  constructor
  · rintro ⟨π, _, hπ⟩
    refine ⟨fun d => π.1 (causalDecisionHistory d), fun d => π.2 _, fun j => ?_⟩
    apply (finiteDeficiency_le_iff_slack_certificate _ _ _).mp
    rw [← causalFiniteExperiment_eq_boundedCausalTraceMass]
    exact hπ j
  · rintro ⟨x, hx, hcert⟩
    refine ⟨boundedCausalPolicy t x hx, boundedCausalPolicy_isFiniteHorizon t x hx,
      fun j => ?_⟩
    unfold causalPolicyTestDeficiency
    rw [causalFiniteExperiment_boundedCausalPolicy]
    exact (finiteDeficiency_le_iff_slack_certificate _ _ _).mpr (hcert j)

/-- Strict finite feasibility is likewise exact, with strictness placed on
the worldwise slack budgets, not on individual coordinate residuals. -/
theorem exists_bounded_causal_deficiency_lt_iff_certificate
    (Qs : Θ → CausalResponse A O) (t : ℕ)
    (q : J → CausalNativeTest A O) (c : J → ℝ) :
    (∃ π : ValidCausalPolicy A O, IsFiniteHorizonPolicy π t ∧
      ∀ j, causalPolicyTestDeficiency π Qs (q j) t < c j) ↔
    ∃ x : CausalDecisionPoint A O t → A → ℝ, (∀ d, IsDist (x d)) ∧
      ∀ j, ∃ G ∈ stochasticRules (CausalFiniteTrace A O t)
          (CausalObservationTrace O (q j).1), ∃ s : Θ → CausalObservationTrace O (q j).1 → ℝ,
        DecoderSlackBounds (boundedCausalTraceMass Qs t x)
          (causalNativeTestExperiment Qs (q j)) G s ∧
        ∀ θ, (1 / 2 : ℝ) * ∑ y, s θ y < c j := by
  constructor
  · rintro ⟨π, _, hπ⟩
    refine ⟨fun d => π.1 (causalDecisionHistory d), fun d => π.2 _, fun j => ?_⟩
    apply (finiteDeficiency_lt_iff_slack_certificate _ _ _).mp
    rw [← causalFiniteExperiment_eq_boundedCausalTraceMass]
    exact hπ j
  · rintro ⟨x, hx, hcert⟩
    refine ⟨boundedCausalPolicy t x hx, boundedCausalPolicy_isFiniteHorizon t x hx,
      fun j => ?_⟩
    unfold causalPolicyTestDeficiency
    rw [causalFiniteExperiment_boundedCausalPolicy]
    exact (finiteDeficiency_lt_iff_slack_certificate _ _ _).mpr (hcert j)

end BoundedFeasibility

end

end IdExp
