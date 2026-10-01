import Formal.InformationPolytopeAdmissibility
import Formal.QuadraticPosterior
import Formal.CrossingPartitionScores

/-!
# Strictly convex posterior potentials are admissible on the policy polytope

The paper's remark after the compact-family modulus: "a bounded continuous
strictly convex posterior-measure potential has a continuous finite-signal
expected score (vanishing predictive masses contribute vanishing terms), and
the full-support likelihood hypotheses supply its strict comparison; such
objectives therefore have this qualitative guarantee too."  This module
proves it for every posterior potential `Φ` that is continuous and strictly
convex on the simplex, on a finite world class with a full-support prior:

* the equality case of data processing for `Φ` (the Bayes reverse channel
  reverses any exact garbling that loses no expected potential), hence strict
  preservation of Blackwell domination;
* continuity of `E ↦ Σ_x m_x(E) Φ(π_x(E))` on nonnegative experiments —
  at a null predictive mass the term is squeezed by `|Φ| ≤ M` times the mass;
* continuity of the complete-record experiment in the policy table.

The compact admissibility modulus then applies.  The paper's second
objective, squared posterior movement, is the instance
`Φ = posteriorQuadraticPotential`, which is shown strictly convex on the
simplex.
-/

namespace IdExp

open Set Filter Topology

noncomputable section

set_option linter.unusedSectionVars false

/-! ## The quadratic potential is strictly convex on the simplex -/

section Quadratic

variable {Θ : Type*} [Fintype Θ]

theorem strictConvexOn_posteriorQuadraticPotential :
    StrictConvexOn ℝ (stdSimplex ℝ Θ) (posteriorQuadraticPotential : (Θ → ℝ) → ℝ) := by
  refine ⟨convex_stdSimplex ℝ Θ, ?_⟩
  intro p _ q _ hpq a b ha hb hab
  simp only [posteriorQuadraticPotential, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  have he : ∀ θ, a * (p θ)^2 + b * (q θ)^2 - (a * p θ + b * q θ)^2 =
      a * b * (p θ - q θ)^2 := by
    intro θ
    have hb' : b = 1 - a := by linarith
    rw [hb']
    ring
  obtain ⟨θ₀, hθ₀⟩ : ∃ θ, p θ ≠ q θ := Function.ne_iff.1 hpq
  have hpos : 0 < ∑ θ, a * b * (p θ - q θ)^2 := by
    apply Finset.sum_pos' (fun θ _ => mul_nonneg (mul_nonneg ha.le hb.le) (sq_nonneg _))
    exact ⟨θ₀, Finset.mem_univ _, mul_pos (mul_pos ha hb) (sq_pos_iff.2 (sub_ne_zero.2 hθ₀))⟩
  have hsum : ∑ θ, (a * (p θ)^2 + b * (q θ)^2) - ∑ θ, (a * p θ + b * q θ)^2 =
      ∑ θ, a * b * (p θ - q θ)^2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun θ _ => he θ
  linarith

end Quadratic

/-! ## Equality case of data processing for a strictly convex potential -/

section EqualityCase

variable {Θ X Y : Type*} [Fintype Θ] [Fintype X] [Fintype Y]

/-- **Equality case of data processing for posterior potentials.**  On a finite
class with a full-support prior, an exact garbling that loses no expected
strictly convex potential is reversible by a single stochastic channel. -/
theorem exists_reverse_of_potential_eq [Nonempty X] (Φ : (Θ → ℝ) → ℝ)
    (hΦ : StrictConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (hpos : ∀ θ, 0 < α θ)
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (G : X → Y → ℝ) (hG : G ∈ stochasticRules X Y)
    (heq : finiteBayesPotential Φ α (finiteDecisionLaw E G) = finiteBayesPotential Φ α E) :
    ∃ R ∈ stochasticRules Y X, finiteDecisionLaw (finiteDecisionLaw E G) R = E := by
  classical
  have hEG : IsFiniteExperiment (finiteDecisionLaw E G) := finiteDecisionLaw_valid E hE G hG
  let P := finitePriorPosteriorSystem α hα E hE
  let Q := finitePriorPosteriorSystem α hα (finiteDecisionLaw E G) hEG
  have hGF : finiteDecisionLaw (fun θ x => α θ * E θ x) G =
      (fun θ y => α θ * finiteDecisionLaw E G θ y) := by
    funext θ y
    simp only [finiteDecisionLaw]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hmass : ∀ y, ∑ x, P.mass x * G x y = Q.mass y := by
    intro y
    simp only [P, Q, finitePriorPosteriorSystem, finiteBayesMass, finiteDecisionLaw]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro θ _
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hpot : Q.potential Φ = P.potential Φ := by
    show (finitePriorPosteriorSystem α hα (finiteDecisionLaw E G) hEG).potential Φ =
      (finitePriorPosteriorSystem α hα E hE).potential Φ
    rw [finitePriorPosteriorSystem_potential, finitePriorPosteriorSystem_potential]
    exact heq
  have hrev := signalPosterior_reverse_of_potential_eq P Q G hG hGF hmass Φ
    (stdSimplex ℝ Θ) hΦ (finitePriorPosteriorSystem_density_mem α hα E hE) hpot
  refine ⟨signalPosteriorReverse P Q G, signalPosteriorReverse_stochastic P Q G hG hmass, ?_⟩
  funext θ x
  have h := congrFun (congrFun hrev θ) x
  have hl : finiteDecisionLaw (fun θ y => α θ * finiteDecisionLaw E G θ y)
      (signalPosteriorReverse P Q G) θ x =
      α θ * finiteDecisionLaw (finiteDecisionLaw E G) (signalPosteriorReverse P Q G) θ x := by
    simp only [finiteDecisionLaw]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [hl] at h
  exact mul_left_cancel₀ (hpos θ).ne' h

/-- **Strictly convex potentials strictly preserve Blackwell domination** on
finite classes with a full-support prior. -/
theorem potential_strict_of_deficiency_eq_zero [Nonempty Θ] [Nonempty X] [Nonempty Y]
    (Φ : (Θ → ℝ) → ℝ) (hΦ : StrictConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (hpos : ∀ θ, 0 < α θ)
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E) (F : FiniteExperiment Θ Y)
    (h0 : finiteDeficiency E F = 0)
    (hle : finiteBayesPotential Φ α E ≤ finiteBayesPotential Φ α F) :
    finiteDeficiency F E = 0 := by
  obtain ⟨G, hG, hGF⟩ := finiteBlackwellLE_of_finiteDeficiency_eq_zero E F h0
  have hdp := finiteBayesPotential_garble_le α hα E hE G hG Φ hΦ.convexOn
  rw [hGF] at hdp
  have heq : finiteBayesPotential Φ α (finiteDecisionLaw E G) = finiteBayesPotential Φ α E := by
    rw [hGF]; exact le_antisymm hdp hle
  obtain ⟨R, hR, hRE⟩ := exists_reverse_of_potential_eq Φ hΦ α hα hpos E hE G hG heq
  rw [hGF] at hRE
  exact finiteDeficiency_eq_zero_of_finiteBlackwellLE F E ⟨R, hR, hRE⟩

end EqualityCase

/-! ## Continuity of the expected potential on nonnegative experiments -/

section Continuity

variable {Θ X : Type*} [Fintype Θ] [Fintype X]

/-- Experiments with nonnegative entries. -/
def nonnegExperiments (Θ X : Type*) : Set (Θ → X → ℝ) := {E | ∀ θ x, 0 ≤ E θ x}

theorem continuous_finiteBayesMass_apply (α : Θ → ℝ) (x : X) :
    Continuous fun E : Θ → X → ℝ => finiteBayesMass α E x := by
  unfold finiteBayesMass
  exact continuous_finset_sum _ fun θ _ =>
    continuous_const.mul ((continuous_apply x).comp (continuous_apply θ))

/-- A bounded potential makes each signal's term at most `M` times its mass. -/
theorem finiteBayesPotential_term_abs_le (Φ : (Θ → ℝ) → ℝ) (M : ℝ)
    (hM : ∀ p ∈ stdSimplex ℝ Θ, |Φ p| ≤ M) (α : Θ → ℝ) (hα : ∀ θ, 0 ≤ α θ)
    (E : Θ → X → ℝ) (hE : ∀ θ x, 0 ≤ E θ x) (x : X) :
    |finiteBayesMass α E x * Φ (finiteBayesPosterior α E x)| ≤ M * finiteBayesMass α E x := by
  by_cases hx : finiteBayesMass α E x = 0
  · rw [hx]; simp
  · rw [abs_mul, abs_of_nonneg (finiteBayesMass_nonneg α E hα hE x), mul_comm]
    exact mul_le_mul_of_nonneg_right (hM _ (finiteBayesPosterior_mem_simplex α E hα hE x hx))
      (finiteBayesMass_nonneg α E hα hE x)

/-- **The expected potential is continuous on nonnegative experiments** for
any potential continuous on the simplex. -/
theorem continuousOn_finiteBayesPotential (Φ : (Θ → ℝ) → ℝ)
    (hΦ : ContinuousOn Φ (stdSimplex ℝ Θ)) (α : Θ → ℝ) (hα : ∀ θ, 0 ≤ α θ) :
    ContinuousOn (fun E : Θ → X → ℝ => finiteBayesPotential Φ α E) (nonnegExperiments Θ X) := by
  obtain ⟨M, hM⟩ : ∃ M, ∀ p ∈ stdSimplex ℝ Θ, |Φ p| ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_stdSimplex ℝ Θ).bddAbove_image hΦ.abs
    exact ⟨M, fun p hp => hM ⟨p, hp, rfl⟩⟩
  unfold finiteBayesPotential
  apply continuousOn_finset_sum
  intro x _
  intro E₀ hE₀
  have hmass := continuous_finiteBayesMass_apply α x (X := X)
  by_cases h0 : finiteBayesMass α E₀ x = 0
  · -- squeeze: the term is at most `M · mass`, which tends to `0`
    have hval : finiteBayesMass α E₀ x * Φ (finiteBayesPosterior α E₀ x) = 0 := by
      rw [h0, zero_mul]
    rw [ContinuousWithinAt, hval]
    apply squeeze_zero_norm' (a := fun E => M * finiteBayesMass α E x)
    · exact eventually_nhdsWithin_of_forall fun E hE => by
        rw [Real.norm_eq_abs]
        exact finiteBayesPotential_term_abs_le Φ M hM α hα E hE x
    · have : Tendsto (fun E => M * finiteBayesMass α E x) (𝓝 E₀) (𝓝 (M * finiteBayesMass α E₀ x)) :=
        (continuous_const.mul hmass).tendsto E₀
      rw [h0, mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
  · -- composition on the neighbourhood where the mass is nonzero
    have hopen : {E : Θ → X → ℝ | finiteBayesMass α E x ≠ 0} ∈ 𝓝 E₀ :=
      (isOpen_ne_fun hmass continuous_const).mem_nhds h0
    rw [← continuousWithinAt_inter hopen]
    have hden : ContinuousAt (fun E : Θ → X → ℝ => ∑ c, α c * E c x) E₀ := hmass.continuousAt
    have h0' : (∑ c, α c * E₀ c x) ≠ 0 := h0
    have hinv : ContinuousAt (fun E : Θ → X → ℝ => (∑ c, α c * E c x)⁻¹) E₀ := hden.inv₀ h0'
    have hpost : ContinuousAt (fun E : Θ → X → ℝ => finiteBayesPosterior α E x) E₀ := by
      unfold finiteBayesPosterior
      simp only [div_eq_mul_inv]
      refine continuousAt_pi.2 fun θ => ?_
      have hproj : Continuous fun E : Θ → X → ℝ => E θ x :=
        (continuous_apply x).comp (continuous_apply θ)
      have hcoord : ContinuousAt (fun E : Θ → X → ℝ => α θ * E θ x) E₀ :=
        (continuous_const.mul hproj).continuousAt
      exact hcoord.mul hinv
    refine hmass.continuousWithinAt.mul ?_
    refine ContinuousWithinAt.comp (hΦ _ ?_) hpost.continuousWithinAt ?_
    · exact finiteBayesPosterior_mem_simplex α E₀ hα hE₀ x h0
    · intro E hE
      exact finiteBayesPosterior_mem_simplex α E hα hE.1 x hE.2

end Continuity

/-! ## Admissibility on the policy polytope -/

section Polytope

variable {A O Θ : Type*} [Fintype A] [Fintype O] [Nonempty A] [Nonempty O]
  [Fintype Θ] [Nonempty Θ]

/-- The complete-record experiment is continuous in the policy table, entrywise. -/
theorem continuous_policyRowExperiment (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (H : ℕ) :
    Continuous (policyRowExperiment Qs H) := by
  refine continuous_pi fun θ => continuous_pi fun w => ?_
  rw [Metric.continuous_iff]
  intro x ε hε
  set C : ℝ := (H : ℝ) * ((Fintype.card A : ℝ) / 2) with hC
  have hC0 : 0 ≤ C := by positivity
  refine ⟨ε / (C + 1), by positivity, fun y hy => ?_⟩
  have htv := finiteTV_silentHorizonPolicyOfRows_experiment_le Qs hQ H y x θ
  have hsum : ∑ w, policyRowExperiment Qs H y θ w = ∑ w, policyRowExperiment Qs H x θ w := by
    rw [(policyRowExperiment_valid Qs hQ H y θ).2, (policyRowExperiment_valid Qs hQ H x θ).2]
  have hc := finiteTV_coord_abs_le (policyRowExperiment Qs H y θ) (policyRowExperiment Qs H x θ) hsum w
  have hlt : C * (ε / (C + 1)) < ε := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity : (0:ℝ) < C + 1)]
    nlinarith
  rw [Real.dist_eq]
  calc |policyRowExperiment Qs H y θ w - policyRowExperiment Qs H x θ w|
      ≤ finiteTV (policyRowExperiment Qs H y θ) (policyRowExperiment Qs H x θ) := hc
    _ ≤ (H : ℝ) * (((Fintype.card A : ℝ) / 2) * dist y x) := htv
    _ = C * dist y x := by rw [hC]; ring
    _ ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left hy.le hC0
    _ < ε := hlt

/-- The expected potential of the complete record is continuous in the policy table. -/
theorem continuous_policyRowPotential (Φ : (Θ → ℝ) → ℝ) (hΦ : ContinuousOn Φ (stdSimplex ℝ Θ))
    (α : Θ → ℝ) (hα : IsDist α) (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (H : ℕ) :
    Continuous fun x : SilentHorizonPolicyRows A O H =>
      finiteBayesPotential Φ α (policyRowExperiment Qs H x) :=
  (continuousOn_finiteBayesPotential Φ hΦ α hα.1).comp_continuous
    (continuous_policyRowExperiment Qs hQ H)
    fun x θ w => (policyRowExperiment_valid Qs hQ H x θ).1 w

/-- **Admissibility modulus for every continuous strictly convex posterior
potential** on the horizon-`H` policy polytope, under a full-support prior. -/
theorem policyRowPotential_admissibility_modulus (Φ : (Θ → ℝ) → ℝ)
    (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ)) (hΦs : StrictConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (hpos : ∀ θ, 0 < α θ)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ)) (H : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ s t : SilentHorizonPolicyRows A O H,
      finiteDeficiency (policyRowExperiment Qs H t) (policyRowExperiment Qs H s) ≤ ρ →
        finiteBayesPotential Φ α (policyRowExperiment Qs H t) ≤
          finiteBayesPotential Φ α (policyRowExperiment Qs H s) + η →
          finiteDeficiency (policyRowExperiment Qs H s) (policyRowExperiment Qs H t) ≤ ε :=
  policyRow_admissibility_modulus Qs hQ H
    (fun x => finiteBayesPotential Φ α (policyRowExperiment Qs H x))
    (continuous_policyRowPotential Φ hΦc α hα Qs hQ H)
    (fun s t h0 hle => potential_strict_of_deficiency_eq_zero Φ hΦs α hα hpos _
      (policyRowExperiment_valid Qs hQ H t) _ h0 hle)

/-- **Approximately optimal tables for a strictly convex potential are
approximately admissible.** -/
theorem policyRowPotential_eta_optimal_simulates_rho_dominators (Φ : (Θ → ℝ) → ℝ)
    (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ)) (hΦs : StrictConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (hpos : ∀ θ, 0 < α θ)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ)) (H : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ s : SilentHorizonPolicyRows A O H,
      (∀ t, finiteBayesPotential Φ α (policyRowExperiment Qs H t) ≤
        finiteBayesPotential Φ α (policyRowExperiment Qs H s) + η) →
        ∀ t, finiteDeficiency (policyRowExperiment Qs H t) (policyRowExperiment Qs H s) ≤ ρ →
          finiteDeficiency (policyRowExperiment Qs H s) (policyRowExperiment Qs H t) ≤ ε :=
  policyRow_eta_optimal_simulates_rho_dominators Qs hQ H
    (fun x => finiteBayesPotential Φ α (policyRowExperiment Qs H x))
    (continuous_policyRowPotential Φ hΦc α hα Qs hQ H)
    (fun s t h0 hle => potential_strict_of_deficiency_eq_zero Φ hΦs α hα hpos _
      (policyRowExperiment_valid Qs hQ H t) _ h0 hle)

/-- **Squared posterior movement is admissible on the policy polytope**: the
paper's second objective satisfies the same joint-tolerance guarantee as
information gain. -/
theorem policyRowQuadratic_eta_optimal_simulates_rho_dominators
    (α : Θ → ℝ) (hα : IsDist α) (hpos : ∀ θ, 0 < α θ)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ)) (H : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ s : SilentHorizonPolicyRows A O H,
      (∀ t, quadraticPosteriorScore α (policyRowExperiment Qs H t) ≤
        quadraticPosteriorScore α (policyRowExperiment Qs H s) + η) →
        ∀ t, finiteDeficiency (policyRowExperiment Qs H t) (policyRowExperiment Qs H s) ≤ ρ →
          finiteDeficiency (policyRowExperiment Qs H s) (policyRowExperiment Qs H t) ≤ ε := by
  intro ε hε
  obtain ⟨η, hη, ρ, hρ, h⟩ := policyRowPotential_eta_optimal_simulates_rho_dominators
    posteriorQuadraticPotential continuous_posteriorQuadraticPotential.continuousOn
    strictConvexOn_posteriorQuadraticPotential α hα hpos Qs hQ H ε hε
  refine ⟨η, hη, ρ, hρ, fun s hs t ht => h s (fun t => ?_) t ht⟩
  have := hs t
  unfold quadraticPosteriorScore at this
  linarith

end Polytope

end

end IdExp
