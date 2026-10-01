import Formal.PolicySimplexRowFamily
import Formal.InformationDeficiencyContinuity
import Formal.FiniteDecoderAttainment

/-!
# Approximately optimal information-gain policies are approximately admissible

The paper's headline comparison objective is information gain.  On the
fixed-horizon policy polytope the compact admissibility modulus applies to it
once two facts are available: the score is continuous on the polytope, and
it strictly preserves Blackwell domination of complete records.

* Continuity is the rowwise TV modulus of information composed with the
  policy-perturbation bound of the polytope; this holds for any
  `UniformRowFamily` and any score with a vanishing uniform-row modulus.
* Strictness is the **equality case of data processing**: on a finite world
  class with a full-support prior, an exact garbling with equal information
  is reversible by the Bayes reverse channel (strict Jensen for `-ent` on the
  simplex).  Full support is where the prior enters: at a null-prior world
  the reverse channel is unconstrained.

The result is the paper's qualitative admissibility statement for
information gain in exact form: for every `ε` there are `η, ρ > 0` such that
every `η`-optimal information-gain policy table at horizon `H` simulates every
`ρ`-dominating table within `ε`.  No rate, no decoder attainment beyond
finiteness of the class, and no restriction on the response worlds.
-/

namespace IdExp

open Set Filter Topology

noncomputable section

set_option linter.unusedSectionVars false

/-! ## Continuity of a uniformly row-continuous score on a row family -/

section Continuity

variable {Θ X T : Type*} [Fintype X] [TopologicalSpace T]

/-- Any score with a vanishing uniform-row modulus is continuous along a
uniformly row-continuous family. -/
theorem UniformRowFamily.continuous_score (fam : UniformRowFamily Θ X T)
    (S : FiniteExperiment Θ X → ℝ) (ω : ℝ → ℝ) (hω : VanishingModulus ω)
    (hS : ∀ E F : FiniteExperiment Θ X, IsFiniteExperiment E → IsFiniteExperiment F →
      ∀ r : ℝ, 0 ≤ r → (∀ θ, finiteTV (E θ) (F θ) ≤ r) → |S E - S F| ≤ ω r) :
    Continuous (fun t => S (fam.exp t)) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [Metric.continuousAt_iff']
  intro ε hε
  obtain ⟨η, hη, hηε⟩ := hω (ε / 2) (by positivity)
  have hev := fam.uniformRow t₀ (η / 2) (by positivity)
  refine hev.mono fun t ht => ?_
  have hb := hS _ _ (fam.valid t) (fam.valid t₀) (η / 2) (by positivity) ht
  have h2 := hηε (η / 2) (by positivity) (by linarith)
  rw [Real.dist_eq]
  linarith

end Continuity

/-! ## Equality case of data processing for information gain -/

section EqualityCase

variable {Θ X Y : Type*} [Fintype Θ] [Fintype X] [Fintype Y]

theorem finiteBayesPotential_neg_ent (α : Θ → ℝ) {Z : Type*} [Fintype Z] (F : Θ → Z → ℝ) :
    finiteBayesPotential (fun p => -ent p) α F = -finiteBayesPotential ent α F := by
  simp only [finiteBayesPotential, mul_neg, Finset.sum_neg_distrib]

/-- **Equality case of data processing.**  On a finite class with a
full-support prior, an exact garbling that loses no information is
reversible by a single stochastic channel valid in every world. -/
theorem exists_reverse_of_information_eq [Nonempty X] (α : Θ → ℝ) (hα : IsDist α)
    (hpos : ∀ θ, 0 < α θ) (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (G : X → Y → ℝ) (hG : G ∈ stochasticRules X Y)
    (heq : finiteBayesInformation α (finiteDecisionLaw E G) = finiteBayesInformation α E) :
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
  have hpot : Q.potential (fun p => -ent p) = P.potential (fun p => -ent p) := by
    show (finitePriorPosteriorSystem α hα (finiteDecisionLaw E G) hEG).potential (fun p => -ent p) =
      (finitePriorPosteriorSystem α hα E hE).potential (fun p => -ent p)
    rw [finitePriorPosteriorSystem_potential, finitePriorPosteriorSystem_potential,
      finiteBayesPotential_neg_ent, finiteBayesPotential_neg_ent]
    unfold finiteBayesInformation at heq
    linarith
  have hrev := signalPosterior_reverse_of_potential_eq P Q G hG hGF hmass (fun p => -ent p)
    (stdSimplex ℝ Θ) strictConvexOn_neg_ent_simplex
    (finitePriorPosteriorSystem_density_mem α hα E hE) hpot
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

/-- **Strict data processing.**  Without a reverse channel, an exact garbling
strictly loses information under a full-support prior. -/
theorem finiteBayesInformation_garble_lt_of_no_reverse [Nonempty X] (α : Θ → ℝ)
    (hα : IsDist α) (hpos : ∀ θ, 0 < α θ) (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E)
    (G : X → Y → ℝ) (hG : G ∈ stochasticRules X Y)
    (hnot : ¬ ∃ R ∈ stochasticRules Y X, finiteDecisionLaw (finiteDecisionLaw E G) R = E) :
    finiteBayesInformation α (finiteDecisionLaw E G) < finiteBayesInformation α E := by
  refine lt_of_le_of_ne (finiteBayesInformation_garble_le α hα E hE G hG) fun heq => ?_
  exact hnot (exists_reverse_of_information_eq α hα hpos E hE G hG heq)

/-- **Information strictly preserves Blackwell domination on finite classes.**
If `F` simulates `E` exactly and scores no more information, then `E`
simulates `F` exactly. -/
theorem information_strict_of_deficiency_eq_zero [Nonempty Θ] [Nonempty X] [Nonempty Y]
    (α : Θ → ℝ) (hα : IsDist α) (hpos : ∀ θ, 0 < α θ)
    (E : FiniteExperiment Θ X) (hE : IsFiniteExperiment E) (F : FiniteExperiment Θ Y)
    (h0 : finiteDeficiency E F = 0)
    (hle : finiteBayesInformation α E ≤ finiteBayesInformation α F) :
    finiteDeficiency F E = 0 := by
  obtain ⟨G, hG, hGF⟩ := finiteBlackwellLE_of_finiteDeficiency_eq_zero E F h0
  have hdp := finiteBayesInformation_garble_le α hα E hE G hG
  rw [hGF] at hdp
  have heq : finiteBayesInformation α (finiteDecisionLaw E G) = finiteBayesInformation α E := by
    rw [hGF]; exact le_antisymm hdp hle
  obtain ⟨R, hR, hRE⟩ := exists_reverse_of_information_eq α hα hpos E hE G hG heq
  rw [hGF] at hRE
  exact finiteDeficiency_eq_zero_of_finiteBlackwellLE F E ⟨R, hR, hRE⟩

end EqualityCase

/-! ## Information gain on the fixed-horizon policy polytope -/

section Polytope

variable {A O Θ : Type*} [Fintype A] [Fintype O] [Nonempty A] [Nonempty O]
  [Fintype Θ] [Nonempty Θ]

/-- The information-gain score of a policy table at horizon `H`. -/
def policyRowInformation (α : Θ → ℝ) (Qs : Θ → CausalResponse A O) (H : ℕ)
    (x : SilentHorizonPolicyRows A O H) : ℝ :=
  finiteBayesInformation α (policyRowExperiment Qs H x)

theorem continuous_policyRowInformation (α : Θ → ℝ) (hα : IsDist α)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ)) (H : ℕ) :
    Continuous (policyRowInformation α Qs H) := by
  have hω : VanishingModulus
      (fun r => 2 * cappedEntropyModulus (Fintype.card (CausalFiniteTrace A O H)) r) := by
    intro ε hε
    obtain ⟨η, hη, h⟩ :=
      cappedEntropyModulus_vanishing (Fintype.card (CausalFiniteTrace A O H)) (ε / 2)
        (by positivity)
    exact ⟨η, hη, fun r hr0 hr => by have := h r hr0 hr; linarith⟩
  exact (policyRowFamily Qs hQ H).continuous_score (finiteBayesInformation α) _ hω
    fun E F hE hF r hr0 hrow => abs_finiteBayesInformation_sub_le α hα E F hE hF r hr0 hrow

/-- Information strictly preserves Blackwell domination of complete records
on the polytope. -/
theorem policyRowInformation_strict (α : Θ → ℝ) (hα : IsDist α) (hpos : ∀ θ, 0 < α θ)
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ)) (H : ℕ)
    (s t : SilentHorizonPolicyRows A O H)
    (h0 : finiteDeficiency (policyRowExperiment Qs H t) (policyRowExperiment Qs H s) = 0)
    (hle : policyRowInformation α Qs H t ≤ policyRowInformation α Qs H s) :
    finiteDeficiency (policyRowExperiment Qs H s) (policyRowExperiment Qs H t) = 0 :=
  information_strict_of_deficiency_eq_zero α hα hpos _ (policyRowExperiment_valid Qs hQ H t) _
    h0 hle

/-- **Exact information maximizers are Blackwell-admissible** on the polytope:
any table simulating an optimum exactly is simulated by it exactly. -/
theorem policyRowInformation_maximizer_admissible (α : Θ → ℝ) (hα : IsDist α)
    (hpos : ∀ θ, 0 < α θ) (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (H : ℕ) (s : SilentHorizonPolicyRows A O H)
    (hmax : ∀ t, policyRowInformation α Qs H t ≤ policyRowInformation α Qs H s)
    (t : SilentHorizonPolicyRows A O H)
    (h0 : finiteDeficiency (policyRowExperiment Qs H t) (policyRowExperiment Qs H s) = 0) :
    finiteDeficiency (policyRowExperiment Qs H s) (policyRowExperiment Qs H t) = 0 :=
  policyRowInformation_strict α hα hpos Qs hQ H s t h0 (hmax t)

/-- **Admissibility modulus for information gain.**  For a full-support prior
on a finite class, every `ε` has joint tolerances `η, ρ > 0` on the
horizon-`H` polytope: a table simulating another within `ρ` while gaining at
most `η` less information is itself simulated within `ε`. -/
theorem policyRowInformation_admissibility_modulus (α : Θ → ℝ) (hα : IsDist α)
    (hpos : ∀ θ, 0 < α θ) (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (H : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ s t : SilentHorizonPolicyRows A O H,
      finiteDeficiency (policyRowExperiment Qs H t) (policyRowExperiment Qs H s) ≤ ρ →
        policyRowInformation α Qs H t ≤ policyRowInformation α Qs H s + η →
          finiteDeficiency (policyRowExperiment Qs H s) (policyRowExperiment Qs H t) ≤ ε :=
  policyRow_admissibility_modulus Qs hQ H (policyRowInformation α Qs H)
    (continuous_policyRowInformation α hα Qs hQ H)
    (fun s t h0 hle => policyRowInformation_strict α hα hpos Qs hQ H s t h0 hle)

/-- **Approximately optimal information-gain tables are approximately
admissible**: an `η`-optimal table simulates every `ρ`-dominating table
within `ε`. -/
theorem policyRowInformation_eta_optimal_simulates_rho_dominators (α : Θ → ℝ) (hα : IsDist α)
    (hpos : ∀ θ, 0 < α θ) (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (H : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ s : SilentHorizonPolicyRows A O H,
      (∀ t, policyRowInformation α Qs H t ≤ policyRowInformation α Qs H s + η) →
        ∀ t, finiteDeficiency (policyRowExperiment Qs H t) (policyRowExperiment Qs H s) ≤ ρ →
          finiteDeficiency (policyRowExperiment Qs H s) (policyRowExperiment Qs H t) ≤ ε :=
  policyRow_eta_optimal_simulates_rho_dominators Qs hQ H (policyRowInformation α Qs H)
    (continuous_policyRowInformation α hα Qs hQ H)
    (fun s t h0 hle => policyRowInformation_strict α hα hpos Qs hQ H s t h0 hle)

end Polytope

end

end IdExp
