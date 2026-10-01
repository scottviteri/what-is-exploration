import Formal.Hellinger
import Formal.CausalFiniteRecovery

/-!
# Worst-pair terminal Hellinger separation on causal paths

This supporting objective (`thm:finite-objectives` in the full reader) compares
the actual complete-path laws of distinct worlds and takes their worst-pair
separation. For a finite class with at least two worlds it has value one exactly
at identifying policies. If full revelation is attainable, these are exactly
its maximizers and exactly the natively sufficient policies.

It is not the sequential posterior-movement reward in the selected paper's
Hellinger row (`PosteriorMovement.lean`). That reward compares consecutive
posteriors and sums their expected movement over time; this objective compares
world-indexed terminal laws. Moreover, on probability laws `Hellinger.lean`
uses `1 - affinity`, whereas the posterior reward uses the sum of squared
square-root differences, twice that normalization. The identification theorem
here does not apply to that reward or contradict its four-bit counterexample.

The at-least-two-world restriction is essential: `worstPairHellinger` uses an
extended-real infimum, infinite on the empty set of distinct pairs.
-/

namespace IdExp

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Θ : Type*} [Fintype Θ] [Nontrivial Θ] [DecidableEq Θ]
  [MeasurableSpace Θ] [MeasurableSingletonClass Θ]
  {A O : Type*} [Fintype A] [Fintype O] [Nonempty A] [Nonempty O]
  [MeasurableSpace A] [MeasurableSpace O]
  [MeasurableSingletonClass A] [MeasurableSingletonClass O]

noncomputable def causalHellingerObjective
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) : ℝ≥0∞ :=
  worstPairHellinger (fun θ => (causalPathExperiment Qs hQ π θ : Measure (CausalTraj A O)))

omit [Fintype Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ] [DecidableEq Θ] in
theorem causalHellingerObjective_le_one
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) : causalHellingerObjective Qs hQ π ≤ 1 :=
  worstPairHellinger_le_one _

theorem causalHellingerObjective_eq_one_iff_exactlyIdentifies
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (π : ValidCausalPolicy A O) :
    causalHellingerObjective Qs hQ π = 1 ↔ CausalExactlyIdentifies Qs hQ π := by
  unfold causalHellingerObjective
  rw [worstPairHellinger_eq_one_iff_pairwise_mutuallySingular _
    (isProbabilityMeasure_causalPathExperiment' Qs hQ π)]
  exact (causalExactlyIdentifies_iff_pairwise_mutuallySingular Qs hQ π).symm

theorem causalHellingerObjective_isGreatest_one_iff_attainable
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ)) :
    IsGreatest (Set.range (causalHellingerObjective Qs hQ)) 1 ↔
      CausalFullRevelationAttainable Qs hQ := by
  rw [causalFullRevelationAttainable_iff_exactlyIdentifies Qs hQ]
  constructor
  · rintro ⟨⟨π, hπ⟩, _⟩
    exact ⟨π, (causalHellingerObjective_eq_one_iff_exactlyIdentifies Qs hQ π).1 hπ⟩
  · rintro ⟨π, hπ⟩
    refine ⟨⟨π, (causalHellingerObjective_eq_one_iff_exactlyIdentifies Qs hQ π).2 hπ⟩, ?_⟩
    rintro _ ⟨σ, rfl⟩
    exact causalHellingerObjective_le_one Qs hQ σ

theorem causalHellingerObjective_maximizer_iff_exactlyIdentifies
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hattain : CausalFullRevelationAttainable Qs hQ) (π : ValidCausalPolicy A O) :
    (∀ σ, causalHellingerObjective Qs hQ σ ≤ causalHellingerObjective Qs hQ π) ↔
      CausalExactlyIdentifies Qs hQ π := by
  have hmax := (causalHellingerObjective_isGreatest_one_iff_attainable Qs hQ).2 hattain
  constructor
  · intro h
    apply (causalHellingerObjective_eq_one_iff_exactlyIdentifies Qs hQ π).1
    obtain ⟨σ, hσ⟩ := hmax.1
    exact le_antisymm (causalHellingerObjective_le_one Qs hQ π) (hσ ▸ h σ)
  · intro hid σ
    rw [(causalHellingerObjective_eq_one_iff_exactlyIdentifies Qs hQ π).2 hid]
    exact causalHellingerObjective_le_one Qs hQ σ

/-- The exact causal argmax statement for item 2 of the attained-top
objective theorem. -/
theorem causalHellingerObjective_argmax_eq_nativelySufficient
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (hattain : CausalFullRevelationAttainable Qs hQ) :
    {π | ∀ σ, causalHellingerObjective Qs hQ σ ≤ causalHellingerObjective Qs hQ π} =
      {π | CausalNativelySufficient Qs π} := by
  ext π
  exact (causalHellingerObjective_maximizer_iff_exactlyIdentifies Qs hQ hattain π).trans
    (causalNativelySufficient_iff_exactlyIdentifies_of_attainable Qs hQ hattain π).symm

end IdExp
