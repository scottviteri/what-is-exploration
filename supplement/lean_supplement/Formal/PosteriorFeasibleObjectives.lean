import Formal.NativeCapabilitySelection
import Formal.PotentialDeficiencyContinuity

/-!
# Feasible posterior objectives and their actual regret

A feasible sufficient policy attains the complete posterior objective's
supremum on any policy family containing it. The family carries no topology
and need not be closed. This identifies a comparator gap with the literal
regret used by the paper's selected-policy sets.

The direct controlled-behavior objective is also identified with the limit of
the actual finite-record posterior gains. No world-identification assumption
is involved in any of these statements.
-/
namespace IdExp
open Set Filter Topology
noncomputable section

section Supremum
variable {P : Type*}

/-- An attained pointwise upper bound is the objective supremum. -/
theorem objectiveSup_eq_of_attained_upper (J : P → ℝ) (p : P)
    (h : ∀ q, J q ≤ J p) : objectiveSup J = J p := by
  have hb : BddAbove (range J) := ⟨J p, by rintro _ ⟨q, rfl⟩; exact h q⟩
  apply le_antisymm
  · exact csSup_le ⟨J p, mem_range_self p⟩ (by rintro _ ⟨q, rfl⟩; exact h q)
  · exact le_csSup hb (mem_range_self p)

end Supremum

section Prior
variable {Θ : Type*} [Fintype Θ] [Nonempty Θ]

/-- The actual minimum prior mass on a finite nonempty world class. -/
def priorMinimum (α : Θ → ℝ) : ℝ := Finset.univ.inf' Finset.univ_nonempty α

theorem priorMinimum_le (α : Θ → ℝ) (θ : Θ) : priorMinimum α ≤ α θ :=
  Finset.inf'_le _ (Finset.mem_univ θ)

theorem priorMinimum_pos (α : Θ → ℝ) (hfs : FullSupport α) : 0 < priorMinimum α := by
  exact (Finset.lt_inf'_iff _).mpr (fun θ _ => hfs θ)

end Prior

section Causal
universe u v
variable {A O Θ : Type u} {P : Type v} [Fintype A] [Fintype O]
  [MeasurableSpace A] [MeasurableSpace O]
  [MeasurableSingletonClass A] [MeasurableSingletonClass O]
  [Nonempty A] [Nonempty O] [Fintype Θ] [Nonempty Θ]
  [DecidableEq Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ]

theorem causalPotentialObjective_feasibleSup_eq
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (Φ : (Θ → ℝ) → ℝ) (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ))
    (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (F : P → ValidCausalPolicy A O)
    (pstar : P) (hstar : CausalNativelySufficient Qs (F pstar)) :
    objectiveSup (fun p => causalPotentialObjective Φ α Qs hQ (F p)) =
      causalPotentialObjective Φ α Qs hQ (F pstar) := by
  apply objectiveSup_eq_of_attained_upper
  exact fun p => causalPotentialObjective_le_of_nativelySufficient
    Qs hQ Φ hΦc hΦ α hα hstar (F p)

/-- The complete posterior gain on the semantic controlled-prefix behavior. -/
def causalBehaviorPotentialObjective (Φ : (Θ → ℝ) → ℝ) (α : Θ → ℝ)
    (ps : Θ → CausalBehavior A O) (π : ValidCausalPolicy A O) : ℝ :=
  causalPotentialObjective Φ α (causalBehaviorResponsePresentation ps)
    (causalBehaviorResponsePresentation_valid ps) π

/-- This objective is the literal limit of finite-record expected potential
gains. Continuity on the finite simplex suffices for this identification. -/
theorem tendsto_causalBehaviorPotentialGain
    (ps : Θ → CausalBehavior A O) (Φ : (Θ → ℝ) → ℝ)
    (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ)) (α : Θ → ℝ) (hα : IsDist α)
    (π : ValidCausalPolicy A O) :
    Tendsto (fun t => finiteBayesPotential Φ α
      (causalBehaviorFiniteExperiment π.1 ps t) - Φ α) atTop
      (𝓝 (causalBehaviorPotentialObjective Φ α ps π)) := by
  simpa only [causalBehaviorFiniteExperiment_eq_toResponse,
    causalBehaviorPotentialObjective, causalPotentialObjective, causalTerminalPotential] using
    (tendsto_causalBayesPotential α hα (causalBehaviorResponsePresentation ps)
      (causalBehaviorResponsePresentation_valid ps) π Φ hΦc).sub_const (Φ α)

theorem causalBehaviorPotentialObjective_feasibleSup_eq
    (ps : Θ → CausalBehavior A O) (Φ : (Θ → ℝ) → ℝ)
    (hΦc : ContinuousOn Φ (stdSimplex ℝ Θ)) (hΦ : ConvexOn ℝ (stdSimplex ℝ Θ) Φ)
    (α : Θ → ℝ) (hα : IsDist α) (F : P → ValidCausalPolicy A O)
    (pstar : P) (hstar : CausalBehaviorNativelySufficient ps (F pstar)) :
    objectiveSup (fun p => causalBehaviorPotentialObjective Φ α ps (F p)) =
      causalBehaviorPotentialObjective Φ α ps (F pstar) := by
  exact causalPotentialObjective_feasibleSup_eq _ _ Φ hΦc hΦ α hα F pstar
    ((causalBehaviorNativelySufficient_iff_raw ps (F pstar)).mp hstar)

end Causal
end
end IdExp
