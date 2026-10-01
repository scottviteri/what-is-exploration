import Formal.StrictFinitaryRegularity

/-!
# Compact acquisition trajectories

The full space of valid behavioral policies carries its actual product/subtype
topology. Fixed finite-target deficiencies are continuous even over an arbitrary
nonempty world class. Their joint image in the product cube is compact. No
compactness is asserted for an arbitrary restricted feasible policy family.
-/

namespace IdExp

open Set Topology

noncomputable section

variable {A O Θ ι : Type*} [Fintype A] [Fintype O]

/-- The valid policy tables form a product of compact finite simplices. -/
theorem validCausalPolicy_isCompact :
    IsCompact {π : CausalPolicy A O | IsCausalPolicy π} := by
  change IsCompact {π : CausalHistory A O → A → ℝ | ∀ h, IsDist (π h)}
  exact isCompact_pi_infinite (fun _ => isCompact_stdSimplex ℝ A)

/-- Compactness uses every behavioral policy, including all randomized rows. -/
instance validCausalPolicy_compactSpace : CompactSpace (ValidCausalPolicy A O) :=
  isCompact_iff_compactSpace.mp validCausalPolicy_isCompact

variable [Nonempty A] [Nonempty O] [Nonempty Θ]
    (Qs : Θ → CausalResponse A O) (hQ : ∀ θ, IsCausalResponse (Qs θ))
    {Y : ι → Type*} [∀ j, Fintype (Y j)]
    (T : ∀ j, FiniteExperiment Θ (Y j)) (hT : ∀ j, IsFiniteExperiment (T j))

/-- The complete time-by-target array, retaining which coordinates belong to
one policy. Its target family may be arbitrary; countable native families are
an immediate specialization. -/
def acquisitionTrajectory (π : ValidCausalPolicy A O) : (ℕ × ι) → Set.Icc (0 : ℝ) 1 :=
  fun p => ⟨finiteDeficiency (causalFiniteExperiment π.1 Qs p.1) (T p.2),
    causalPrefixDeficiency_mem_unitInterval Qs hQ p.1 _ (hT p.2) π⟩

/-- The actual deficiency coordinate map into the product cube is continuous. -/
theorem continuous_acquisitionTrajectory :
    Continuous (acquisitionTrajectory Qs hQ T hT) := by
  exact continuous_pi fun p =>
    (continuous_causalPrefixDeficiency Qs hQ p.1 (T p.2) (hT p.2)).subtype_mk _

/-- Proposition `capability-trajectory-compactness`: the joint trajectory image
of the full behavioral-policy space is compact. -/
theorem isCompact_range_acquisitionTrajectory :
    IsCompact (Set.range (acquisitionTrajectory Qs hQ T hT)) :=
  isCompact_range (continuous_acquisitionTrajectory Qs hQ T hT)

include hT in
/-- Direct controlled-prefix-behavior version of coordinate continuity. -/
theorem continuous_causalBehaviorPrefixDeficiency
    (ps : Θ → CausalBehavior A O) (t : ℕ) (j : ι) :
    Continuous (fun π : ValidCausalPolicy A O =>
      finiteDeficiency (causalBehaviorFiniteExperiment π.1 ps t) (T j)) := by
  simpa only [causalBehaviorFiniteExperiment_eq_toResponse] using
    continuous_causalPrefixDeficiency (causalBehaviorResponsePresentation ps)
      (causalBehaviorResponsePresentation_valid ps) t (T j) (hT j)

include hT in
/-- Full-policy compactness and joint image compactness, stated directly for
controlled-prefix behaviors with target-dependent finite signal types. -/
theorem causalBehavior_acquisition_trajectory_compactness
    (ps : Θ → CausalBehavior A O) :
    let Φ := fun (π : ValidCausalPolicy A O) (p : ℕ × ι) =>
      finiteDeficiency (causalBehaviorFiniteExperiment π.1 ps p.1) (T p.2)
    Continuous Φ ∧ IsCompact (Set.range Φ) ∧
      ∀ π p, Φ π p ∈ Set.Icc (0 : ℝ) 1 := by
  dsimp only
  have hc : Continuous (fun (π : ValidCausalPolicy A O) (p : ℕ × ι) =>
      finiteDeficiency (causalBehaviorFiniteExperiment π.1 ps p.1) (T p.2)) :=
    continuous_pi fun p => continuous_causalBehaviorPrefixDeficiency T hT ps p.1 p.2
  refine ⟨hc, isCompact_range hc, ?_⟩
  intro π p
  simpa only [Set.mem_Icc, causalBehaviorFiniteExperiment_eq_toResponse] using
    causalPrefixDeficiency_mem_unitInterval (causalBehaviorResponsePresentation ps)
      (causalBehaviorResponsePresentation_valid ps) p.1 _ (hT p.2) π

end
end IdExp
