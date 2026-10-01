import Formal.CausalBehavior
import Formal.CausalContinuity

/-!
# Topology of controlled-prefix behaviors

`CausalBehavior` is the direct controlled-prefix-mass presentation of a
causal world.  This file equips it with the topology inherited from the
coordinate map

`p \mapsto p.mass : CausalHistory A O \to \mathbb R`,

proves directly that its image is a compact closed system of linear
consistency equations inside the unit cube, and identifies it
homeomorphically with the existing behavioral quotient `CausalWorld`.

The inverse map from behaviors to response kernels divides child masses by
their parent mass and is not visibly continuous at null histories.  The
homeomorphism proof deliberately avoids trying to prove continuity of that
raw representative choice: the forward quotient map is a continuous
bijection from a compact space to a Hausdorff space, hence a homeomorphism.
-/

namespace IdExp

open Finset Set TopologicalSpace

set_option linter.unusedSectionVars false

variable {A O : Type*} [Fintype A] [Fintype O]

/-! ## Coordinate topology and metrizability -/

/-- Direct behaviors carry the subspace topology induced by all controlled
prefix-mass coordinates. -/
instance causalBehavior_topologicalSpace : TopologicalSpace (CausalBehavior A O) :=
  TopologicalSpace.induced CausalBehavior.mass inferInstance

/-- The mass field completely determines a direct behavior. -/
theorem CausalBehavior.mass_injective :
    Function.Injective (CausalBehavior.mass : CausalBehavior A O → CausalHistory A O → ℝ) := by
  intro p q hpq
  exact CausalBehavior.ext hpq

/-- The mass field realizes direct behaviors as a topological subspace of
the product of real coordinate lines. -/
theorem causalBehavior_mass_isEmbedding :
    Topology.IsEmbedding
      (CausalBehavior.mass : CausalBehavior A O → CausalHistory A O → ℝ) :=
  CausalBehavior.mass_injective.isEmbedding_induced

/-- Since the history set is countable for finite alphabets, the direct
behavior space is metrizable in its coordinate topology. -/
instance causalBehavior_metrizableSpace : MetrizableSpace (CausalBehavior A O) :=
  causalBehavior_mass_isEmbedding.metrizableSpace

/-! ## Direct compactness as a closed subset of the unit cube -/

/-- Raw controlled-prefix mass tables before imposing probability and
consistency constraints. -/
abbrev CausalBehaviorMassTable (A O : Type*) := CausalHistory A O → ℝ

/-- The root and marginalization equations defining consistent controlled
prefix masses. -/
def causalBehaviorLinearSet : Set (CausalBehaviorMassTable A O) :=
  {p | p [] = 1} ∩
    ⋂ (h : CausalHistory A O), ⋂ (a : A),
      {p | (∑ o, p (h ++ [(a, o)])) = p h}

/-- The concrete image of direct behaviors: unit-interval coordinates
satisfying the root and controlled marginalization equations. -/
def causalBehaviorMassSet : Set (CausalBehaviorMassTable A O) :=
  {p | ∀ h, p h ∈ Set.Icc (0 : ℝ) 1} ∩ causalBehaviorLinearSet

/-- The infinite system of root and marginalization equations is closed in
the product topology. -/
theorem isClosed_causalBehaviorLinearSet :
    IsClosed (causalBehaviorLinearSet (A := A) (O := O)) := by
  unfold causalBehaviorLinearSet
  apply (isClosed_eq (continuous_apply []) continuous_const).inter
  apply isClosed_iInter
  intro h
  apply isClosed_iInter
  intro a
  apply isClosed_eq
  · apply continuous_finsetSum
    intro o _
    exact continuous_apply _
  · exact continuous_apply _

/-- The feasible controlled-prefix mass tables form a compact subset of the
countable real product: a closed linear slice of the compact unit cube. -/
theorem isCompact_causalBehaviorMassSet :
    IsCompact (causalBehaviorMassSet (A := A) (O := O)) := by
  unfold causalBehaviorMassSet
  exact (isCompact_pi_infinite (fun _ => isCompact_Icc)).inter_right
    isClosed_causalBehaviorLinearSet

/-- The range of the mass embedding is exactly the feasible compact set.
The upper coordinate bound is derived from consistency, not added to the
mathematical notion of behavior. -/
theorem CausalBehavior.range_mass :
    Set.range (CausalBehavior.mass : CausalBehavior A O → CausalBehaviorMassTable A O) =
      causalBehaviorMassSet := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨fun h => q.mass_mem_unitInterval h, q.root, ?_⟩
    simp only [Set.mem_iInter]
    exact q.consistent
  · intro hp
    rcases hp with ⟨hbound, hroot, hconsistent⟩
    refine ⟨{
      mass := p
      root := hroot
      nonneg := fun h => (hbound h).1
      consistent := ?_
    }, rfl⟩
    simpa only [Set.mem_iInter, Set.mem_ofPred_eq] using hconsistent

/-- Direct controlled-prefix behaviors are compact without passing through
the response-kernel quotient. -/
theorem isCompact_univ_causalBehavior :
    IsCompact (Set.univ : Set (CausalBehavior A O)) := by
  rw [causalBehavior_mass_isEmbedding.isCompact_iff]
  simpa only [Set.image_univ, CausalBehavior.range_mass] using
    (isCompact_causalBehaviorMassSet (A := A) (O := O))

instance causalBehavior_compactSpace : CompactSpace (CausalBehavior A O) :=
  isCompact_univ_iff.mp isCompact_univ_causalBehavior

/-! ## Continuity of the semantic quotient map -/

/-- Taking all controlled-prefix probabilities is continuous from valid raw
response kernels to the direct behavior space. -/
theorem continuous_validCausalWorld_toBehavior :
    Continuous (fun Q : ValidCausalWorld A O =>
      CausalBehavior.ofResponse Q.val Q.property) := by
  rw [causalBehavior_mass_isEmbedding.isInducing.continuous_iff]
  change Continuous (fun Q : ValidCausalWorld A O =>
    fun h => causalResponseProb Q.val h)
  apply continuous_pi
  intro h
  exact (continuous_causalResponseProb h).comp continuous_subtype_val

/-- The quotient-to-behavior normal-form map is continuous for the canonical
quotient topology. -/
theorem continuous_causalWorldToBehavior :
    Continuous (causalWorldToBehavior : CausalWorld A O → CausalBehavior A O) := by
  unfold causalWorldToBehavior
  exact continuous_validCausalWorld_toBehavior.quotient_lift
    (fun Q Q' hQQ' =>
      (CausalBehavior.ofResponse_eq_iff_causalBehEq Q.property Q'.property).2 hQQ')

/-! ## Homeomorphism with the existing behavioral quotient -/

/-- The concrete behavior normal form is a homeomorphism from the existing
controlled-trace quotient.  Compact-to-Hausdorff uniqueness supplies inverse
continuity, so no continuity is claimed for the arbitrary null-row filler as
a raw response kernel. -/
theorem isHomeomorph_causalWorldToBehavior [Nonempty O] :
    IsHomeomorph (causalWorldToBehavior : CausalWorld A O → CausalBehavior A O) := by
  rw [isHomeomorph_iff_continuous_bijective]
  exact ⟨continuous_causalWorldToBehavior,
    (causalWorldEquivBehavior (A := A) (O := O)).bijective⟩

/-- Bundled form of the equivalence, retaining the explicit algebraic inverse
`behaviorToCausalWorld`. -/
noncomputable def causalWorldHomeomorphBehavior [Nonempty O] :
    CausalWorld A O ≃ₜ CausalBehavior A O where
  toEquiv := causalWorldEquivBehavior
  continuous_toFun := continuous_causalWorldToBehavior
  continuous_invFun :=
    (causalWorldEquivBehavior (A := A) (O := O)).continuous_symm_iff.mpr
      (isHomeomorph_causalWorldToBehavior (A := A) (O := O)).isOpenMap

@[simp]
theorem causalWorldHomeomorphBehavior_apply [Nonempty O] (q : CausalWorld A O) :
    causalWorldHomeomorphBehavior q = causalWorldToBehavior q :=
  rfl

@[simp]
theorem causalWorldHomeomorphBehavior_symm_apply [Nonempty O] (p : CausalBehavior A O) :
    (causalWorldHomeomorphBehavior (A := A) (O := O)).symm p =
      behaviorToCausalWorld p :=
  rfl

end IdExp
