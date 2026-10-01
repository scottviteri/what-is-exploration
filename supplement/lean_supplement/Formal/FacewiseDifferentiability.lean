import Formal.BregmanPotential
import Mathlib.Analysis.Convex.Intrinsic

/-!
# Choosing and comparing derivatives on simplex faces

The derivative family used by facewise Bregman movement carries no extra
uniformity or measurability requirement. Its existence is exactly pointwise
differentiability within each current support face. Ambient representatives
need not be unique on a lower-dimensional face, but their values agree on
every displacement along that face, so the Bregman divergence is independent
of the representative.
-/

namespace IdExp

open Set
open scoped Topology

variable {Θ : Type*} [Fintype Θ]

/-- The affine hull retains normalization and all fixed zero coordinates. -/
theorem affineSpan_simplexSupportFace_constraints (p : Θ → ℝ)
    {q : Θ → ℝ} (hq : q ∈ affineSpan ℝ (simplexSupportFace p)) :
    (∑ θ, q θ = 1) ∧ ∀ θ, p θ = 0 → q θ = 0 := by
  refine affineSpan_induction hq (fun r hr => ⟨hr.1.2, hr.2⟩) ?_
  intro c u v w hu hv hw
  constructor
  · change (∑ θ, (c * (u θ - v θ) + w θ)) = 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
      hu.1, hv.1, hw.1]
    ring
  · intro θ hθ
    change c * (u θ - v θ) + w θ = 0
    simp only [hu.2 θ hθ, hv.2 θ hθ, hw.2 θ hθ, sub_self, mul_zero, add_zero]

private theorem isOpen_supportPositive (p : Θ → ℝ) :
    IsOpen {q : Θ → ℝ | ∀ θ, p θ ≠ 0 → 0 < q θ} := by
  have heq : {q : Θ → ℝ | ∀ θ, p θ ≠ 0 → 0 < q θ} =
      ⋂ θ : {θ // p θ ≠ 0}, {q | 0 < q θ.1} := by
    ext q
    simp
  rw [heq]
  exact isOpen_iInter_of_finite fun θ => isOpen_lt continuous_const (continuous_apply θ.1)

/-- Keeping the active coordinates positive gives a relative open neighborhood
inside the closed support face. -/
theorem mem_intrinsicInterior_simplexSupportFace_of_pos (p : Θ → ℝ)
    {q : Θ → ℝ} (hq : q ∈ simplexSupportFace p)
    (hpos : ∀ θ, p θ ≠ 0 → 0 < q θ) :
    q ∈ intrinsicInterior ℝ (simplexSupportFace p) := by
  let y : affineSpan ℝ (simplexSupportFace p) := ⟨q, subset_affineSpan ℝ _ hq⟩
  refine mem_intrinsicInterior.mpr ⟨y, ?_, rfl⟩
  rw [mem_interior_iff_mem_nhds]
  have hopen := (isOpen_supportPositive p).preimage
    (continuous_subtype_val : Continuous
      (fun r : affineSpan ℝ (simplexSupportFace p) => (r : Θ → ℝ)))
  have hy : y ∈ (fun r : affineSpan ℝ (simplexSupportFace p) => (r : Θ → ℝ)) ⁻¹'
      {q : Θ → ℝ | ∀ θ, p θ ≠ 0 → 0 < q θ} := hpos
  apply Filter.mem_of_superset (hopen.mem_nhds hy)
  intro r hr
  have hc := affineSpan_simplexSupportFace_constraints p r.property
  refine ⟨⟨fun θ => ?_, hc.1⟩, hc.2⟩
  by_cases hθ : p θ = 0
  · exact le_of_eq (hc.2 θ hθ).symm
  · exact le_of_lt (hr θ hθ)

/-- Every posterior lies in the relative interior of its own minimal support face. -/
theorem mem_intrinsicInterior_simplexSupportFace {p : Θ → ℝ}
    (hp : p ∈ stdSimplex ℝ Θ) :
    p ∈ intrinsicInterior ℝ (simplexSupportFace p) := by
  exact mem_intrinsicInterior_simplexSupportFace_of_pos p
    (mem_simplexSupportFace_self hp)
    (fun θ hθ => lt_of_le_of_ne (hp.1 θ) (Ne.symm hθ))

/-- At its current posterior, a closed support face and its relative interior
have the same local domain. -/
theorem intrinsicInterior_simplexSupportFace_mem_nhdsWithin {p : Θ → ℝ}
    (hp : p ∈ stdSimplex ℝ Θ) :
    intrinsicInterior ℝ (simplexSupportFace p) ∈ 𝓝[simplexSupportFace p] p := by
  have hpos : ∀ θ, p θ ≠ 0 → 0 < p θ :=
    fun θ hθ => lt_of_le_of_ne (hp.1 θ) (Ne.symm hθ)
  apply Filter.mem_of_superset
    (inter_mem_nhdsWithin (simplexSupportFace p)
      ((isOpen_supportPositive p).mem_nhds hpos))
  intro q hq
  exact mem_intrinsicInterior_simplexSupportFace_of_pos p hq.1 hq.2

/-- A chosen face derivative exists precisely when the potential is
differentiable at every simplex point within its own support face.
The choice imposes no regularity across different faces. -/
theorem exists_hasFacewiseDerivative_iff_differentiableWithinAt
    (F : (Θ → ℝ) → ℝ) :
    (∃ dF : (Θ → ℝ) → (Θ → ℝ) →L[ℝ] ℝ, HasFacewiseDerivative F dF) ↔
      ∀ p ∈ stdSimplex ℝ Θ, DifferentiableWithinAt ℝ F (simplexSupportFace p) p := by
  constructor
  · rintro ⟨dF, hdF⟩ p hp
    exact (hdF p hp).differentiableWithinAt
  · intro h
    exact ⟨fun p => fderivWithin ℝ F (simplexSupportFace p) p,
      fun p hp => (h p hp).hasFDerivWithinAt⟩

/-- Explicit pointwise derivative-existence and one globally chosen family
are equivalent; neither condition requests a measurable derivative map. -/
theorem exists_hasFacewiseDerivative_iff_pointwise
    (F : (Θ → ℝ) → ℝ) :
    (∃ dF : (Θ → ℝ) → (Θ → ℝ) →L[ℝ] ℝ, HasFacewiseDerivative F dF) ↔
      ∀ p ∈ stdSimplex ℝ Θ, ∃ L : (Θ → ℝ) →L[ℝ] ℝ,
        HasFDerivWithinAt F L (simplexSupportFace p) p := by
  exact exists_hasFacewiseDerivative_iff_differentiableWithinAt F

/-- Differentiability on relative interiors, as stated in the paper, supplies
the chosen ambient representatives used by the Bregman theorems. -/
theorem exists_hasFacewiseDerivative_of_differentiableOn_intrinsicInterior
    (F : (Θ → ℝ) → ℝ)
    (hF : ∀ p ∈ stdSimplex ℝ Θ,
      DifferentiableOn ℝ F (intrinsicInterior ℝ (simplexSupportFace p))) :
    ∃ dF : (Θ → ℝ) → (Θ → ℝ) →L[ℝ] ℝ, HasFacewiseDerivative F dF := by
  apply (exists_hasFacewiseDerivative_iff_differentiableWithinAt F).2
  intro p hp
  have hd := (hF p hp p (mem_intrinsicInterior_simplexSupportFace hp)).hasFDerivWithinAt
  exact (hd.mono_of_mem_nhdsWithin
    (intrinsicInterior_simplexSupportFace_mem_nhdsWithin hp)).differentiableWithinAt

/-- Two ambient representatives of face derivatives agree on a valid
posterior displacement, even when the support face has empty ambient interior. -/
theorem hasFacewiseDerivative_apply_sub_eq
    (F : (Θ → ℝ) → ℝ)
    (dF dG : (Θ → ℝ) → (Θ → ℝ) →L[ℝ] ℝ)
    (hdF : HasFacewiseDerivative F dF) (hdG : HasFacewiseDerivative F dG)
    {p q : Θ → ℝ} (hp : p ∈ stdSimplex ℝ Θ) (hq : q ∈ simplexSupportFace p) :
    dF p (q - p) = dG p (q - p) := by
  exact (hdF p hp).unique_on (hdG p hp) (mem_tangentConeAt_of_segment_subset
    ((convex_simplexSupportFace p).segment_subset (mem_simplexSupportFace_self hp) hq))

/-- Facewise Bregman movement does not depend on the chosen ambient
extension of the derivative. -/
theorem facewiseBregman_eq_of_hasFacewiseDerivative
    (F : (Θ → ℝ) → ℝ)
    (dF dG : (Θ → ℝ) → (Θ → ℝ) →L[ℝ] ℝ)
    (hdF : HasFacewiseDerivative F dF) (hdG : HasFacewiseDerivative F dG)
    {p q : Θ → ℝ} (hp : p ∈ stdSimplex ℝ Θ) (hq : q ∈ simplexSupportFace p) :
    facewiseBregman F dF q p = facewiseBregman F dG q p := by
  unfold facewiseBregman
  rw [hasFacewiseDerivative_apply_sub_eq F dF dG hdF hdG hp hq]

end IdExp
