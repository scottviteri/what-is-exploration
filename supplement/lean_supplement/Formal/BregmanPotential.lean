import Formal.FiniteBlackwell

/-!
# Facewise Bregman potentials on a finite simplex

This file isolates the analytic and finite-martingale ingredients of the
paper's posterior-movement objective. A derivative is required only within
the current support face. It is not required to extend continuously to the
boundary, nor to be uniformly bounded as the current posterior varies.

The finite averaging identity is algebraic and therefore holds for any
chosen linear functional at each parent posterior. Convexity and a genuine
face derivative separately establish nonnegativity of each realized movement.
The final causal posterior-limit and objective-maximizer assembly lives in
`CausalPosteriorLimit`, `CausalPotentialObjective`, and `CausalBregmanTotal`.
-/

namespace IdExp

set_option linter.unusedSectionVars false

open Finset Set Filter
open scoped Topology

variable {Θ X : Type*} [Fintype Θ] [Fintype X]

/-- The closed support face of a probability vector. -/
def simplexSupportFace (p : Θ → ℝ) : Set (Θ → ℝ) :=
  {q | q ∈ stdSimplex ℝ Θ ∧ ∀ θ, p θ = 0 → q θ = 0}

theorem mem_simplexSupportFace_self {p : Θ → ℝ}
    (hp : p ∈ stdSimplex ℝ Θ) : p ∈ simplexSupportFace p :=
  ⟨hp, fun _ h => h⟩

theorem convex_simplexSupportFace (p : Θ → ℝ) :
    Convex ℝ (simplexSupportFace p) := by
  intro q hq r hr a b ha hb hab
  refine ⟨(convex_stdSimplex ℝ Θ) hq.1 hr.1 ha hb hab, ?_⟩
  intro θ hθ
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hq.2 θ hθ, hr.2 θ hθ,
    mul_zero, add_zero]

/-- An ambient linear representative of the derivative on each support face.
Only the values on tangent directions in that face matter. This formulation
does not ask for differentiability across two different faces. -/
def HasFacewiseDerivative (F : (Θ → ℝ) → ℝ)
    (dF : (Θ → ℝ) → (Θ → ℝ) →L[ℝ] ℝ) : Prop :=
  ∀ p ∈ stdSimplex ℝ Θ, HasFDerivWithinAt F (dF p) (simplexSupportFace p) p

/-- Bregman movement from the parent `p` to its refinement `q`. -/
def facewiseBregman (F : (Θ → ℝ) → ℝ)
    (dF : (Θ → ℝ) → (Θ → ℝ) →L[ℝ] ℝ) (q p : Θ → ℝ) : ℝ :=
  F q - F p - dF p (q - p)

@[simp] theorem facewiseBregman_self (F : (Θ → ℝ) → ℝ)
    (dF : (Θ → ℝ) → (Θ → ℝ) →L[ℝ] ℝ) (p : Θ → ℝ) :
    facewiseBregman F dF p p = 0 := by
  simp [facewiseBregman]

/-- A face derivative of a convex potential supports that potential everywhere
on the same closed face, including points on its smaller boundary faces. -/
theorem facewiseBregman_nonneg (F : (Θ → ℝ) → ℝ)
    (hF : ConvexOn ℝ (stdSimplex ℝ Θ) F)
    (dF : (Θ → ℝ) → (Θ → ℝ) →L[ℝ] ℝ) (hdF : HasFacewiseDerivative F dF)
    {p q : Θ → ℝ} (hp : p ∈ stdSimplex ℝ Θ) (hq : q ∈ simplexSupportFace p) :
    0 ≤ facewiseBregman F dF q p := by
  let line : ℝ → (Θ → ℝ) := fun t => p + t • (q - p)
  have hline (t : ℝ) : line t = (1 - t) • p + t • q := by
    ext θ
    simp only [line, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hmem : MapsTo line (Icc 0 1) (simplexSupportFace p) := by
    intro t ht
    rw [hline]
    exact convex_simplexSupportFace p (mem_simplexSupportFace_self hp) hq
      (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hlineDeriv : HasDerivAt line (q - p) 0 := by
    simpa [line] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (q - p)).const_add p
  have hd : HasDerivWithinAt (F ∘ line) (dF p (q - p)) (Icc 0 1) 0 := by
    have hbase : HasFDerivWithinAt F (dF p) (simplexSupportFace p) (line 0) := by
      simpa [line] using hdF p hp
    exact hbase.comp_hasDerivWithinAt 0 hlineDeriv.hasDerivWithinAt hmem
  have hc : ConvexOn ℝ (Icc 0 1) (F ∘ line) := by
    refine ⟨convex_Icc _ _, ?_⟩
    intro a ha b hb c d hc hd hcd
    have hm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) := (hmem ht).1
    have heq : line (c * a + d * b) = c • line a + d • line b := by
      ext θ
      simp only [line, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      calc
        p θ + (c * a + d * b) * (q θ - p θ) =
            (c + d) * p θ + (c * a + d * b) * (q θ - p θ) := by rw [hcd, one_mul]
        _ = c * (p θ + a * (q θ - p θ)) + d * (p θ + b * (q θ - p θ)) := by ring
    simpa only [Function.comp_apply, smul_eq_mul, heq] using
      hF.2 (hm a ha) (hm b hb) hc hd hcd
  have hsupport := hc.le_slope_of_hasDerivWithinAt
    (show (0 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num) (by norm_num) hd
  have hline0 : line 0 = p := by simp [line]
  have hline1 : line 1 = q := by simp [line]
  simp only [slope_def_field, Function.comp_apply, hline0, hline1,
    sub_zero, div_one] at hsupport
  exact sub_nonneg.mpr hsupport

/-- The derivative contribution has zero expectation whenever the children
average to their parent. No bound on the chosen derivative is needed. -/
theorem sum_linear_posterior_movement_eq_zero (w : X → ℝ) (q : X → Θ → ℝ)
    (p : Θ → ℝ) (L : (Θ → ℝ) →L[ℝ] ℝ) (hw : ∑ x, w x = 1)
    (hbary : ∑ x, w x • q x = p) :
    ∑ x, w x * L (q x - p) = 0 := by
  calc
    ∑ x, w x * L (q x - p) = L (∑ x, w x • (q x - p)) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = L ((∑ x, w x • q x) - (∑ x, w x) • p) := by
      rw [Finset.sum_smul]
      simp only [smul_sub, Finset.sum_sub_distrib]
    _ = 0 := by rw [hbary, hw, one_smul, sub_self, map_zero]

/-- Exact expected Bregman movement for one finite refinement. The result
continues to hold at a parent on a proper support face. -/
theorem sum_facewiseBregman_eq (F : (Θ → ℝ) → ℝ)
    (dF : (Θ → ℝ) → (Θ → ℝ) →L[ℝ] ℝ)
    (w : X → ℝ) (q : X → Θ → ℝ) (p : Θ → ℝ)
    (hw : ∑ x, w x = 1) (hbary : ∑ x, w x • q x = p) :
    ∑ x, w x * facewiseBregman F dF (q x) p =
      (∑ x, w x * F (q x)) - F p := by
  simp only [facewiseBregman, mul_sub, Finset.sum_sub_distrib]
  rw [sum_linear_posterior_movement_eq_zero w q p (dF p) hw hbary,
    ← Finset.sum_mul, hw, one_mul, sub_zero]

variable [DecidableEq Θ]

/-- The full-revelation value of a posterior, minus its current potential.
For a convex potential this is its Jensen gap against the simplex vertices. -/
noncomputable def posteriorPotentialGap (F : (Θ → ℝ) → ℝ) (p : Θ → ℝ) : ℝ :=
  (∑ θ, p θ * F (Pi.single θ 1)) - F p

theorem sum_smul_simplex_vertices (p : Θ → ℝ) :
    (∑ θ, p θ • Pi.single θ (1 : ℝ)) = p := by
  classical
  ext θ
  simp [Finset.sum_apply, Pi.single_apply]

theorem posteriorPotentialGap_nonneg (F : (Θ → ℝ) → ℝ)
    (hF : ConvexOn ℝ (stdSimplex ℝ Θ) F) {p : Θ → ℝ}
    (hp : p ∈ stdSimplex ℝ Θ) : 0 ≤ posteriorPotentialGap F p := by
  classical
  have hJ := hF.map_sum_le (t := Finset.univ) (w := p)
    (p := fun θ => Pi.single θ (1 : ℝ)) (fun θ _ => hp.1 θ) hp.2
    (fun θ _ => single_mem_stdSimplex ℝ θ)
  rw [sum_smul_simplex_vertices] at hJ
  exact sub_nonneg.mpr hJ

/-- Strict convexity makes the full-revelation Jensen gap vanish precisely at
a vertex, including boundary posteriors with some zero coordinates. -/
theorem posteriorPotentialGap_eq_zero_iff (F : (Θ → ℝ) → ℝ)
    (hF : StrictConvexOn ℝ (stdSimplex ℝ Θ) F) {p : Θ → ℝ}
    (hp : p ∈ stdSimplex ℝ Θ) :
    posteriorPotentialGap F p = 0 ↔ ∃ θ, p = Pi.single θ 1 := by
  classical
  constructor
  · intro hgap
    have hJ := (hF.map_sum_eq_iff' (t := Finset.univ) (w := p)
      (p := fun θ => Pi.single θ (1 : ℝ)) (fun θ _ => hp.1 θ) hp.2
      (fun θ _ => single_mem_stdSimplex ℝ θ)).1
    have heq : F (∑ θ, p θ • Pi.single θ (1 : ℝ)) =
        ∑ θ, p θ • F (Pi.single θ (1 : ℝ)) := by
      rw [sum_smul_simplex_vertices]
      exact (sub_eq_zero.mp hgap).symm
    have hsome : ∃ θ, p θ ≠ 0 := by
      by_contra! hn
      have hsum : ∑ θ, p θ = 0 := Finset.sum_eq_zero fun θ _ => hn θ
      linarith [hp.2]
    obtain ⟨θ, hθ⟩ := hsome
    exact ⟨θ, by simpa only [sum_smul_simplex_vertices] using (hJ heq θ (Finset.mem_univ θ) hθ).symm⟩
  · rintro ⟨θ, rfl⟩
    simp [posteriorPotentialGap, Pi.single_apply]

end IdExp
