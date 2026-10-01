import Formal.CausalBregmanTotal

/-! # Squared posterior movement as a literal Bregman objective -/
namespace IdExp
open Finset Set
set_option linter.unusedSectionVars false
variable {Θ : Type*} [Fintype Θ]

noncomputable def posteriorQuadraticPotential (p : Θ → ℝ) : ℝ := ∑ θ, (p θ)^2

noncomputable def posteriorQuadraticDerivative (p : Θ → ℝ) : (Θ → ℝ) →L[ℝ] ℝ :=
  ∑ θ, (2 * p θ) • ContinuousLinearMap.proj θ

theorem continuous_posteriorQuadraticPotential :
    Continuous (posteriorQuadraticPotential : (Θ → ℝ) → ℝ) := by
  unfold posteriorQuadraticPotential
  fun_prop

theorem convexOn_posteriorQuadraticPotential :
    ConvexOn ℝ (stdSimplex ℝ Θ) (posteriorQuadraticPotential : (Θ → ℝ) → ℝ) := by
  refine ⟨convex_stdSimplex ℝ Θ, ?_⟩
  intro p hp q hq a b ha hb hab
  simp only [posteriorQuadraticPotential, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro θ _
  have he : a * (p θ)^2 + b * (q θ)^2 - (a * p θ + b * q θ)^2 =
      a * b * (p θ - q θ)^2 := by
    have hb' : b = 1 - a := by linarith
    rw [hb']; ring
  have hn := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (p θ - q θ))
  linarith

theorem hasFacewiseDerivative_posteriorQuadraticPotential :
    HasFacewiseDerivative (posteriorQuadraticPotential : (Θ → ℝ) → ℝ)
      posteriorQuadraticDerivative := by
  intro p hp
  apply HasFDerivAt.hasFDerivWithinAt
  have h := HasFDerivAt.sum (u := Finset.univ) (fun θ _ =>
    ((ContinuousLinearMap.proj θ : (Θ → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := p)).mul
      ((ContinuousLinearMap.proj θ : (Θ → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := p)))
  convert! h using 1
  · funext q
    simp [posteriorQuadraticPotential, pow_two]
  · ext q
    simp only [posteriorQuadraticDerivative, _root_.sum_apply,
      smul_apply, add_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro θ _
    ring

/-- The actual facewise Bregman reward is squared Euclidean posterior change. -/
theorem facewiseBregman_posteriorQuadratic (p q : Θ → ℝ) :
    facewiseBregman posteriorQuadraticPotential posteriorQuadraticDerivative q p =
      ∑ θ, (q θ - p θ)^2 := by
  simp only [facewiseBregman, posteriorQuadraticPotential, posteriorQuadraticDerivative,
    _root_.sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, Pi.sub_apply, smul_eq_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro θ _
  ring

@[simp] theorem posteriorQuadraticPotential_vertex [DecidableEq Θ] (θ : Θ) :
    posteriorQuadraticPotential (Pi.single θ (1 : ℝ)) = 1 := by
  classical
  simp [posteriorQuadraticPotential, Pi.single_apply, ite_pow]
end IdExp
