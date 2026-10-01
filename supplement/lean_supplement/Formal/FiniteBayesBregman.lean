import Formal.BregmanPotential
import Formal.FiniteBayes

/-!
# Exact Bregman telescoping along finite Bayesian refinements

Refinement means that a deterministic map forgets part of the finer signal.
The coarse experiment is the literal fiber marginal of the finer one. Bayes
rule then proves the weighted posterior barycenter and preservation of the
parent support face, including all null-signal cases. No posterior-martingale
identity is assumed.

The infinite-horizon series theorem takes convergence of the expected terminal
potential as an explicit premise. It proves summability rather than using a
real `tsum` with an unproved convergence convention. `CausalPosteriorLimit`
discharges that premise for actual causal histories; `CausalBregmanTotal`
proves the integrable pathwise total and its strict-convex maximizers.
-/

namespace IdExp

set_option linter.unusedSectionVars false

open Finset Set Filter
open scoped Topology

variable {Θ X Y : Type*} [Fintype Θ] [Fintype X] [Fintype Y] [DecidableEq Y]

/-- Deterministic marginalization of finite experiment rows. -/
def IsFiniteRefinement (E : Θ → X → ℝ) (B : Θ → Y → ℝ) (forget : X → Y) : Prop :=
  ∀ θ y, ∑ x with forget x = y, E θ x = B θ y

theorem finiteBayesMass_refinement (α : Θ → ℝ)
    (E : Θ → X → ℝ) (B : Θ → Y → ℝ) (forget : X → Y)
    (href : IsFiniteRefinement E B forget) (y : Y) :
    ∑ x with forget x = y, finiteBayesMass α E x = finiteBayesMass α B y := by
  classical
  simp only [finiteBayesMass]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro θ _
  rw [← Finset.mul_sum, href θ y]

/-- The unnormalized Bayes martingale identity, valid even on null atoms. -/
theorem finiteBayesPosterior_refinement_barycenter (α : Θ → ℝ)
    (E : Θ → X → ℝ) (B : Θ → Y → ℝ) (forget : X → Y)
    (hα : ∀ θ, 0 ≤ α θ) (hE : ∀ θ x, 0 ≤ E θ x) (hB : ∀ θ y, 0 ≤ B θ y)
    (href : IsFiniteRefinement E B forget) (y : Y) :
    ∑ x with forget x = y, finiteBayesMass α E x • finiteBayesPosterior α E x =
      finiteBayesMass α B y • finiteBayesPosterior α B y := by
  classical
  ext θ
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_comm (finiteBayesMass α E _) _, mul_comm (finiteBayesMass α B _) _]
  simp_rw [finiteBayesMass, finiteBayesPosterior_mul_mass α E hα hE,
    finiteBayesPosterior_mul_mass α B hα hB]
  rw [← Finset.mul_sum, href]

/-- A positive-mass child cannot resurrect a world excluded by its parent.
This supplies exactly the face needed to evaluate a facewise derivative. -/
theorem finiteBayesPosterior_refinement_support (α : Θ → ℝ)
    (E : Θ → X → ℝ) (B : Θ → Y → ℝ) (forget : X → Y)
    (hα : ∀ θ, 0 ≤ α θ) (hE : ∀ θ x, 0 ≤ E θ x) (hB : ∀ θ y, 0 ≤ B θ y)
    (href : IsFiniteRefinement E B forget) (x : X)
    (hx : 0 < finiteBayesMass α E x) :
    finiteBayesPosterior α E x ∈ simplexSupportFace (finiteBayesPosterior α B (forget x)) := by
  classical
  refine ⟨finiteBayesPosterior_mem_simplex α E hα hE x hx.ne', ?_⟩
  intro θ hθ
  have hzero : α θ * B θ (forget x) = 0 := by
    rw [← finiteBayesPosterior_mul_mass α B hα hB (forget x) θ, hθ, zero_mul]
  have hsum : ∑ z with forget z = forget x, α θ * E θ z = 0 := by
    rw [← Finset.mul_sum, href, hzero]
  have hcoord := (Finset.sum_eq_zero_iff_of_nonneg
    (fun z _ => mul_nonneg (hα θ) (hE θ z))).1 hsum x (by simp)
  simp [finiteBayesPosterior, hcoord]

theorem finiteBayesMass_parent_pos (α : Θ → ℝ)
    (E : Θ → X → ℝ) (B : Θ → Y → ℝ) (forget : X → Y)
    (hα : ∀ θ, 0 ≤ α θ) (hE : ∀ θ x, 0 ≤ E θ x)
    (href : IsFiniteRefinement E B forget) (x : X)
    (hx : 0 < finiteBayesMass α E x) :
    0 < finiteBayesMass α B (forget x) := by
  classical
  rw [← finiteBayesMass_refinement α E B forget href]
  exact hx.trans_le (Finset.single_le_sum
    (fun z _ => finiteBayesMass_nonneg α E hα hE z) (by simp))

/-- Expected posterior potential under the actual prior mixture. -/
noncomputable def finiteBayesPotential (F : (Θ → ℝ) → ℝ) (α : Θ → ℝ) (E : Θ → X → ℝ) : ℝ :=
  ∑ x, finiteBayesMass α E x * F (finiteBayesPosterior α E x)

/-- Expected facewise movement from a coarse observation to its refinement. -/
noncomputable def finiteBayesBregmanIncrement (F : (Θ → ℝ) → ℝ)
    (dF : (Θ → ℝ) → (Θ → ℝ) →L[ℝ] ℝ) (α : Θ → ℝ)
    (E : Θ → X → ℝ) (B : Θ → Y → ℝ) (forget : X → Y) : ℝ :=
  ∑ x, finiteBayesMass α E x * facewiseBregman F dF
    (finiteBayesPosterior α E x) (finiteBayesPosterior α B (forget x))

private theorem sum_fibers {Z : Type*} [AddCommMonoid Z]
    (forget : X → Y) (f : X → Z) :
    (∑ y, ∑ x with forget x = y, f x) = ∑ x, f x := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

/-- The exact one-step expected identity, with Bayes' martingale property
proved from the row marginalization and no gradient boundedness premise. -/
theorem finiteBayesBregmanIncrement_eq (F : (Θ → ℝ) → ℝ)
    (dF : (Θ → ℝ) → (Θ → ℝ) →L[ℝ] ℝ) (α : Θ → ℝ)
    (E : Θ → X → ℝ) (B : Θ → Y → ℝ) (forget : X → Y)
    (hα : ∀ θ, 0 ≤ α θ) (hE : ∀ θ x, 0 ≤ E θ x) (hB : ∀ θ y, 0 ≤ B θ y)
    (href : IsFiniteRefinement E B forget) :
    finiteBayesBregmanIncrement F dF α E B forget =
      finiteBayesPotential F α E - finiteBayesPotential F α B := by
  classical
  have hlin (y : Y) : ∑ x with forget x = y, finiteBayesMass α E x *
      dF (finiteBayesPosterior α B y)
        (finiteBayesPosterior α E x - finiteBayesPosterior α B y) = 0 := by
    calc
      _ = dF (finiteBayesPosterior α B y)
          (∑ x with forget x = y, finiteBayesMass α E x •
            (finiteBayesPosterior α E x - finiteBayesPosterior α B y)) := by
        simp only [map_sum, map_smul, smul_eq_mul]
      _ = 0 := by
        simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
        rw [finiteBayesPosterior_refinement_barycenter α E B forget hα hE hB href,
          finiteBayesMass_refinement α E B forget href, sub_self, map_zero]
  have hfiber (y : Y) :
      ∑ x with forget x = y, finiteBayesMass α E x * facewiseBregman F dF
          (finiteBayesPosterior α E x) (finiteBayesPosterior α B (forget x)) =
        (∑ x with forget x = y, finiteBayesMass α E x * F (finiteBayesPosterior α E x)) -
          finiteBayesMass α B y * F (finiteBayesPosterior α B y) := by
    have hrepl : ∀ x ∈ (Finset.univ.filter fun x => forget x = y),
        finiteBayesPosterior α B (forget x) = finiteBayesPosterior α B y :=
      fun x hx => congrArg (finiteBayesPosterior α B) (Finset.mem_filter.mp hx).2
    calc
      _ = ∑ x with forget x = y, finiteBayesMass α E x * facewiseBregman F dF
          (finiteBayesPosterior α E x) (finiteBayesPosterior α B y) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hrepl x hx]
      _ = _ := by
        simp only [facewiseBregman, mul_sub, Finset.sum_sub_distrib]
        rw [hlin, ← Finset.sum_mul, finiteBayesMass_refinement α E B forget href, sub_zero]
  unfold finiteBayesBregmanIncrement finiteBayesPotential
  rw [← sum_fibers forget]
  simp_rw [hfiber]
  rw [Finset.sum_sub_distrib, sum_fibers]

theorem finiteBayesBregmanIncrement_nonneg (F : (Θ → ℝ) → ℝ)
    (hF : ConvexOn ℝ (stdSimplex ℝ Θ) F)
    (dF : (Θ → ℝ) → (Θ → ℝ) →L[ℝ] ℝ) (hdF : HasFacewiseDerivative F dF)
    (α : Θ → ℝ) (E : Θ → X → ℝ) (B : Θ → Y → ℝ) (forget : X → Y)
    (hα : ∀ θ, 0 ≤ α θ) (hE : ∀ θ x, 0 ≤ E θ x) (hB : ∀ θ y, 0 ≤ B θ y)
    (href : IsFiniteRefinement E B forget) :
    0 ≤ finiteBayesBregmanIncrement F dF α E B forget := by
  classical
  refine Finset.sum_nonneg fun x _ => ?_
  by_cases hx : finiteBayesMass α E x = 0
  · simp [hx]
  · have hpos := lt_of_le_of_ne (finiteBayesMass_nonneg α E hα hE x) (Ne.symm hx)
    refine mul_nonneg hpos.le (facewiseBregman_nonneg F hF dF hdF ?_ ?_)
    · exact finiteBayesPosterior_mem_simplex α B hα hB (forget x)
        (finiteBayesMass_parent_pos α E B forget hα hE href x hpos).ne'
    · exact finiteBayesPosterior_refinement_support α E B forget hα hE hB href x hpos

section Chain

variable {S : ℕ → Type*} [∀ n, Fintype (S n)] [∀ n, DecidableEq (S n)]

/-- Finite expected movement telescopes exactly along any finite-signal
Bayesian refinement chain. All horizon and zero-mass cases are included. -/
theorem sum_finiteBayesBregmanIncrement (F : (Θ → ℝ) → ℝ)
    (dF : (Θ → ℝ) → (Θ → ℝ) →L[ℝ] ℝ) (α : Θ → ℝ)
    (E : ∀ n, Θ → S n → ℝ) (forget : ∀ n, S (n + 1) → S n)
    (hα : ∀ θ, 0 ≤ α θ) (hE : ∀ n θ s, 0 ≤ E n θ s)
    (href : ∀ n, IsFiniteRefinement (E (n + 1)) (E n) (forget n)) (N : ℕ) :
    ∑ n ∈ Finset.range N, finiteBayesBregmanIncrement F dF α
        (E (n + 1)) (E n) (forget n) =
      finiteBayesPotential F α (E N) - finiteBayesPotential F α (E 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih,
        finiteBayesBregmanIncrement_eq F dF α (E (N + 1)) (E N) (forget N)
          hα (hE (N + 1)) (hE N) (href N)]
      ring

/-- Complete expected movement is a genuinely convergent series when the
expected posterior potentials converge. Its value is the terminal increase;
the gradients need not have any uniform bound. -/
theorem hasSum_finiteBayesBregmanIncrement (F : (Θ → ℝ) → ℝ)
    (hF : ConvexOn ℝ (stdSimplex ℝ Θ) F)
    (dF : (Θ → ℝ) → (Θ → ℝ) →L[ℝ] ℝ) (hdF : HasFacewiseDerivative F dF)
    (α : Θ → ℝ) (E : ∀ n, Θ → S n → ℝ) (forget : ∀ n, S (n + 1) → S n)
    (hα : ∀ θ, 0 ≤ α θ) (hE : ∀ n θ s, 0 ≤ E n θ s)
    (href : ∀ n, IsFiniteRefinement (E (n + 1)) (E n) (forget n))
    (L : ℝ) (hlim : Tendsto (fun n => finiteBayesPotential F α (E n)) atTop (𝓝 L)) :
    HasSum (fun n => finiteBayesBregmanIncrement F dF α (E (n + 1)) (E n) (forget n))
      (L - finiteBayesPotential F α (E 0)) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (fun n => finiteBayesBregmanIncrement_nonneg F hF dF hdF α
      (E (n + 1)) (E n) (forget n) hα (hE (n + 1)) (hE n) (href n)) _).2
  simpa only [sum_finiteBayesBregmanIncrement F dF α E forget hα hE href] using
    hlim.sub_const (finiteBayesPotential F α (E 0))

end Chain

end IdExp
