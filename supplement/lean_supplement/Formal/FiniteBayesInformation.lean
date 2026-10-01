import Formal.EntropyGeometry
import Formal.FiniteBayesBregman

/-!
# Information increases under finite Bayesian refinement

This is an exact Jensen argument for literal finite experiment rows.
Null children have zero mixture weight; they are replaced by the parent
posterior only inside the proof so Jensen uses points of the simplex.
No full-support prior, derivative, or asymptotic assumption is needed.
-/

namespace IdExp

open Finset Set

variable {Θ X Y : Type*} [Fintype Θ] [Fintype X] [Fintype Y] [DecidableEq Y]

/-- A convex posterior potential increases when a deterministic map forgets
part of a finer finite signal. All zero-mixture-mass atoms are included. -/
theorem finiteBayesPotential_mono_refinement (F : (Θ → ℝ) → ℝ)
    (hF : ConvexOn ℝ (stdSimplex ℝ Θ) F)
    (α : Θ → ℝ) (E : Θ → X → ℝ) (B : Θ → Y → ℝ) (forget : X → Y)
    (hα : ∀ θ, 0 ≤ α θ) (hE : ∀ θ x, 0 ≤ E θ x) (hB : ∀ θ y, 0 ≤ B θ y)
    (href : IsFiniteRefinement E B forget) :
    finiteBayesPotential F α B ≤ finiteBayesPotential F α E := by
  classical
  have hfiber (y : Y) :
      finiteBayesMass α B y * F (finiteBayesPosterior α B y) ≤
        ∑ x with forget x = y, finiteBayesMass α E x * F (finiteBayesPosterior α E x) := by
    by_cases hm0 : finiteBayesMass α B y = 0
    · have hchild : ∀ x ∈ (Finset.univ.filter fun x => forget x = y),
          finiteBayesMass α E x = 0 := by
        apply (Finset.sum_eq_zero_iff_of_nonneg
          (fun x _ => finiteBayesMass_nonneg α E hα hE x)).1
        exact (finiteBayesMass_refinement α E B forget href y).trans hm0
      rw [hm0, zero_mul]
      apply le_of_eq
      exact (Finset.sum_eq_zero fun x hx => by rw [hchild x hx, zero_mul]).symm
    · have hmpos : 0 < finiteBayesMass α B y :=
        lt_of_le_of_ne (finiteBayesMass_nonneg α B hα hB y) (Ne.symm hm0)
      let q : X → Θ → ℝ := fun x =>
        if finiteBayesMass α E x = 0 then finiteBayesPosterior α B y
          else finiteBayesPosterior α E x
      have hq (x : X) : q x ∈ stdSimplex ℝ Θ := by
        dsimp [q]
        split_ifs with hx
        · exact finiteBayesPosterior_mem_simplex α B hα hB y hm0
        · exact finiteBayesPosterior_mem_simplex α E hα hE x hx
      have hsum : ∑ x with forget x = y,
          finiteBayesMass α E x / finiteBayesMass α B y = 1 := by
        rw [← Finset.sum_div, finiteBayesMass_refinement α E B forget href y, div_self hm0]
      have hvector : (∑ x with forget x = y,
          (finiteBayesMass α E x / finiteBayesMass α B y) • q x) =
            finiteBayesPosterior α B y := by
        calc _ = (finiteBayesMass α B y)⁻¹ •
            (∑ x with forget x = y, finiteBayesMass α E x • finiteBayesPosterior α E x) := by
              rw [Finset.smul_sum]
              apply Finset.sum_congr rfl
              intro x _
              by_cases hx : finiteBayesMass α E x = 0
              · simp [q, hx]
              · simp [q, hx, div_eq_mul_inv, smul_smul, mul_comm]
          _ = finiteBayesPosterior α B y := by
              rw [finiteBayesPosterior_refinement_barycenter α E B forget hα hE hB href y,
                smul_smul, inv_mul_cancel₀ hm0, one_smul]
      have hJ := hF.map_sum_le
        (t := Finset.univ.filter fun x => forget x = y)
        (w := fun x => finiteBayesMass α E x / finiteBayesMass α B y) (p := q)
        (fun x _ => div_nonneg (finiteBayesMass_nonneg α E hα hE x) hmpos.le) hsum
        (fun x _ => hq x)
      rw [hvector] at hJ
      have hright : (∑ x with forget x = y,
          (finiteBayesMass α E x / finiteBayesMass α B y) • F (q x)) =
            (∑ x with forget x = y,
              finiteBayesMass α E x * F (finiteBayesPosterior α E x)) /
                finiteBayesMass α B y := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : finiteBayesMass α E x = 0
        · simp [hx]
        · simp only [q, if_neg hx, smul_eq_mul]
          ring
      rw [hright] at hJ
      simpa only [mul_comm] using (le_div_iff₀ hmpos).1 hJ
  unfold finiteBayesPotential
  calc _ ≤ ∑ y, ∑ x with forget x = y,
      finiteBayesMass α E x * F (finiteBayesPosterior α E x) :=
        Finset.sum_le_sum fun y _ => hfiber y
    _ = _ := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      simp

/-- Entropy-form mutual information for a finite experiment. -/
noncomputable def finiteBayesInformation (α : Θ → ℝ) (E : Θ → X → ℝ) : ℝ :=
  ent α - finiteBayesPotential ent α E

/-- Acquiring a finer finite signal cannot decrease its mutual information. -/
theorem finiteBayesInformation_mono_refinement
    (α : Θ → ℝ) (E : Θ → X → ℝ) (B : Θ → Y → ℝ) (forget : X → Y)
    (hα : ∀ θ, 0 ≤ α θ) (hE : ∀ θ x, 0 ≤ E θ x) (hB : ∀ θ y, 0 ≤ B θ y)
    (href : IsFiniteRefinement E B forget) :
    finiteBayesInformation α B ≤ finiteBayesInformation α E := by
  have h := finiteBayesPotential_mono_refinement (fun p => -ent p)
    strictConvexOn_neg_ent_simplex.convexOn α E B forget hα hE hB href
  simp only [finiteBayesPotential, mul_neg, Finset.sum_neg_distrib] at h
  exact sub_le_sub_left (neg_le_neg_iff.1 h) _

end IdExp
