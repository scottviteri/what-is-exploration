import Formal.FiniteProbability

/-!
# Model-independent Shannon entropy geometry

Shannon entropy is continuous, strictly concave on the class simplex, and
zero at its vertices. These facts do not use any environment, posterior
encoding, prior, or recovery assumption.
-/

namespace IdExp

open Finset Set

variable {Θ : Type*} [Fintype Θ]

theorem continuous_ent : Continuous (ent : (Θ → ℝ) → ℝ) := by
  exact continuous_finsetSum _ fun θ _ =>
    Real.continuous_negMulLog.comp (continuous_apply θ)

/-- Distinct probability vectors differ in a coordinate where the strict
concavity of `-x log x` makes the summed Jensen inequality strict. -/
theorem strictConcaveOn_ent_simplex :
    StrictConcaveOn ℝ (stdSimplex ℝ Θ) (ent : (Θ → ℝ) → ℝ) := by
  refine ⟨convex_stdSimplex ℝ Θ, ?_⟩
  intro p hp q hq hpq a b ha hb hab
  have hle (θ : Θ) :
      a * Real.negMulLog (p θ) + b * Real.negMulLog (q θ) ≤
        Real.negMulLog (a * p θ + b * q θ) :=
    Real.concaveOn_negMulLog.2 (hp.1 θ) (hq.1 θ) ha.le hb.le hab
  obtain ⟨θ, hθ⟩ : ∃ θ, p θ ≠ q θ := Function.ne_iff.mp hpq
  have hlt :
      a * Real.negMulLog (p θ) + b * Real.negMulLog (q θ) <
        Real.negMulLog (a * p θ + b * q θ) :=
    Real.strictConcaveOn_negMulLog.2 (hp.1 θ) (hq.1 θ) hθ ha hb hab
  have hsum := Finset.sum_lt_sum (s := Finset.univ) (fun θ _ => hle θ)
    ⟨θ, Finset.mem_univ θ, hlt⟩
  simpa only [ent, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum] using hsum

theorem strictConvexOn_neg_ent_simplex :
    StrictConvexOn ℝ (stdSimplex ℝ Θ) (fun p : Θ → ℝ => -ent p) :=
  strictConcaveOn_ent_simplex.neg

@[simp] theorem ent_simplex_vertex [DecidableEq Θ] (θ : Θ) :
    ent (Pi.single θ (1 : ℝ)) = 0 := by
  classical
  unfold ent
  apply Finset.sum_eq_zero
  intro η _
  by_cases hη : η = θ
  · subst η
    simp
  · simp [hη]

end IdExp
