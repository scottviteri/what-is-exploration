import Formal.FiniteBayesBregman
import Formal.CausalExperiment

/-!
# Facewise Bregman movement on actual causal prefixes

The finite experiment at time `n` is the policy's full action-observation
prefix. Its Bayes posterior is computed from the actual causal row laws, not
postulated as an abstract martingale. Forgetting the newest pair verifies the
finite-refinement hypotheses and yields exact expected telescoping from the
prior at time zero. Null prefixes and null children have zero mixture weight.

The complete-series theorem here still requires convergence of the expected
potential. Identifying that limit with the terminal posterior's expectation,
and the strict-convex maximizer theorem, are separate from this wrapper.
-/

namespace IdExp

set_option linter.unusedSectionVars false

open Finset Filter
open scoped Topology

variable {A O Θ : Type*} [Fintype A] [Fintype O] [Fintype Θ]

/-- Actual causal prefixes form a deterministic Bayesian refinement chain. -/
theorem causalFiniteExperiment_isFiniteRefinement (π : CausalPolicy A O)
    (hπ : IsCausalPolicy π) (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (n : ℕ)
    [DecidableEq A] [DecidableEq O] :
    IsFiniteRefinement (causalFiniteExperiment π Qs (n + 1))
      (causalFiniteExperiment π Qs n) Fin.init := by
  classical
  intro θ y
  have h := congrFun (congrFun (causalFiniteExperiment_prefix π hπ Qs hQ n) θ) y
  simpa only [finiteDecisionLaw, causalPrefixRule, mul_ite, mul_one, mul_zero,
    Finset.sum_filter, eq_comm] using h

theorem causalFiniteBayesPotential_zero (F : (Θ → ℝ) → ℝ) (α : Θ → ℝ)
    (hα : IsDist α) (π : CausalPolicy A O) (Qs : Θ → CausalResponse A O) :
    finiteBayesPotential F α (causalFiniteExperiment π Qs 0) = F α := by
  classical
  simp [finiteBayesPotential, finiteBayesMass,
    causalFiniteExperiment, causalTraceProb, causalTraceProbFrom, hα.2]
  congr 1
  funext θ
  simp [finiteBayesPosterior, causalFiniteExperiment, causalTraceProb,
    causalTraceProbFrom, hα.2]

/-- Exact finite-horizon identity on the actual causal history experiments.
No full-support prior or attained full revelation is needed for conservativity. -/
theorem causalBregman_finite_telescope (F : (Θ → ℝ) → ℝ)
    (dF : (Θ → ℝ) → (Θ → ℝ) →L[ℝ] ℝ) (α : Θ → ℝ) (hα : IsDist α)
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π) (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ)) (N : ℕ) :
    ∑ n ∈ Finset.range N, finiteBayesBregmanIncrement F dF α
        (causalFiniteExperiment π Qs (n + 1)) (causalFiniteExperiment π Qs n) Fin.init =
      finiteBayesPotential F α (causalFiniteExperiment π Qs N) - F α := by
  classical
  rw [sum_finiteBayesBregmanIncrement F dF α
      (causalFiniteExperiment π Qs) (fun _ => Fin.init) hα.1
      (fun n θ x => (causalFiniteExperiment_valid π hπ Qs hQ n θ).1 x)
      (fun n => causalFiniteExperiment_isFiniteRefinement π hπ Qs hQ n),
    causalFiniteBayesPotential_zero F α hα π Qs]

/-- The full expected movement series for an actual causal policy converges
to the limiting expected potential increase, whenever that limit is supplied.
Nonnegativity is discharged using the actual Bayesian support-face theorem. -/
theorem causalBregman_hasSum_of_potential_tendsto (F : (Θ → ℝ) → ℝ)
    (hF : ConvexOn ℝ (stdSimplex ℝ Θ) F)
    (dF : (Θ → ℝ) → (Θ → ℝ) →L[ℝ] ℝ) (hdF : HasFacewiseDerivative F dF)
    (α : Θ → ℝ) (hα : IsDist α)
    (π : CausalPolicy A O) (hπ : IsCausalPolicy π) (Qs : Θ → CausalResponse A O)
    (hQ : ∀ θ, IsCausalResponse (Qs θ))
    (L : ℝ) (hlim : Tendsto
      (fun n => finiteBayesPotential F α (causalFiniteExperiment π Qs n)) atTop (𝓝 L)) :
    HasSum (fun n => finiteBayesBregmanIncrement F dF α
      (causalFiniteExperiment π Qs (n + 1)) (causalFiniteExperiment π Qs n) Fin.init)
      (L - F α) := by
  classical
  simpa only [causalFiniteBayesPotential_zero F α hα π Qs] using
    hasSum_finiteBayesBregmanIncrement F hF dF hdF α
      (causalFiniteExperiment π Qs) (fun _ => Fin.init) hα.1
      (fun n θ x => (causalFiniteExperiment_valid π hπ Qs hQ n θ).1 x)
      (fun n => causalFiniteExperiment_isFiniteRefinement π hπ Qs hQ n) L hlim

end IdExp
