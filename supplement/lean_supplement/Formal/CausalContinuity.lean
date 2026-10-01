import Formal.CausalUniversality

/-!
# Compact raw causal worlds and continuous finite experiments

The topology on raw response kernels is the countable product of the usual
finite-dimensional row topologies. Valid kernels form a product of finite
probability simplices, hence a compact metrizable space. Every finite
controlled likelihood and native experiment is continuous in these raw
coordinates. No identification of unreachable-history coordinates is made
here: the behavioral quotient and its native metric are a separate layer.
-/

namespace IdExp

open Finset Set TopologicalSpace

set_option linter.unusedSectionVars false

variable {A O : Type*} [Fintype A] [Fintype O]

/-- Raw causal kernels have the product topology on all response coordinates. -/
instance causalResponse_topologicalSpace : TopologicalSpace (CausalResponse A O) :=
  inferInstanceAs (TopologicalSpace (CausalHistory A O → A → O → ℝ))

/-- There are only countably many finite histories, so the raw product is
metrizable, even though it is not a finite-dimensional space. -/
instance causalResponse_metrizableSpace : MetrizableSpace (CausalResponse A O) :=
  inferInstanceAs (MetrizableSpace (CausalHistory A O → A → O → ℝ))

/-- Valid response laws are a compact subset of the raw product space. -/
theorem validCausalWorld_isCompact :
    IsCompact {Q : CausalResponse A O | IsCausalResponse Q} := by
  change IsCompact {Q : CausalHistory A O → A → O → ℝ | ∀ h a, IsDist (Q h a)}
  have hrow : IsCompact {p : O → ℝ | IsDist p} :=
    isCompact_stdSimplex ℝ O
  have haction : IsCompact {q : A → O → ℝ | ∀ a, IsDist (q a)} :=
    isCompact_pi_infinite (fun _ => hrow)
  exact isCompact_pi_infinite (fun _ => haction)

/-- The inherited raw topology on valid worlds is compact. -/
instance validCausalWorld_compactSpace : CompactSpace (ValidCausalWorld A O) :=
  isCompact_iff_compactSpace.mp validCausalWorld_isCompact

/-- The inherited raw topology on valid worlds is metrizable. -/
instance validCausalWorld_metrizableSpace : MetrizableSpace (ValidCausalWorld A O) :=
  MetrizableSpace.subtype {Q : CausalResponse A O | IsCausalResponse Q}

/-- Evaluation at one response coordinate is continuous in the raw topology. -/
theorem continuous_causalResponse_apply (h : CausalHistory A O) (a : A) (o : O) :
    Continuous (fun Q : CausalResponse A O => Q h a o) := by
  exact (continuous_apply o).comp ((continuous_apply a).comp (continuous_apply h))

/-- Continuation likelihoods are finite products of coordinate functions. -/
theorem continuous_causalTraceProbFrom (π : CausalPolicy A O)
    (pre rest : CausalHistory A O) :
    Continuous (fun Q : CausalResponse A O => causalTraceProbFrom π Q pre rest) := by
  induction rest generalizing pre with
  | nil => exact continuous_const
  | cons ao rest ih =>
      exact (continuous_const.mul (continuous_causalResponse_apply pre ao.1 ao.2)).mul
        (ih (pre ++ [ao]))

theorem continuous_causalTraceProb (π : CausalPolicy A O) (h : CausalHistory A O) :
    Continuous (fun Q : CausalResponse A O => causalTraceProb π Q h) :=
  continuous_causalTraceProbFrom π [] h

/-- The same finite-product argument applies to intervened response likelihoods. -/
theorem continuous_causalResponseProbFrom (pre rest : CausalHistory A O) :
    Continuous (fun Q : CausalResponse A O => causalResponseProbFrom Q pre rest) := by
  induction rest generalizing pre with
  | nil => exact continuous_const
  | cons ao rest ih =>
      exact (continuous_causalResponse_apply pre ao.1 ao.2).mul (ih (pre ++ [ao]))

theorem continuous_causalResponseProb (h : CausalHistory A O) :
    Continuous (fun Q : CausalResponse A O => causalResponseProb Q h) :=
  continuous_causalResponseProbFrom [] h

/-- The entire finite action--observation law varies continuously with the world. -/
theorem continuous_causalFiniteExperiment (π : CausalPolicy A O) (n : ℕ) :
    Continuous (fun Q : CausalResponse A O => causalFiniteExperiment π id n Q) := by
  apply continuous_pi
  intro w
  exact continuous_causalTraceProb π (List.ofFn w)

/-- Native observation laws are continuous, with their actual observation-only
signal representation, not just an abstract finite experiment. -/
theorem continuous_causalPlanObservationExperiment [Nonempty A]
    (n : ℕ) (τ : CausalPlan A O n) :
    Continuous (fun Q : CausalResponse A O => causalPlanObservationExperiment n τ id Q) := by
  apply continuous_pi
  intro o
  simp_rw [causalPlanObservationExperiment_eq_reconstruction]
  exact continuous_causalTraceProb (causalPolicyOfPlan n τ)
    (List.ofFn (causalTraceOfObservations τ o))

/-- Restricting the raw experiment to valid worlds preserves continuity. -/
theorem continuous_validCausalPlanObservationExperiment [Nonempty A]
    (n : ℕ) (τ : CausalPlan A O n) :
    Continuous (fun Q : ValidCausalWorld A O =>
      causalPlanObservationExperiment n τ (fun R : ValidCausalWorld A O => R.val) Q) :=
  (continuous_causalPlanObservationExperiment n τ).comp continuous_subtype_val

/-- The distance associated with any one native intervention is jointly
continuous on raw worlds. Finite maxima can therefore be formed continuously. -/
theorem continuous_causalPlanObservationTV [Nonempty A]
    (n : ℕ) (τ : CausalPlan A O n) :
    Continuous (fun p : CausalResponse A O × CausalResponse A O =>
      finiteTV (causalPlanObservationExperiment n τ id p.1)
        (causalPlanObservationExperiment n τ id p.2)) :=
  continuous_finiteTV.comp
    (((continuous_causalPlanObservationExperiment n τ).comp continuous_fst).prodMk
      ((continuous_causalPlanObservationExperiment n τ).comp continuous_snd))

theorem continuous_validCausalPlanObservationTV [Nonempty A]
    (n : ℕ) (τ : CausalPlan A O n) :
    Continuous (fun p : ValidCausalWorld A O × ValidCausalWorld A O =>
      finiteTV (causalPlanObservationExperiment n τ
        (fun Q : ValidCausalWorld A O => Q.val) p.1)
        (causalPlanObservationExperiment n τ
          (fun Q : ValidCausalWorld A O => Q.val) p.2)) :=
  continuous_finiteTV.comp
    (((continuous_validCausalPlanObservationExperiment n τ).comp continuous_fst).prodMk
      ((continuous_validCausalPlanObservationExperiment n τ).comp continuous_snd))

end IdExp
