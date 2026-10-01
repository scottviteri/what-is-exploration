import Formal.CausalBehaviorExperiment
import Formal.CausalBehaviorTopology
import Formal.CausalGeometry

/-!
# Native geometry on direct controlled-prefix behaviors

This supporting finite-alphabet module identifies the native observation laws
and native metric written directly on `CausalBehavior` with the already checked
laws and metric on the quotient `CausalWorld`.  The pulled-back metric is
explicitly compatible with the coordinate topology from
`CausalBehaviorTopology`.

This is a carrier-compatibility result, not an exploration theorem.  In
particular it does not extend the scalar-prefix representation to atomless or
general standard-Borel observations.
-/

namespace IdExp

open Finset TopologicalSpace

set_option linter.unusedSectionVars false

variable {A O : Type*} [Fintype A] [Fintype O]
  [Nonempty A] [Nonempty O] [DecidableEq A] [DecidableEq O]

/-- Direct plan evaluation is exactly the native law on the corresponding
quotient world. -/
theorem causalBehaviorPlanLaw_eq_nativeWorldObservationLaw
    (n : ℕ) (tau : CausalPlan A O n) (p : CausalBehavior A O) :
    causalBehaviorPlanLaw n tau p =
      nativeWorldObservationLaw n tau (behaviorToCausalWorld p) := by
  change causalBehaviorPlanLaw n tau p =
    nativeObservationLaw n tau ⟨p.toResponse, p.toResponse_valid⟩
  funext w
  rw [causalBehaviorPlanLaw_apply]
  unfold nativeObservationLaw
  rw [causalPlanObservationExperiment_eq_responseProb,
    CausalBehavior.responseProb_toResponse]

/-- The finite-depth native pseudometric written without raw response
representatives. -/
noncomputable def causalBehaviorDepthDist (n : ℕ)
    (p q : CausalBehavior A O) : ℝ :=
  (Finset.univ : Finset (CausalPlan A O n)).sup' Finset.univ_nonempty
    (fun tau => finiteTV (causalBehaviorPlanLaw n tau p)
      (causalBehaviorPlanLaw n tau q))

/-- The direct finite-depth formula is the pullback of the quotient formula. -/
theorem causalBehaviorDepthDist_eq_nativeWorldDepthDist
    (n : ℕ) (p q : CausalBehavior A O) :
    causalBehaviorDepthDist n p q =
      nativeWorldDepthDist n (behaviorToCausalWorld p)
        (behaviorToCausalWorld q) := by
  unfold causalBehaviorDepthDist nativeWorldDepthDist
  simp_rw [← causalBehaviorPlanLaw_eq_nativeWorldObservationLaw]

/-- Each direct native plan law is continuous in behavior coordinates. -/
theorem continuous_causalBehaviorPlanLaw (n : ℕ) (tau : CausalPlan A O n) :
    Continuous (causalBehaviorPlanLaw n tau) := by
  apply continuous_pi
  intro w
  change Continuous (fun p : CausalBehavior A O =>
    p.mass (List.ofFn (causalTraceOfObservations tau w)))
  exact (continuous_apply _).comp causalBehavior_mass_isEmbedding.continuous

/-- Each direct finite-depth native pseudometric is jointly continuous. -/
theorem continuous_causalBehaviorDepthDist (n : ℕ) :
    Continuous (fun z : CausalBehavior A O × CausalBehavior A O =>
      causalBehaviorDepthDist n z.1 z.2) := by
  unfold causalBehaviorDepthDist
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro tau _
  exact continuous_finiteTV.comp
    (((continuous_causalBehaviorPlanLaw n tau).comp continuous_fst).prodMk
      ((continuous_causalBehaviorPlanLaw n tau).comp continuous_snd))

@[simp]
theorem causalBehaviorDepthDist_self (n : ℕ) (p : CausalBehavior A O) :
    causalBehaviorDepthDist n p p = 0 := by
  rw [causalBehaviorDepthDist_eq_nativeWorldDepthDist]
  exact nativeWorldDepthDist_self n _

theorem causalBehaviorDepthDist_comm (n : ℕ)
    (p q : CausalBehavior A O) :
    causalBehaviorDepthDist n p q = causalBehaviorDepthDist n q p := by
  simp only [causalBehaviorDepthDist_eq_nativeWorldDepthDist]
  exact nativeWorldDepthDist_comm n _ _

theorem causalBehaviorDepthDist_triangle (n : ℕ)
    (p q r : CausalBehavior A O) :
    causalBehaviorDepthDist n p r ≤
      causalBehaviorDepthDist n p q + causalBehaviorDepthDist n q r := by
  simp only [causalBehaviorDepthDist_eq_nativeWorldDepthDist]
  exact nativeWorldDepthDist_triangle n _ _ _

/-- The weighted direct native distance from the note. -/
noncomputable def causalBehaviorNativeDist
    (p q : CausalBehavior A O) : ℝ :=
  ∑' n, nativeWeight n * causalBehaviorDepthDist (n + 1) p q

/-- The weighted direct formula is exactly the installed quotient distance. -/
theorem causalBehaviorNativeDist_eq_causalWorld_dist
    (p q : CausalBehavior A O) :
    causalBehaviorNativeDist p q =
      dist (behaviorToCausalWorld p) (behaviorToCausalWorld q) := by
  rw [causalWorld_dist_eq_tsum_nativeWorldDepthDist]
  unfold causalBehaviorNativeDist
  congr 1
  funext n
  rw [causalBehaviorDepthDist_eq_nativeWorldDepthDist]

/-- The direct weighted formula separates behaviors. -/
theorem causalBehaviorNativeDist_eq_zero_iff
    (p q : CausalBehavior A O) :
    causalBehaviorNativeDist p q = 0 ↔ p = q := by
  rw [causalBehaviorNativeDist_eq_causalWorld_dist, dist_eq_zero]
  constructor
  · intro hpq
    have h := congrArg causalWorldToBehavior hpq
    simpa using h
  · rintro rfl
    rfl

/-- A named metric structure whose distance is the direct native formula and
whose topology is the already installed behavior-coordinate topology.  It is
kept named rather than installed as a second global metric instance. -/
@[instance_reducible]
noncomputable def causalBehaviorNativeMetric :
    MetricSpace (CausalBehavior A O) :=
  (causalWorldHomeomorphBehavior (A := A) (O := O)).symm.isEmbedding.comapMetricSpace
    (behaviorToCausalWorld : CausalBehavior A O → CausalWorld A O)

theorem causalBehaviorNativeMetric_dist (p q : CausalBehavior A O) :
    (causalBehaviorNativeMetric (A := A) (O := O)).dist p q =
      causalBehaviorNativeDist p q := by
  change dist (behaviorToCausalWorld p) (behaviorToCausalWorld q) = _
  exact (causalBehaviorNativeDist_eq_causalWorld_dist p q).symm

/-- The named native metric induces exactly the direct coordinate topology. -/
theorem causalBehaviorNativeMetric_topology :
    (causalBehaviorNativeMetric (A := A) (O := O)).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (CausalBehavior A O)) := by
  rfl

end IdExp
